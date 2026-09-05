use proptest::prelude::*;
use proptest::test_runner::FileFailurePersistence;
use sumi_frontend::{
    Applicability, DiagnosticCode, FileId, ParsedSource, Place, Severity, codes, parse_source,
};
use sumi_syntax::{RawIdx, SyntaxKind};

/// The file every test source stands for; the frontend copies it into every
/// label rather than deriving it from anything.
const FILE: FileId = FileId::new(3);

fn parsed(source: &str) -> ParsedSource {
    parse_source(FILE, source.into()).expect("test sources fit in u32")
}

fn diagnostic_codes(front: &ParsedSource) -> Vec<DiagnosticCode> {
    front
        .diagnostics()
        .iter()
        .map(|diagnostic| diagnostic.code)
        .collect()
}

/// Apply the diagnostic's fix as a tool would, unread: the frontend's fixes
/// are all mechanical, so it must call every one of them safe.
fn apply_fix(source: &str, diagnostic: &sumi_frontend::Diagnostic) -> String {
    let fix = diagnostic.fix.as_ref().expect("diagnostic has a fix");
    assert_eq!(fix.applicability, Applicability::Safe);
    let mut result = source.to_owned();
    for edit in fix.edits.iter().rev() {
        let range = edit.range();
        result.replace_range(
            range.start().to_usize()..range.end().to_usize(),
            edit.replacement(),
        );
    }
    result
}

// A closer repair must add exactly its named code token, not alter literal
// text or comments. Same-kind nested repairs may still be offered inside-out;
// neither a same-site reoffer nor a global error count is a repair oracle.
fn check_closer_fixes(front: &ParsedSource) {
    let preserved = |front: &ParsedSource| {
        front
            .lexed()
            .indices()
            .filter(|&raw| {
                !front.lexed().kind(raw).is_trivia()
                    || front.lexed().kind(raw) == SyntaxKind::LineComment
            })
            .map(|raw| {
                (
                    front.lexed().kind(raw),
                    front.lexed().text(front.source(), raw).to_owned(),
                )
            })
            .collect::<Vec<_>>()
    };
    for diagnostic in front.diagnostics() {
        if diagnostic.code != codes::EXPECTED_TOKEN || diagnostic.fix.is_none() {
            continue;
        }
        let fix = diagnostic.fix.as_ref().unwrap();
        assert_eq!(fix.edits.len(), 1);
        let edit = &fix.edits[0];
        assert_eq!(edit.range().start(), edit.range().end());
        let kind = match edit.replacement() {
            ")" => SyntaxKind::RParen,
            "}" => SyntaxKind::RBrace,
            other => panic!("unexpected closer {other:?}"),
        };
        let after = parsed(&apply_fix(front.source(), diagnostic));
        let raw = after
            .lexed()
            .token_at(edit.range().start())
            .expect("inserted token");
        assert_eq!(after.lexed().range(raw).start(), edit.range().start());
        assert_eq!(after.lexed().kind(raw), kind, "{:?}", front.source());
        assert_eq!(after.lexed().text(after.source(), raw), edit.replacement());
        let rank = after
            .lexed()
            .indices()
            .take_while(|&token| token < raw)
            .filter(|&token| {
                !after.lexed().kind(token).is_trivia()
                    || after.lexed().kind(token) == SyntaxKind::LineComment
            })
            .count();
        let mut tokens = preserved(&after);
        tokens.remove(rank);
        assert_eq!(tokens, preserved(front), "{:?}", front.source());
    }
}

#[test]
fn nested_closer_repairs_remain_available_inside_out() {
    let mut source = "fn f() = ((x".to_owned();
    for _ in 0..2 {
        let front = parsed(&source);
        check_closer_fixes(&front);
        let fixes: Vec<_> = front
            .diagnostics()
            .iter()
            .filter(|d| d.fix.is_some())
            .collect();
        assert_eq!(fixes.len(), 1);
        source = apply_fix(&source, fixes[0]);
    }
    assert!(parsed(&source).diagnostics().is_empty());
}

#[test]
fn parentheses_can_still_be_repaired_in_hole_code() {
    let source = "fn f() = \"{g(x}\"";
    let front = parsed(source);
    check_closer_fixes(&front);
    let diagnostic = front
        .diagnostics()
        .iter()
        .find(|d| d.fix.is_some())
        .unwrap();
    let fixed = apply_fix(source, diagnostic);
    assert_eq!(fixed, "fn f() = \"{g(x)}\"");
    assert!(parsed(&fixed).diagnostics().is_empty());
}

#[test]
fn parsed_source_owns_every_syntactic_product() {
    let source = String::from("fn f() {}\n").into_boxed_str();
    let front = parse_source(FILE, source).expect("test source fits in u32");

    assert_eq!(front.file(), FILE);
    assert_eq!(front.source(), "fn f() {}\n");
    assert_eq!(front.lexed().source_len().to_usize(), front.source().len());
    let tree = front.parse().tree();
    assert_eq!(tree.first_token(tree.root()), RawIdx::new(0));
    assert_eq!(tree.end_token(tree.root()), front.lexed().end());
    assert!(front.diagnostics().is_empty());

    assert!(parsed("").diagnostics().is_empty());
}

#[test]
fn frontend_diagnostic_identity_is_syntactic_not_phase_specific() {
    for code in [
        codes::UNKNOWN_CHARACTER,
        codes::NONCANONICAL_NUMBER,
        codes::EXPECTED_TOKEN,
    ] {
        assert_eq!(code.group(), codes::SYNTAX);
    }
}

#[test]
fn empty_producer_ranges_do_not_become_missing_syntax() {
    let front = parsed("fn f() { '' }");
    let [diagnostic] = front.diagnostics() else {
        panic!("an empty character literal has one diagnostic")
    };
    assert_eq!(diagnostic.code, codes::EMPTY_CHAR_LITERAL);
    let Place::Range(range) = diagnostic.primary.location.place else {
        panic!("empty literal content is still a producer range")
    };
    assert_eq!(range.start(), range.end());
    assert_eq!(range.start().to_usize(), 10);
}

#[test]
fn diagnostics_are_globally_sorted_with_stable_ties() {
    // The lexer observes the later `€` before parser diagnostics are lowered,
    // so source sorting must move the missing `:` ahead of it.
    let front = parsed("fn f(a) { € }");
    assert_eq!(
        diagnostic_codes(&front),
        [codes::EXPECTED_TOKEN, codes::UNKNOWN_CHARACTER]
    );
    assert_eq!(front.diagnostics()[0].message.as_ref(), "expected `:`");

    // Both facts sit at EOF; stable sorting retains parser observation order.
    let front = parsed("fn f(a: int");
    assert_eq!(front.diagnostics().len(), 2);
    assert_eq!(front.diagnostics()[0].message.as_ref(), "expected `)`");
    assert_eq!(
        front.diagnostics()[1].message.as_ref(),
        "expected a body, `{` or `=`"
    );
    assert_eq!(
        front.diagnostics()[0].primary.location,
        front.diagnostics()[1].primary.location
    );
    assert_eq!(
        apply_fix("fn f(a: int", &front.diagnostics()[0]),
        "fn f(a: int)"
    );
    assert!(front.diagnostics()[1].fix.is_none());
}

#[test]
fn independent_same_token_facts_remain_independent() {
    let front = parsed(r#"fn f() { "\q\q" }"#);
    assert_eq!(
        diagnostic_codes(&front),
        [codes::UNKNOWN_ESCAPE, codes::UNKNOWN_ESCAPE]
    );
    assert_ne!(
        front.diagnostics()[0].primary.location,
        front.diagnostics()[1].primary.location
    );
}

/// Source fragments beyond every keyword and punctuation text of the
/// language: names, malformed literals, roleless punctuation, and trivia.
const EXTRA_FRAGMENTS: &[&str] = &[
    "x",
    "Δ",
    "0",
    "01_",
    "1E+05",
    "1e",
    r#""\q""#,
    "'ab'",
    ";",
    " ",
    "\n",
    "// c",
    "€",
    "\"{",
    "}\"",
    "\"{x}\"",
    "\"\"\"\n{",
];

fn source() -> impl Strategy<Value = String> {
    let fragments: Vec<&'static str> = SyntaxKind::ALL
        .iter()
        .filter_map(|kind| kind.text())
        .chain(EXTRA_FRAGMENTS.iter().copied())
        .collect();
    proptest::collection::vec(prop::sample::select(fragments), 0..64)
        .prop_map(|pieces| pieces.concat())
}

/// Records every failing seed in the crate's tracked `proptest-regressions/`
/// file, which each later run replays before generating anything new, so a
/// failure found once stays found. Proptest's default location is found by
/// walking up from the test file to a `lib.rs`, which a test under `tests/`
/// never reaches; this path is fixed at compile time instead.
fn config() -> ProptestConfig {
    ProptestConfig {
        failure_persistence: Some(Box::new(FileFailurePersistence::Direct(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/proptest-regressions/frontend.txt"
        )))),
        ..ProptestConfig::default()
    }
}

proptest! {
    #![proptest_config(config())]
    #[test]
    fn closer_fixes_preserve_existing_tokens(source in source()) {
        check_closer_fixes(&parsed(&source));
    }

    #[test]
    fn closer_fixes_at_interpolation_boundaries(
        text in "[a-z ]{0,16}",
        hole in prop::sample::select(vec!["", "x", "(x", "((x", "{ x", "g(x"]),
        block in any::<bool>(),
        terminated in any::<bool>(),
        signature in prop::sample::select(vec!["fn f(", "fn f()"]),
    ) {
        let quote = if block { "\"\"\"\n" } else { "\"" };
        let end = if !terminated { "" } else if block { "\n\"\"\"" } else { "\"" };
        let source = format!("{signature} -> str = {quote}before {{{hole}}}{text}{end}");
        check_closer_fixes(&parsed(&source));
    }

    #[test]
    fn every_canonical_location_is_valid(source in source()) {
        let front = parse_source(FILE, source.into_boxed_str()).expect("generated sources fit in u32");
        let source = front.source();
        let mut previous = None;
        for diagnostic in front.diagnostics() {
            prop_assert_eq!(diagnostic.severity, Severity::Error);
            let key = (
                diagnostic.primary.location.start().to_u32(),
                diagnostic.primary.location.end().to_u32(),
            );
            if let Some(previous) = previous {
                prop_assert!(previous <= key, "diagnostics are not source sorted");
            }
            previous = Some(key);

            for label in std::iter::once(&diagnostic.primary).chain(&*diagnostic.secondary) {
                prop_assert_eq!(label.location.file, FILE);
                let start = label.location.start().to_usize();
                let end = label.location.end().to_usize();
                prop_assert!(start <= end && end <= source.len());
                prop_assert!(source.is_char_boundary(start));
                prop_assert!(source.is_char_boundary(end));
                if let Place::Point(point) = label.location.place {
                    prop_assert_eq!(point.to_usize(), start);
                    prop_assert_eq!(start, end);
                }
            }
            if let Some(fix) = &diagnostic.fix {
                prop_assert_eq!(fix.applicability, Applicability::Safe);
                prop_assert!(!fix.edits.is_empty());
                let mut previous_end = None;
                for edit in &fix.edits {
                    let range = edit.range();
                    let start = range.start().to_usize();
                    let end = range.end().to_usize();
                    prop_assert!(start <= end && end <= source.len());
                    prop_assert!(source.is_char_boundary(start));
                    prop_assert!(source.is_char_boundary(end));
                    if let Some(previous_end) = previous_end {
                        prop_assert!(previous_end <= start);
                    }
                    previous_end = Some(end);
                }
            }
        }
    }
}
