use proptest::prelude::*;
use sumi_frontend::{
    Applicability, DiagnosticCode, FileId, Location, ParsedSource, Place, Severity, codes,
    parse_source,
};
use sumi_syntax::{NodeKind, ParseAnchor, ParseEvidence, RawIdx, SyntaxKind};
use sumi_text::TextSize;

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

fn location_text(front: &ParsedSource, location: Location) -> &str {
    assert_eq!(location.file, front.file());
    match location.place {
        Place::Range(range) => range.text(front.source()),
        Place::Point(point) => &front.source()[point.to_usize()..point.to_usize()],
    }
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

fn same_tree_shape(left: &ParsedSource, right: &ParsedSource) -> bool {
    let left = left.parse().tree();
    let right = right.parse().tree();
    left.len() == right.len()
        && left.nodes().all(|node| left.kind(node) == right.kind(node))
        && left.parents() == right.parents()
}

fn raw_boundary(front: &ParsedSource, raw: RawIdx) -> TextSize {
    sumi_syntax::raw_boundary(front.lexed(), raw)
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
fn missing_syntax_points_at_the_parser_cursor() {
    let source = "// doc\nf() {}";
    let front = parsed(source);
    let [diagnostic] = front.diagnostics() else {
        panic!("the signature is only missing `fn`")
    };
    assert_eq!(diagnostic.code, codes::EXPECTED_TOKEN);
    assert_eq!(diagnostic.message.as_ref(), "expected `fn`");
    assert_eq!(
        diagnostic.primary.location,
        Location::point(FILE, TextSize::new(source.find('f').unwrap() as u32))
    );
    assert!(diagnostic.fix.is_none());

    let source = "fn f() { x // tail";
    let front = parsed(source);
    let [diagnostic] = front.diagnostics() else {
        panic!("the block is only missing a closing brace")
    };
    assert_eq!(diagnostic.code, codes::EXPECTED_TOKEN);
    assert_eq!(diagnostic.message.as_ref(), "expected `}`");
    assert_eq!(
        diagnostic.primary.location,
        Location::point(FILE, TextSize::new(source.len() as u32))
    );
    let [opener] = &*diagnostic.secondary else {
        panic!("the missing closer must retain its opener")
    };
    assert_eq!(location_text(&front, opener.location), "{");
    assert_eq!(opener.message.as_deref(), Some("opening delimiter is here"));
    let fix = diagnostic
        .fix
        .as_ref()
        .expect("the missing closer has a fix");
    assert_eq!(fix.message.as_ref(), "insert `}`");
    let [edit] = &*fix.edits else {
        panic!("inserting a closer is one edit")
    };
    let insertion = TextSize::new(source.find(" // tail").unwrap() as u32);
    assert_eq!(
        edit.range(),
        sumi_text::TextRange::new(insertion, insertion)
    );
    assert_eq!(edit.replacement(), "}");
    let fixed = apply_fix(source, diagnostic);
    assert_eq!(fixed, "fn f() { x} // tail");
    assert!(parsed(&fixed).diagnostics().is_empty());

    let [ParseEvidence::Recovery(recovery)] = front.parse().evidence() else {
        panic!("the parse retains the missing closer evidence")
    };
    let ParseAnchor::Gap(gap) = recovery.anchor else {
        panic!("the closer is absent from a raw gap")
    };
    let start = raw_boundary(&front, gap.trivia_start()).to_usize();
    let end = raw_boundary(&front, gap.trivia_end()).to_usize();
    assert_eq!(&source[start..end], " // tail");
}

#[test]
fn raw_ranges_map_across_multibyte_source_and_parser_cascades_are_suppressed() {
    let front = parsed("fn f() { a € + b }");
    let [diagnostic] = front.diagnostics() else {
        panic!("the lexer owns the unknown character")
    };
    assert_eq!(diagnostic.code, codes::UNKNOWN_CHARACTER);
    assert_eq!(location_text(&front, diagnostic.primary.location), "€");
    assert!(matches!(
        front.parse().evidence(),
        [ParseEvidence::Recovery(_)]
    ));

    let front = parsed("fn f() {\n  a ;\n  b\n}");
    assert_eq!(diagnostic_codes(&front), [codes::UNKNOWN_PUNCTUATION]);
    assert_eq!(front.parse().evidence().len(), 2);
}

#[test]
fn an_error_in_a_skipped_effect_does_not_suppress_a_valid_cause() {
    let front = parsed(": €");
    assert_eq!(
        diagnostic_codes(&front),
        [codes::EXPECTED_ITEM, codes::UNKNOWN_CHARACTER]
    );
    let parser = &front.diagnostics()[0];
    assert_eq!(location_text(&front, parser.primary.location), ":");
    let [skipped] = &*parser.secondary else {
        panic!("the parser diagnostic retains its skipped effect")
    };
    assert_eq!(location_text(&front, skipped.location), ": €");
}

#[test]
fn closers_after_unterminated_literals_have_no_fix() {
    for literal in ["\"tail", "r\"tail", "'tail", "\"\"\"tail", "r\"\"\"tail"] {
        let source = format!("fn f() {{ ({literal}");
        let front = parsed(&source);
        let closers: Vec<_> = front
            .diagnostics()
            .iter()
            .filter(|diagnostic| {
                matches!(diagnostic.message.as_ref(), "expected `)`" | "expected `}`")
            })
            .collect();

        assert!(
            closers
                .iter()
                .any(|diagnostic| diagnostic.message.as_ref() == "expected `)`"),
            "nested paren closer is reported for {source:?}"
        );
        assert!(
            closers
                .iter()
                .any(|diagnostic| diagnostic.message.as_ref() == "expected `}`"),
            "block closer is reported for {source:?}"
        );
        assert!(
            closers.iter().all(|diagnostic| diagnostic.fix.is_none()),
            "a closer cannot be inserted after the unterminated literal in {source:?}"
        );
    }
}

#[test]
fn nested_same_kind_closers_are_fixed_inside_out() {
    for (source, message, after_first) in [
        ("fn f() { if true {", "expected `}`", "fn f() { if true {}"),
        ("fn f() { ((1 }", "expected `)`", "fn f() { ((1) }"),
    ] {
        let front = parsed(source);
        let closers: Vec<_> = front
            .diagnostics()
            .iter()
            .filter(|diagnostic| diagnostic.message.as_ref() == message)
            .collect();
        assert_eq!(closers.len(), 2, "two nested closers for {source:?}");
        assert!(closers[0].fix.is_some(), "innermost closer is fixable");
        assert!(closers[1].fix.is_none(), "outer closer waits for reparse");

        let fixed = apply_fix(source, closers[0]);
        assert_eq!(fixed, after_first);
        let reparsed = parsed(&fixed);
        let remaining: Vec<_> = reparsed
            .diagnostics()
            .iter()
            .filter(|diagnostic| diagnostic.message.as_ref() == message)
            .collect();
        assert_eq!(remaining.len(), 1, "only the outer closer remains");
        assert!(remaining[0].fix.is_some(), "outer closer is now fixable");
    }
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
    assert_eq!(front.diagnostics()[1].message.as_ref(), "expected `{`");
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
fn numeric_canonicalization_facts_form_one_diagnostic() {
    let front = parsed("fn f() { 1E+05 }");
    let [diagnostic] = front.diagnostics() else {
        panic!("one literal has one canonicalization diagnostic")
    };
    assert_eq!(diagnostic.code, codes::NONCANONICAL_NUMBER);
    assert_eq!(location_text(&front, diagnostic.primary.location), "E");
    assert_eq!(
        diagnostic.primary.message.as_deref(),
        Some("exponent marker must be lowercase `e`")
    );
    assert_eq!(diagnostic.secondary.len(), 2);
    assert_eq!(location_text(&front, diagnostic.secondary[0].location), "+");
    assert_eq!(location_text(&front, diagnostic.secondary[1].location), "0");
    assert_eq!(
        diagnostic.fix.as_ref().unwrap().message.as_ref(),
        "canonicalize numeric literal"
    );
    assert_eq!(apply_fix("fn f() { 1E+05 }", diagnostic), "fn f() { 1e5 }");

    let front = parsed("fn f() { 01_ }");
    let [diagnostic] = front.diagnostics() else {
        panic!("both spelling facts form one diagnostic")
    };
    assert_eq!(diagnostic.code, codes::NONCANONICAL_NUMBER);
    assert_eq!(diagnostic.secondary.len(), 1);

    let front = parsed("fn f() { 01u32 }");
    assert_eq!(
        diagnostic_codes(&front),
        [codes::NONCANONICAL_NUMBER, codes::UNKNOWN_SUFFIX]
    );
    let fixed = apply_fix("fn f() { 01u32 }", &front.diagnostics()[0]);
    assert_eq!(fixed, "fn f() { 1u32 }");
    assert_eq!(diagnostic_codes(&parsed(&fixed)), [codes::UNKNOWN_SUFFIX]);

    let front = parsed("fn f() { 01E }");
    assert_eq!(
        diagnostic_codes(&front),
        [codes::NONCANONICAL_NUMBER, codes::MISSING_EXPONENT]
    );
    let fixed = apply_fix("fn f() { 01E }", &front.diagnostics()[0]);
    assert_eq!(fixed, "fn f() { 1E }");
    assert_eq!(diagnostic_codes(&parsed(&fixed)), [codes::MISSING_EXPONENT]);

    let front = parsed("fn f() { 1_e }");
    assert_eq!(
        diagnostic_codes(&front),
        [codes::NONCANONICAL_NUMBER, codes::MISSING_EXPONENT]
    );
}

#[test]
fn parser_layout_violations_offer_safe_fixes() {
    for (source, code, expected) in [
        ("fn f()\n{ 1 }", codes::BLOCK_ON_NEW_LINE, "fn f() {\n 1 }"),
        (
            "fn f() { a==b }",
            codes::UNSPACED_BINARY_OPERATOR,
            "fn f() { a == b }",
        ),
        (
            "fn f() { a +\n b }",
            codes::TRAILING_OPERATOR,
            "fn f() { a \n + b }",
        ),
        (
            "fn f() { - \t1 }",
            codes::SPACED_PREFIX_OPERATOR,
            "fn f() { -1 }",
        ),
    ] {
        let front = parsed(source);
        let diagnostic = front
            .diagnostics()
            .iter()
            .find(|diagnostic| diagnostic.code == code)
            .expect("layout diagnostic exists");
        let fixed = apply_fix(source, diagnostic);
        assert_eq!(fixed, expected);
        assert!(same_tree_shape(&front, &parsed(&fixed)));
    }
}

#[test]
fn layout_movement_fixes_yield_to_recovery() {
    for (source, code) in [
        ("fn f()\n{ : }", codes::BLOCK_ON_NEW_LINE),
        ("fn f() { a +\n b : }", codes::TRAILING_OPERATOR),
        ("fn f()\n{ € }", codes::BLOCK_ON_NEW_LINE),
    ] {
        let front = parsed(source);
        let diagnostic = front
            .diagnostics()
            .iter()
            .find(|diagnostic| diagnostic.code == code)
            .expect("layout diagnostic exists");
        assert!(diagnostic.fix.is_none(), "movement fix for {source:?}");
    }

    let front = parsed("fn f() { a+b : }");
    let spacing = front
        .diagnostics()
        .iter()
        .find(|diagnostic| diagnostic.code == codes::UNSPACED_BINARY_OPERATOR)
        .expect("spacing diagnostic exists");
    assert!(
        spacing.fix.is_some(),
        "spacing remains safe around recovery"
    );
}

#[test]
fn nonmechanical_layout_violations_have_no_fix() {
    for (source, code) in [
        ("fn f() { - // why\n 1 }", codes::SPACED_PREFIX_OPERATOR),
        ("fn f() { - \r1 }", codes::SPACED_PREFIX_OPERATOR),
        ("fn f() { a < b < c }", codes::CHAINED_COMPARISON),
    ] {
        let front = parsed(source);
        let diagnostic = front
            .diagnostics()
            .iter()
            .find(|diagnostic| diagnostic.code == code)
            .expect("layout diagnostic exists");
        assert!(diagnostic.fix.is_none(), "no fix for {source:?}");
    }
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
    "x", "Δ", "0", "01_", "1E+05", "1e", r#""\q""#, "'ab'", ";", " ", "\n", "// c", "€",
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

proptest! {
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

#[test]
fn line_literals_end_at_their_line() {
    // A stray quote costs its line and nothing after it: the next line
    // still parses as the call it is.
    let source = "fn f() {\n    let s = \"a\n    g(s)\n}\n";
    let front = parsed(source);
    assert_eq!(diagnostic_codes(&front), vec![codes::UNTERMINATED_STRING]);
    assert_eq!(
        location_text(&front, front.diagnostics()[0].primary.location),
        "\"a"
    );
    let tree = front.parse().tree();
    let item = tree.children(tree.root()).next().expect("one item");
    let block = tree
        .children(item)
        .find(|&node| tree.kind(node) == NodeKind::Block)
        .expect("the item has a body");
    let statements: Vec<NodeKind> = tree.children(block).map(|node| tree.kind(node)).collect();
    assert_eq!(statements, vec![NodeKind::CallExpr, NodeKind::LetStmt]);
}

#[test]
fn block_strings_are_one_token_and_report_their_layout() {
    let clean = "fn f() {\n    let s = \"\"\"\n        a\n        \"\"\"\n    g(s)\n}\n";
    assert!(parsed(clean).diagnostics().is_empty());

    let source = "fn f() {\n    let s = \"\"\"tail\n        a\n  b\n    \"\"\"\n}\n";
    let front = parsed(source);
    assert_eq!(
        diagnostic_codes(&front),
        vec![
            codes::BLOCK_STRING_OPENER_CONTENT,
            codes::BLOCK_STRING_INDENTATION
        ]
    );
    let texts: Vec<&str> = front
        .diagnostics()
        .iter()
        .map(|diagnostic| location_text(&front, diagnostic.primary.location))
        .collect();
    assert_eq!(texts, vec!["tail", "  "]);

    let source = "fn f() {\n    let s = \"\"\"\n        a\"\"\"\n}\n";
    let front = parsed(source);
    assert_eq!(
        diagnostic_codes(&front),
        vec![codes::BLOCK_STRING_CLOSER_CONTENT]
    );
    assert_eq!(
        location_text(&front, front.diagnostics()[0].primary.location),
        "\"\"\""
    );
}

#[test]
fn unterminated_block_strings_are_reported_at_their_opener() {
    for (opener, code) in [
        ("\"\"\"", codes::UNTERMINATED_BLOCK_STRING),
        ("r\"\"\"", codes::UNTERMINATED_RAW_BLOCK_STRING),
    ] {
        let source = format!("fn f() {{\n    let s = {opener}\n        a\n}}\n");
        let front = parsed(&source);
        let first = &front.diagnostics()[0];
        assert_eq!(first.code, code, "for {source:?}");
        assert_eq!(location_text(&front, first.primary.location), opener);
    }
}
