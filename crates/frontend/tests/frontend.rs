//! Diagnostics a snapshot cannot express: their order, their fixes, and
//! their independence, over hand-written and generated sources.

use proptest::prelude::*;
use sumi_frontend::{DiagnosticCode, ParsedSource, codes, parse_source};
use sumi_syntax::SyntaxKind;
use sumi_test::check;

fn parsed(source: &str) -> ParsedSource {
    parse_source(source.into()).expect("test sources fit in u32")
}

fn diagnostic_codes(front: &ParsedSource) -> Vec<DiagnosticCode> {
    front
        .diagnostics()
        .iter()
        .map(|diagnostic| diagnostic.code)
        .collect()
}

/// Apply the diagnostic's fix as a tool would, unread.
fn apply_fix(source: &str, diagnostic: &sumi_frontend::Diagnostic) -> String {
    let fix = diagnostic.fix.as_ref().expect("diagnostic has a fix");
    sumi_text::apply(source, [&fix.edit])
}

#[test]
fn nested_closer_repairs_remain_available_inside_out() {
    let mut source = "fn f() = ((x".to_owned();
    for _ in 0..2 {
        let front = parsed(&source);
        check::diagnostics(&front);
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
        front.diagnostics()[0].primary,
        front.diagnostics()[1].primary
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
        front.diagnostics()[0].primary,
        front.diagnostics()[1].primary
    );
}

#[test]
fn leading_zeros_are_fixed_around_a_suffix() {
    let source = "fn f() = 01u32";
    let front = parsed(source);
    assert_eq!(
        diagnostic_codes(&front),
        [codes::NONCANONICAL_NUMBER, codes::UNKNOWN_SUFFIX]
    );
    let diagnostic = &front.diagnostics()[0];
    assert_eq!(
        diagnostic.primary.start().to_usize()..diagnostic.primary.end().to_usize(),
        9..10
    );
    assert_eq!(apply_fix(source, diagnostic), "fn f() = 1u32");
    assert!(front.diagnostics()[1].fix.is_none());
}

/// Source fragments beyond every keyword and punctuation text of the
/// language: names, malformed literals, roleless punctuation, and trivia.
const EXTRA_FRAGMENTS: &[&str] = &[
    "x", "0", "01u32", "1e", r#""\q""#, "\"open", ";", " ", "\n", "// c", "€",
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
    #![proptest_config(sumi_test::regressions(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/proptest-regressions/frontend.txt"
    )))]
    #[test]
    fn every_diagnostic_is_canonical_and_its_fix_safe(source in source()) {
        check::diagnostics(&parsed(&source));
    }
}
