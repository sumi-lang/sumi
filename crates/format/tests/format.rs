use sumi_format::{layout_violation_edits, reprint};
use sumi_syntax::{ParseEvidence, ParseViolationKind};
use sumi_test::front;

fn apply_edits(source: &str, edits: &[sumi_text::TextEdit]) -> String {
    let mut result = source.to_owned();
    for edit in edits.iter().rev() {
        let range = edit.range();
        result.replace_range(
            range.start().to_usize()..range.end().to_usize(),
            edit.replacement(),
        );
    }
    result
}

#[track_caller]
fn check_layout_edits(source: &str, kind: ParseViolationKind, expected: Option<&str>) {
    let front = front(source);
    let violation = front
        .parse
        .evidence()
        .iter()
        .find_map(|evidence| match evidence {
            ParseEvidence::Violation(violation) if violation.kind == kind => Some(*violation),
            _ => None,
        })
        .expect("source has the requested violation");
    let edits = layout_violation_edits(&front.lexed, violation);
    assert_eq!(
        edits.as_deref().map(|edits| apply_edits(source, edits)),
        expected.map(str::to_owned),
        "layout edits for {source:?}"
    );
    if let Some(edits) = edits {
        assert!(!edits.is_empty());
        assert!(
            edits
                .windows(2)
                .all(|pair| { pair[0].range().end() <= pair[1].range().start() })
        );
    }
}

/// Assert that reprinting `source` gives it back byte for byte.
#[track_caller]
fn check_roundtrip(source: &str) {
    let front = front(source);
    assert_eq!(
        reprint(front.parse.tree(), &front.lexed, source),
        source,
        "reprint of {source:?}"
    );
}

#[test]
fn reprint_is_the_identity_on_malformed_sources() {
    for source in [
        "",
        " \t\n",
        "fn f( { ) }",
        "fn f() { a==b }\n\u{20ac} ; [",
        "\"open string",
        "fn f() { 'ab' '' }",
        "0123 1e+05 1u32",
        "r##\"unterminated",
        "let x = 1\nfn g(,,) -> {",
        "fn f() {\r\n return 1 \r}",
        "fn f() { ((((( }",
        ": (x)",
        "// only a comment",
        "fn 0() fn",
    ] {
        check_roundtrip(source);
    }
}

#[test]
fn reprint_survives_the_nesting_recovery_limit() {
    let source = format!("fn f() {{ {}x }}", "(".repeat(400));
    check_roundtrip(&source);
}

#[test]
fn reprint_survives_long_expression_chains() {
    let binary = format!("fn f() {{ x{} }}", " + x".repeat(20_000));
    check_roundtrip(&binary);

    let calls = format!("fn f() {{ f{} }}", "()".repeat(20_000));
    check_roundtrip(&calls);
}

#[test]
fn layout_violation_edits_are_atomic_and_source_ordered() {
    check_layout_edits(
        "fn f() { a==b }",
        ParseViolationKind::UnspacedBinaryOperator,
        Some("fn f() { a == b }"),
    );
    check_layout_edits(
        "fn f() { - \t1 }",
        ParseViolationKind::SpacedPrefixOperator,
        Some("fn f() { -1 }"),
    );
    check_layout_edits(
        "fn\n  f() {}",
        ParseViolationKind::FunctionNameOnNextLine,
        Some("fn f() {}"),
    );
    check_layout_edits(
        "fn a() {}fn b() {}",
        ParseViolationKind::FunctionItemOnSameLine,
        Some("fn a() {}\nfn b() {}"),
    );
    check_layout_edits(
        "fn f() { let\nmut\nx = 1 }",
        ParseViolationKind::BindingNameOnNextLine,
        Some("fn f() { let mut x = 1 }"),
    );
}

#[test]
fn layout_violation_edits_reject_nonmechanical_candidates() {
    check_layout_edits(
        "fn f() { - // why\n 1 }",
        ParseViolationKind::SpacedPrefixOperator,
        None,
    );
    check_layout_edits(
        "fn f() { - \r1 }",
        ParseViolationKind::SpacedPrefixOperator,
        None,
    );
    check_layout_edits(
        "fn f() { a < b < c }",
        ParseViolationKind::ChainedComparison,
        None,
    );
    check_layout_edits(
        "fn // why\nf() {}",
        ParseViolationKind::FunctionNameOnNextLine,
        None,
    );
    check_layout_edits(
        "fn f() { let // why\nx = 1 }",
        ParseViolationKind::BindingNameOnNextLine,
        None,
    );
}
