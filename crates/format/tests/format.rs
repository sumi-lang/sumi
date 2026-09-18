use sumi_format::layout_violation_edits;
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
