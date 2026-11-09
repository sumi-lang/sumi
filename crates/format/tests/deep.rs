//! Chains the parser builds around their left operand, which no nesting limit bounds.

use sumi_test::check;

const LINKS: usize = 100_000;

#[track_caller]
fn formats(source: String, expected: String) {
    let formatted = check::format(&source);
    assert_eq!(formatted.reverted, 0);
    let same = formatted
        .text
        .lines()
        .zip(expected.lines())
        .take_while(|(line, expected)| line == expected)
        .count();
    assert!(
        formatted.text == expected,
        "line {} is laid out otherwise, of {} where {} are expected",
        same + 1,
        formatted.text.lines().count(),
        expected.lines().count(),
    );
}

#[test]
fn a_long_operator_chain_breaks_before_every_operator() {
    formats(
        format!("fn main() -> int = 1{}\n", " + 1".repeat(LINKS)),
        format!("fn main() -> int = 1\n{}", "    + 1\n".repeat(LINKS)),
    );
}

#[test]
fn a_long_field_chain_stays_whole() {
    formats(
        format!("fn f() -> int = a{}\n", ".b".repeat(LINKS)),
        format!("fn f() -> int =\n    a{}\n", ".b".repeat(LINKS)),
    );
}

#[test]
fn a_long_union_stays_whole() {
    formats(
        format!("fn f() -> A{} = 1\n", " | A".repeat(LINKS)),
        format!("fn f() -> A{} =\n    1\n", " | A".repeat(LINKS)),
    );
}
