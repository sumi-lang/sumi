//! Chains the parser builds around their left operand, which no nesting limit bounds.

use sumi_test::check;

const LINKS: usize = 20_000;

#[track_caller]
fn formats(source: String, expected: String) {
    let formatted = check::format(&source);
    assert_eq!(formatted.reverted, 0);
    assert!(
        formatted.text == expected,
        "a chain of {LINKS} links is laid out otherwise"
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
        format!("fn f(a: int) -> int = a{}\n", ".b".repeat(LINKS)),
        format!(
            "fn f(\n    a: int,\n) -> int =\n    a{}\n",
            ".b".repeat(LINKS)
        ),
    );
}

#[test]
fn a_long_union_stays_whole() {
    formats(
        format!(
            "type A {{}}\nfn f(a: A{}) -> int = 1\n",
            " | A".repeat(LINKS)
        ),
        format!(
            "type A {{}}\nfn f(\n    a: A{},\n) -> int = 1\n",
            " | A".repeat(LINKS)
        ),
    );
}
