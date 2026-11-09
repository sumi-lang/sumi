use sumi_frontend::parse_source;
use sumi_hir::analyze;
use sumi_syntax::MAX_DEPTH;

fn analyzes(source: String) {
    let analysis = analyze(parse_source(source.into()).unwrap());
    assert!(!analysis.diagnostics().is_empty());
}

fn nested(open: &str, close: &str, innermost: &str) -> String {
    let depth = MAX_DEPTH as usize + 8;
    let mut source = String::from("fn main() -> int {\n");
    for _ in 0..depth {
        source.push_str(open);
    }
    source.push_str(innermost);
    for _ in 0..depth {
        source.push_str(close);
    }
    source.push_str("\n}\n");
    source
}

/// A chain the parser builds around its left operand, which no nesting limit bounds.
fn chained(prefix: &str, link: &str, count: usize, suffix: &str) -> String {
    let mut source = String::from(prefix);
    for _ in 0..count {
        source.push_str(link);
    }
    source.push_str(suffix);
    source
}

#[test]
fn deeply_nested_blocks_lower_without_overflowing() {
    analyzes(nested("{ ", " }", "1"));
}

#[test]
fn deeply_nested_branches_lower_without_overflowing() {
    analyzes(nested("if true { ", " } else { 0 }", "1"));
}

#[test]
fn deeply_nested_parentheses_and_calls_lower_without_overflowing() {
    analyzes(nested("(", ")", "1"));
    analyzes(nested("f(", ")", "1"));
}

#[test]
fn deeply_nested_operators_lower_without_overflowing() {
    analyzes(nested("-", "", "1"));
    analyzes(nested("1 + (", ")", "1"));
}

#[test]
fn deeply_nested_matches_and_loops_lower_without_overflowing() {
    analyzes(nested("match true { _ => ", " }", "1"));
    analyzes(nested("for i in 0..1 { ", " }", "1"));
}

#[test]
fn long_operator_chains_lower_without_overflowing() {
    analyzes(chained(
        "fn main() -> int { 1",
        " + 1",
        20_000,
        " + true }\n",
    ));
    analyzes(chained(
        "fn main() -> int { if true",
        " && true",
        4_000,
        " { 1 } else { true } }\n",
    ));
}

/// The graph nodes per lazy operator of a valid body that branches on `condition`.
fn nodes_per_operator(head: &str, condition: &str, operators: usize) -> usize {
    let source = format!("{head} if {condition} {{ 1 }} else {{ 2 }} }}\n");
    let analysis = analyze(parse_source(source.into()).unwrap());
    assert!(analysis.is_valid());
    analysis.graph().nodes().len() / operators
}

#[test]
fn a_long_lazy_chain_narrows_each_operand_once() {
    const OPERATORS: usize = 4_000;
    let chain = |operand: &str, link: &str| chained(operand, link, OPERATORS, "");
    for (head, condition) in [
        ("fn main(a: bool) -> int {", chain("a", " && a")),
        ("fn main(a: bool) -> int {", chain("a", " || a")),
        ("fn main(a: int) -> int {", chain("a > 0", " && a > 0")),
        (
            "fn main(p: bool) -> int { let mut a = p\n",
            chain("a", " && a"),
        ),
    ] {
        // Narrowing every operand before it under each operator takes half as many as there are.
        assert!(nodes_per_operator(head, &condition, OPERATORS) < 16);
    }
}

#[test]
fn parentheses_hand_a_lazy_chain_on() {
    const LEVELS: usize = 60;
    const GROUP: usize = 60;
    let group = chained("a", " && a", GROUP - 1, "");
    let mut condition = group.clone();
    for _ in 1..LEVELS {
        condition = format!("({condition}) && {group}");
    }
    // Narrowing what the parentheses hold again at every level takes a multiple of the levels.
    let head = "fn main(a: bool) -> int {";
    assert!(nodes_per_operator(head, &condition, LEVELS * GROUP) < 16);
}

#[test]
fn long_field_chains_lower_without_overflowing() {
    analyzes(chained(
        "type P { p: int }\nfn main(p: P) -> int { p",
        ".p",
        20_000,
        " + true }\n",
    ));
}
