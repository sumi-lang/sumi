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
}

#[test]
fn long_lazy_chains_lower_without_overflowing() {
    // Literals narrow nothing: a chain of one local is narrowed again under every operator.
    analyzes(chained(
        "fn main() -> int { if true",
        " && true",
        1_000,
        " { 1 } else { true } }\n",
    ));
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
