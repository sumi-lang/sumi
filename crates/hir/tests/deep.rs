use sumi_frontend::parse_source;
use sumi_hir::analyze;
use sumi_syntax::MAX_DEPTH;

/// A body nested past the parser's limit, which it recovers at, so lowering sees the deepest
/// tree the parser yields. The harness thread's stack is the smallest any analysis runs on:
/// every construct here fits in a quarter of it in a debug build.
fn analyzes(open: &str, close: &str, innermost: &str) {
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
    let analysis = analyze(parse_source(source.into()).unwrap());
    assert!(!analysis.diagnostics().is_empty());
}

#[test]
fn deeply_nested_blocks_lower_without_overflowing() {
    analyzes("{ ", " }", "1");
}

#[test]
fn deeply_nested_branches_lower_without_overflowing() {
    analyzes("if true { ", " } else { 0 }", "1");
}

#[test]
fn deeply_nested_parentheses_and_calls_lower_without_overflowing() {
    analyzes("(", ")", "1");
    analyzes("f(", ")", "1");
}

#[test]
fn deeply_nested_operators_lower_without_overflowing() {
    analyzes("-", "", "1");
    analyzes("1 + (", ")", "1");
}

#[test]
fn deeply_nested_matches_and_loops_lower_without_overflowing() {
    analyzes("match true { _ => ", " }", "1");
    analyzes("for i in 0..1 { ", " }", "1");
}
