//! `covering`, checked against an exhaustive reference implementation.

use sumi_lexer::lex;
use sumi_syntax::{ParserInput, parse};

#[track_caller]
fn check_covering(source: &str) {
    let lexed = lex(source).expect("test sources fit in u32");
    let parse = parse(ParserInput::new(&lexed));
    let tree = parse.tree();
    for token in lexed.indices() {
        let innermost = tree
            .nodes()
            .filter(|&node| tree.first_token(node) <= token && token < tree.end_token(node))
            .min_by_key(|&node| tree.subtree_len(node))
            .expect("the root covers every token");
        assert_eq!(
            tree.covering(token),
            innermost,
            "covering node for token {token:?} in {source:?}"
        );
    }
}

#[test]
fn covering_matches_the_exhaustive_reference() {
    check_covering("fn f(a: Int) -> Int {\n    let x = a + 1\n    return x * 2\n}\n");
    check_covering("// leading\nfn g() {\n    h(1, (2 + 3), \"s\")\n}\n// trailing");
    check_covering("let a = if c { 1 } else { 2 }\nb.c(d)\n");
    check_covering("fn f( {\n    let x = ((1 +\n}\n");
    check_covering("fn ; broken [ let = \n }} )\n");
    check_covering("€ 'ab' \"open\nfn h() { return }\n");
    check_covering("");
    check_covering("  // just a comment\n\n");
    check_covering(&format!("fn f() = {}1{}", "(".repeat(64), ")".repeat(64)));
}
