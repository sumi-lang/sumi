//! Positional tree queries: covering chains and the on-demand parent table.

use sumi_lexer::lex;
use sumi_syntax::{NodeIdx, ParserInput, RawIdx, SyntaxTree, parse};

/// Every node whose token range contains `token`, by scanning the whole
/// tree: the exhaustive reference `covering_chain` must match. Covering
/// nodes nest and children complete before parents, so ascending order is
/// already innermost first.
fn covering_reference(tree: &SyntaxTree, token: RawIdx) -> Vec<NodeIdx> {
    tree.nodes()
        .filter(|&node| tree.first_token(node) <= token && token < tree.end_token(node))
        .collect()
}

/// Parse `source` and check `covering_chain`, `covering`, and `parents`
/// against exhaustive references, for every raw token in the file.
#[track_caller]
fn check_queries(source: &str) {
    let lexed = lex(source).expect("test sources fit in u32");
    let input = ParserInput::new(&lexed);
    let tree_parse = parse(&input);
    let tree = tree_parse.tree();

    let parents = tree.parents();
    assert_eq!(parents.len(), tree.len());
    assert_eq!(
        parents[tree.root().to_usize()],
        tree.root(),
        "the root names itself"
    );
    for node in tree.nodes() {
        for child in tree.children(node) {
            assert_eq!(parents[child.to_usize()], node, "parent of {child:?}");
        }
    }

    for token in lexed.indices() {
        let chain: Vec<NodeIdx> = tree.covering_chain(token).collect();
        assert_eq!(
            chain,
            covering_reference(tree, token),
            "covering chain for token {token:?} in {source:?}"
        );
        assert_eq!(
            tree.covering(token),
            chain[0],
            "covering node for token {token:?} in {source:?}"
        );
        // The chain is the parent walk out of its own head.
        for pair in chain.windows(2) {
            assert_eq!(parents[pair[0].to_usize()], pair[1]);
        }
    }
}

#[test]
fn covering_matches_the_exhaustive_reference_on_parsed_sources() {
    check_queries("fn f(a: Int) -> Int {\n    let x = a + 1\n    return x * 2\n}\n");
    check_queries("// leading\nfn g() {\n    h(1, (2 + 3), \"s\")\n}\n// trailing");
    check_queries("let a = if c { 1 } else { 2 }\nb.c(d)\n");
}

#[test]
fn covering_matches_the_reference_under_recovery() {
    check_queries("fn f( {\n    let x = ((1 +\n}\n");
    check_queries("fn ; broken [ let = \n }} )\n");
    check_queries("€ 'ab' \"open\nfn h() { return }\n");
}

#[test]
fn trivia_only_files_answer_the_root() {
    check_queries("  // just a comment\n\n");
}
