//! Positional tree queries: covering chains and the on-demand parent table.

use sumi_lexer::lex;
use sumi_syntax::NodeKind::{self, *};
use sumi_syntax::{Marker, Parse, ParserInput, SyntaxTree, parse};

/// Every node whose token range contains `token`, by scanning the whole
/// tree: the exhaustive reference `covering_chain` must match. Covering
/// nodes nest and children complete before parents, so ascending order is
/// already innermost first.
fn covering_reference(tree: &SyntaxTree, token: u32) -> Vec<usize> {
    (0..tree.len())
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
        parents[tree.root()] as usize,
        tree.root(),
        "the root names itself"
    );
    for node in 0..tree.len() {
        for child in tree.children(node) {
            assert_eq!(parents[child] as usize, node, "parent of {child}");
        }
    }

    for token in 0..lexed.len() as u32 {
        let chain: Vec<usize> = tree.covering_chain(token).collect();
        assert_eq!(
            chain,
            covering_reference(tree, token),
            "covering chain for token {token} in {source:?}"
        );
        assert_eq!(
            tree.covering(token),
            chain[0],
            "covering node for token {token} in {source:?}"
        );
        // The chain is the parent walk out of its own head.
        for pair in chain.windows(2) {
            assert_eq!(parents[pair[0]] as usize, pair[1]);
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

fn node(parent: &mut Marker<'_, '_>, kind: NodeKind, body: impl FnOnce(&mut Marker<'_, '_>)) {
    let mut child = parent.start();
    body(&mut child);
    child.complete(kind);
}

/// Build `let x = 1` by hand and probe the boundaries the parsed goldens
/// cannot pin: interior trivia answers the innermost node spanning it.
#[test]
fn trivia_between_children_belongs_to_the_spanning_node() {
    let source = "let x = 1 // c";
    let lexed = lex(source).expect("test sources fit in u32");
    let input = ParserInput::new(&lexed);
    let built = Parse::build(&input, |root| {
        node(root, LetStmt, |stmt| {
            stmt.token(); // let
            node(stmt, NameExpr, |name| name.token());
            stmt.token(); // =
            node(stmt, LiteralExpr, |literal| literal.token());
        });
    });
    let tree = built.tree();
    // Nodes complete in postorder: NameExpr 0, LiteralExpr 1, LetStmt 2,
    // the root 3. Tokens: `let` ` ` `x` ` ` `=` ` ` `1` ` ` `// c`.
    let chain = |token| built.tree().covering_chain(token).collect::<Vec<_>>();
    assert_eq!(chain(0), [2, 3]); // `let` — the statement
    assert_eq!(chain(1), [2, 3]); // the space inside it too
    assert_eq!(chain(2), [0, 2, 3]); // `x` — out from the name
    assert_eq!(chain(6), [1, 2, 3]); // `1` — out from the literal
    assert_eq!(chain(7), [3]); // trailing trivia — the root only
    assert_eq!(chain(8), [3]);
    assert_eq!(tree.covering(6), 1);
}

#[test]
#[should_panic(expected = "token must be within the file")]
fn covering_a_token_past_the_file_panics() {
    let source = "x";
    let lexed = lex(source).expect("test sources fit in u32");
    let input = ParserInput::new(&lexed);
    let built = Parse::build(&input, |root| {
        node(root, NameExpr, |name| name.token());
    });
    built.tree().covering(1);
}
