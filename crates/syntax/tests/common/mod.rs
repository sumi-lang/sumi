//! Shared helpers for the tree and parser tests.
#![allow(dead_code)]

use sumi_lexer::LexedFile;
use sumi_syntax::SyntaxTree;

/// Assert the tree invariants and render one line per node: `Kind
/// start..end` byte ranges, indented by depth, with the text of childless
/// nodes appended.
pub fn dump(tree: &SyntaxTree, lexed: &LexedFile, source: &str) -> Vec<String> {
    let mut lines = Vec::new();
    let mut visited = 0usize;
    render(tree, lexed, source, 0, 0, &mut lines, &mut visited);
    assert_eq!(visited, tree.len(), "extents must partition the tree");
    lines
}

fn render(
    tree: &SyntaxTree,
    lexed: &LexedFile,
    source: &str,
    node: usize,
    depth: usize,
    lines: &mut Vec<String>,
    visited: &mut usize,
) {
    *visited += 1;
    let first = tree.first_token(node);
    let end = tree.end_token(node);
    assert!(first <= end, "node {node} has a backwards token range");

    let from = start_byte(lexed, first);
    let to = if end > first {
        lexed.range(end as usize - 1).end().to_u32()
    } else {
        from
    };
    let mut line = format!(
        "{:indent$}{:?} {from}..{to}",
        "",
        tree.kind(node),
        indent = depth * 2
    );
    if tree.children(node).next().is_none() {
        line.push_str(&format!(" {:?}", &source[from as usize..to as usize]));
    }
    lines.push(line);

    let mut previous_end = first;
    for child in tree.children(node) {
        assert!(
            tree.first_token(child) >= previous_end,
            "children must be ordered and disjoint"
        );
        assert!(
            tree.end_token(child) <= end,
            "a child must stay inside its parent"
        );
        previous_end = tree.end_token(child);
        render(tree, lexed, source, child, depth + 1, lines, visited);
    }
}

/// The start byte of raw token `token`, or the end of the source one past
/// the last token.
pub fn start_byte(lexed: &LexedFile, token: u32) -> u32 {
    if (token as usize) < lexed.len() {
        lexed.range(token as usize).start().to_u32()
    } else {
        lexed.source_len().to_u32()
    }
}
