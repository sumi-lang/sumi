//! Lossless reprinting and layout normalization for Sumi.
//!
//! The syntax tree stores structure only; the token buffers keep every byte
//! of the source. [`elements`] interleaves the two — the raw tokens attached
//! directly to a node with its child subtrees — and [`reprint`] walks them
//! to reconstruct the source byte for byte. [`normalize`] rewrites the
//! layout violations the parser accepted as written — operator spacing and
//! block placement — into canonical form, leaving every other byte,
//! comments included, in place.

use sumi_lexer::LexedFile;
use sumi_syntax::{
    CookedFile, ParseEvidence, ParseViolationKind, SyntaxKind, SyntaxTree, raw_boundary,
};

/// One element of a node: a raw token attached directly to it, or a child
/// subtree. Trivia between two children belongs to the parent and edge
/// trivia to the root, so a node's elements cover its raw token range
/// exactly, in source order.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Element {
    /// A raw index into the tree's token buffers.
    Token(u32),
    /// A node index into the tree.
    Node(usize),
}

/// Iterate the elements of node `index`: its directly attached raw tokens
/// interleaved with its children.
pub fn elements(tree: &SyntaxTree, index: usize) -> impl Iterator<Item = Element> + '_ {
    // The tree yields children last first; elements read in source order.
    // TODO: the reversal buys a Vec per node — a reversed element walk
    // over one shared stack would make reprint allocation-free.
    let mut children: Vec<usize> = tree.children(index).collect();
    children.reverse();
    let mut children = children.into_iter().peekable();
    let mut cursor = tree.first_token(index);
    let end = tree.end_token(index);
    std::iter::from_fn(move || {
        if let Some(&child) = children.peek() {
            if cursor < tree.first_token(child) {
                cursor += 1;
                return Some(Element::Token(cursor - 1));
            }
            children.next();
            cursor = tree.end_token(child);
            Some(Element::Node(child))
        } else if cursor < end {
            cursor += 1;
            Some(Element::Token(cursor - 1))
        } else {
            None
        }
    })
}

/// Reconstruct the source of `tree` byte for byte from its token buffer.
/// `lexed` and `source` must be the file and text the tree was parsed from.
pub fn reprint(tree: &SyntaxTree, lexed: &LexedFile, source: &str) -> String {
    let mut out = String::with_capacity(source.len());
    reprint_node(tree, lexed, source, tree.root(), &mut out);
    out
}

fn reprint_node(tree: &SyntaxTree, lexed: &LexedFile, source: &str, node: usize, out: &mut String) {
    for element in elements(tree, node) {
        match element {
            Element::Token(token) => out.push_str(lexed.text(source, token as usize)),
            Element::Node(child) => reprint_node(tree, lexed, source, child, out),
        }
    }
}

/// Rewrite the layout violations in `evidence` into canonical form: space
/// binary operators, glue prefix operators, lead continuation lines with
/// their operator, and open blocks on the line of their owner. Every other
/// byte keeps its place; a comment is never deleted, at worst the gap it
/// blocks stays as written. Chained comparisons are structural, not layout,
/// and stay as written too.
pub fn normalize(
    source: &str,
    lexed: &LexedFile,
    cooked: &CookedFile,
    evidence: &[ParseEvidence],
) -> String {
    let mut edits = Vec::new();
    for evidence in evidence {
        let ParseEvidence::Violation(violation) = evidence else {
            continue;
        };
        let (start, end) = (violation.range.start(), violation.range.end());
        match violation.kind {
            // Move the `{` to its owner's line; the gap's trivia — comments
            // included — follows it instead.
            ParseViolationKind::BlockOnNewLine => {
                let owner =
                    prev_significant(cooked, start).expect("a misplaced block follows its owner");
                edits.push(Edit::insert(token_end(lexed, owner), " {"));
                edits.push(Edit::delete(
                    token_start(lexed, start),
                    token_end(lexed, start),
                ));
            }
            // Space the operator on each side another token is glued to.
            ParseViolationKind::UnspacedBinaryOperator => {
                if start > 0 && significant(cooked, start - 1) {
                    edits.push(Edit::insert(token_start(lexed, start), " "));
                }
                if (end as usize) < cooked.len() && significant(cooked, end) {
                    edits.push(Edit::insert(token_start(lexed, end), " "));
                }
            }
            // Lead the continuation line with the operator instead.
            ParseViolationKind::TrailingOperator => {
                let continuation = next_significant(cooked, end)
                    .expect("a trailing operator has a continuation line");
                let (op_start, op_end) = (token_start(lexed, start), token_end(lexed, end - 1));
                edits.push(Edit::delete(op_start, op_end));
                edits.push(Edit::insert(
                    token_start(lexed, continuation),
                    format!("{} ", &source[op_start..op_end]),
                ));
            }
            // Glue the operator to its operand — unless a comment sits in
            // the gap, which no layout edit may delete.
            ParseViolationKind::SpacedPrefixOperator => {
                let operand = next_significant(cooked, start + 1)
                    .expect("a spaced prefix operator has an operand");
                if (start + 1..operand)
                    .all(|raw| cooked.kind(raw as usize) != SyntaxKind::LineComment)
                {
                    edits.push(Edit::delete(
                        token_end(lexed, start),
                        token_start(lexed, operand),
                    ));
                }
            }
            ParseViolationKind::ChainedComparison => {}
        }
    }
    apply(source, edits)
}

/// One replacement of a byte range with new text.
struct Edit {
    start: usize,
    end: usize,
    text: String,
}

impl Edit {
    fn insert(at: usize, text: impl Into<String>) -> Self {
        Self {
            start: at,
            end: at,
            text: text.into(),
        }
    }

    fn delete(start: usize, end: usize) -> Self {
        Self {
            start,
            end,
            text: String::new(),
        }
    }
}

/// Apply `edits` to `source`. Violations never share tokens, so the edits
/// are disjoint; inserts at one boundary keep their recording order.
fn apply(source: &str, mut edits: Vec<Edit>) -> String {
    edits.sort_by_key(|edit| (edit.start, edit.end));
    let mut out = String::with_capacity(source.len());
    let mut cursor = 0;
    for edit in edits {
        assert!(cursor <= edit.start, "layout edits must not overlap");
        out.push_str(&source[cursor..edit.start]);
        out.push_str(&edit.text);
        cursor = edit.end;
    }
    out.push_str(&source[cursor..]);
    out
}

fn significant(cooked: &CookedFile, raw: u32) -> bool {
    !matches!(
        cooked.kind(raw as usize),
        SyntaxKind::Whitespace | SyntaxKind::Newline | SyntaxKind::LineComment
    )
}

/// The nearest significant token before `raw`.
fn prev_significant(cooked: &CookedFile, raw: u32) -> Option<u32> {
    (0..raw).rev().find(|&raw| significant(cooked, raw))
}

/// The nearest significant token at or after `raw`.
fn next_significant(cooked: &CookedFile, raw: u32) -> Option<u32> {
    (raw..cooked.len() as u32).find(|&raw| significant(cooked, raw))
}

fn token_start(lexed: &LexedFile, raw: u32) -> usize {
    raw_boundary(lexed, raw).to_usize()
}

fn token_end(lexed: &LexedFile, raw: u32) -> usize {
    lexed.range(raw as usize).end().to_usize()
}
