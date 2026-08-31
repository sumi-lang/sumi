//! Lossless reprinting and layout normalization for Sumi.
//!
//! The syntax tree stores structure only; the token buffers keep every byte
//! of the source. [`elements`] interleaves the two — the raw tokens attached
//! directly to a node with its child subtrees — and [`reprint`] walks them
//! to reconstruct the source byte for byte. [`normalize`] rewrites the
//! layout violations the parser accepted as written — operator spacing and
//! block placement — into canonical form, leaving every other byte,
//! comments included, in place.

use sumi_lexer::{LexedFile, lex};
use sumi_syntax::{
    Parse, ParseEvidence, ParseViolationKind, ParserInput, SyntaxKind, SyntaxTree, parse,
    raw_boundary, starts_expression,
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

/// Rewrite the layout violations of `parsed` into canonical form: space
/// binary operators, glue prefix operators, lead continuation lines with
/// their operator, and open blocks on the line of their owner. Every other
/// byte keeps its place; a comment is never deleted, at worst the gap it
/// blocks stays as written. Chained comparisons are structural, not layout,
/// and stay as written too, as does a trailing operator whose continuation
/// line does not begin its operand.
///
/// The rewrite proves it changed only layout: the result reparses to the
/// same tree shape, or the source comes back as written. Around recovered
/// damage, what the parser makes of a line can turn on where the line
/// breaks — a moved operator or brace may hand recovery a different
/// reading — and no local check on the tokens settles it.
pub fn normalize(source: &str, lexed: &LexedFile, parsed: &Parse) -> String {
    let mut edits = Vec::new();
    for evidence in parsed.evidence() {
        let ParseEvidence::Violation(violation) = evidence else {
            continue;
        };
        let (start, end) = (violation.range.start(), violation.range.end());
        match violation.kind {
            // Move the `{` to its owner's line; the gap's trivia — comments
            // included — follows it instead.
            ParseViolationKind::BlockOnNewLine => {
                let owner =
                    prev_significant(lexed, start).expect("a misplaced block follows its owner");
                edits.push(Edit::insert(token_end(lexed, owner), " {"));
                edits.push(Edit::delete(
                    token_start(lexed, start),
                    token_end(lexed, start),
                ));
            }
            // Space the operator on each side another token is glued to.
            ParseViolationKind::UnspacedBinaryOperator => {
                if start > 0 && significant(lexed, start - 1) {
                    edits.push(Edit::insert(token_start(lexed, start), " "));
                }
                if (end as usize) < lexed.len() && significant(lexed, end) {
                    edits.push(Edit::insert(token_start(lexed, end), " "));
                }
            }
            // Lead the continuation line with the operator instead. The
            // parser records the violation before parsing the operand, so
            // the continuation may turn out not to hold one; only an
            // operator moved in front of its own operand leaves the parse
            // unchanged, and anything else stays as written.
            ParseViolationKind::TrailingOperator => {
                let operand = next_significant(lexed, end)
                    .filter(|&raw| starts_expression(lexed.kind(raw as usize)));
                if let Some(operand) = operand {
                    let (op_start, op_end) = (token_start(lexed, start), token_end(lexed, end - 1));
                    edits.push(Edit::delete(op_start, op_end));
                    edits.push(Edit::insert(
                        token_start(lexed, operand),
                        format!("{} ", &source[op_start..op_end]),
                    ));
                }
            }
            // Glue the operator to its operand — unless a comment sits in
            // the gap, which no layout edit may delete.
            ParseViolationKind::SpacedPrefixOperator => {
                let operand = next_significant(lexed, start + 1)
                    .expect("a spaced prefix operator has an operand");
                if (start + 1..operand)
                    .all(|raw| lexed.kind(raw as usize) != SyntaxKind::LineComment)
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
    if edits.is_empty() {
        return source.to_owned();
    }
    let candidate = apply(source, edits);
    if reparses_alike(&candidate, parsed.tree()) {
        candidate
    } else {
        source.to_owned()
    }
}

/// Whether `candidate` parses to the same tree shape as `tree`: node for
/// node the same kinds and the same parents, with only byte positions free
/// to have moved.
fn reparses_alike(candidate: &str, tree: &SyntaxTree) -> bool {
    let Ok(lexed) = lex(candidate) else {
        return false;
    };
    let reparse = parse(&ParserInput::new(&lexed));
    let after = reparse.tree();
    after.len() == tree.len()
        && (0..tree.len()).all(|node| after.kind(node) == tree.kind(node))
        && after.parents() == tree.parents()
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

fn significant(lexed: &LexedFile, raw: u32) -> bool {
    !matches!(
        lexed.kind(raw as usize),
        SyntaxKind::Whitespace | SyntaxKind::Newline | SyntaxKind::LineComment
    )
}

/// The nearest significant token before `raw`.
fn prev_significant(lexed: &LexedFile, raw: u32) -> Option<u32> {
    (0..raw).rev().find(|&raw| significant(lexed, raw))
}

/// The nearest significant token at or after `raw`.
fn next_significant(lexed: &LexedFile, raw: u32) -> Option<u32> {
    (raw..lexed.len() as u32).find(|&raw| significant(lexed, raw))
}

fn token_start(lexed: &LexedFile, raw: u32) -> usize {
    raw_boundary(lexed, raw).to_usize()
}

fn token_end(lexed: &LexedFile, raw: u32) -> usize {
    lexed.range(raw as usize).end().to_usize()
}
