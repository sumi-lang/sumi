//! Formatting and lossless reprinting for Sumi.
//!
//! The syntax tree stores structure only; the token buffers keep every byte
//! of the source. [`elements`] interleaves the two — the raw tokens attached
//! directly to a node with its child subtrees — and [`reprint`] walks them
//! to reconstruct the source byte for byte. [`format`] lays the tokens out
//! afresh: a separator per gap, chosen by rules over the tree and fitted to
//! a width, with comments and retained blank lines kept in place and every
//! gap the parser recovered around left as written. [`rep`] is its
//! contract: the layout-free content of a source, which formatting keeps.
//! [`layout_violation_edits`] gives each spacing violation the parser
//! accepted as written its mechanical fix, for diagnostics to offer.

mod plan;
mod print;
pub mod rep;
pub mod trivia;

use std::fmt;

use sumi_lexer::{LexErrorKind, LexedFile, lex};
use sumi_syntax::{
    NodeIdx, Parse, ParseViolation, ParseViolationKind, ParserInput, RawIdx, SyntaxKind,
    SyntaxTree, parse,
};
use sumi_text::{TextEdit, TextRange, TextSize};

pub use plan::{INDENT, WIDTH};
pub use rep::{ItemRep, Rep, rep};

/// The formatted form of one source.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Formatted {
    /// The formatted text: the source with the edits applied.
    pub text: String,
    /// The edits, sorted and disjoint, that turn the source into the text.
    pub edits: Box<[TextEdit]>,
    /// Top-level items left as written because formatting them would have
    /// changed their parse: recovery is layout-sensitive where the parser
    /// recovered.
    pub reverted: usize,
}

/// The formatter would have changed the parse of the whole file, even
/// with every disagreeing item left as written: a formatter bug, and the
/// source is untouched.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Defect {
    /// The text the formatter produced and rejected.
    pub rejected: String,
}

impl fmt::Display for Defect {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("formatting would change the parse; the source is left as written")
    }
}

impl std::error::Error for Defect {}

/// Format `source`, which `lexed` and `parsed` must be the products of:
/// canonical spacing and indentation, lines fitted to [`WIDTH`], comments
/// and retained blank lines kept in place, and everything the parser
/// recovered around left as written. The result has the [`rep`] of the
/// source, or an item that would not is left as written, or the whole is
/// a [`Defect`].
pub fn format(source: &str, lexed: &LexedFile, parsed: &Parse) -> Result<Formatted, Defect> {
    let input = ParserInput::new(lexed);
    let plan = plan::plan(lexed, &input, parsed);
    let mut edits = print::print(source, lexed, &input, &plan);
    let before = rep(source, lexed, &input, parsed.tree());

    let candidate = apply_gap_edits(source, &edits);
    let mut reverted = 0;
    if let Some(disagreeing) = mismatch(&before, &candidate) {
        // Drop the edits inside every item whose rep changed; the gaps
        // between items stay formatted.
        let tree = parsed.tree();
        let sig_of_raw = rep::sig_of_raw(&input, lexed);
        let items: Vec<NodeIdx> = tree.children_in_order(tree.root()).collect();
        for (index, &item) in items.iter().enumerate() {
            if !disagreeing.contains(&index) {
                continue;
            }
            reverted += 1;
            let first = sig_of_raw[tree.first_token(item).to_usize()] as usize;
            let end = sig_of_raw[tree.end_token(item).to_usize() - 1] as usize + 1;
            edits.retain(|edit| edit.gap <= first || edit.gap >= end);
        }
        let candidate = apply_gap_edits(source, &edits);
        if mismatch(&before, &candidate).is_some() {
            return Err(Defect {
                rejected: candidate,
            });
        }
        return Ok(Formatted {
            text: candidate,
            edits: edits.into_iter().map(|edit| edit.edit).collect(),
            reverted,
        });
    }
    Ok(Formatted {
        text: candidate,
        edits: edits.into_iter().map(|edit| edit.edit).collect(),
        reverted,
    })
}

fn apply_gap_edits(source: &str, edits: &[print::GapEdit]) -> String {
    let edits: Vec<TextEdit> = edits.iter().map(|edit| edit.edit.clone()).collect();
    sumi_text::apply(source, &edits)
}

/// The items of `before` whose rep differs in `candidate`, or every item
/// when the file's shape differs; `None` when the reps agree.
fn mismatch(before: &Rep<'_>, candidate: &str) -> Option<Vec<usize>> {
    let Ok(lexed) = lex(candidate) else {
        return Some((0..before.items.len()).collect());
    };
    let input = ParserInput::new(&lexed);
    let parsed = parse(&input);
    let after = rep(candidate, &lexed, &input, parsed.tree());
    if after == *before {
        return None;
    }
    if after.items.len() != before.items.len() || after.edges != before.edges {
        return Some((0..before.items.len()).collect());
    }
    Some(
        (0..before.items.len())
            .filter(|&index| after.items[index] != before.items[index])
            .collect(),
    )
}

/// One element of a node: a raw token attached directly to it, or a child
/// subtree. Trivia between two children belongs to the parent and edge
/// trivia to the root, so a node's elements cover its raw token range
/// exactly, in source order.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Element {
    /// A raw index into the tree's token buffers.
    Token(RawIdx),
    /// A node index into the tree.
    Node(NodeIdx),
}

/// Iterate the elements of node `index`: its directly attached raw tokens
/// interleaved with its children.
pub fn elements(tree: &SyntaxTree, index: NodeIdx) -> impl Iterator<Item = Element> + '_ {
    // The tree yields children last first; elements read in source order.
    // The public lazy iterator owns this reversal; reprinting instead uses
    // shared traversal stacks so it does not allocate once per node.
    let mut children: Vec<NodeIdx> = tree.children(index).collect();
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
    let mut pending = Vec::new();
    let root = tree.root();
    pending.extend(tree.children(root));
    let mut frames = vec![(root, 0, tree.first_token(root))];

    while let Some((node, base, mut cursor)) = frames.pop() {
        if pending.len() > base {
            let child = pending.pop().expect("a pending child exists above base");
            for token in cursor.until(tree.first_token(child)) {
                out.push_str(lexed.text(source, token));
            }
            cursor = tree.end_token(child);
            frames.push((node, base, cursor));

            let child_base = pending.len();
            pending.extend(tree.children(child));
            frames.push((child, child_base, tree.first_token(child)));
        } else {
            for token in cursor.until(tree.end_token(node)) {
                out.push_str(lexed.text(source, token));
            }
        }
    }
    out
}

/// Build the mechanically valid candidate edits for one parser layout
/// violation. The edits are nonempty, nonoverlapping, and source ordered,
/// and none joins a hole's line to the next, which would change what the
/// lexer makes of both. Nothing here checks the result reparses: a fix is
/// one diagnostic's offer, and [`format`] is what rewrites a whole file.
pub fn layout_violation_edits(
    lexed: &LexedFile,
    violation: ParseViolation,
) -> Option<Box<[TextEdit]>> {
    let (start, end) = (violation.range.start(), violation.range.end());
    let mut edits = Vec::new();
    match violation.kind {
        // Space the operator on each side another token is glued to.
        ParseViolationKind::UnspacedBinaryOperator => {
            if start
                .checked_sub(1)
                .is_some_and(|before| significant(lexed, before))
            {
                edits.push(insert(token_start(lexed, start), " "));
            }
            if end < lexed.end() && significant(lexed, end) {
                edits.push(insert(token_start(lexed, end), " "));
            }
        }
        // Glue the operator to its operand only when the gap is clean trivia:
        // comments and lexer errors are evidence no fix may erase. A line
        // break in the gap closes a hole its line left open, and the
        // operand is the next line's code, not the hole's: that break stays.
        ParseViolationKind::SpacedPrefixOperator => {
            let operand = next_significant(lexed, start + 1)
                .expect("a spaced prefix operator has an operand");
            let gap = (start + 1).until(operand);
            if !gap.clone().all(|raw| {
                matches!(
                    lexed.kind(raw),
                    SyntaxKind::Whitespace | SyntaxKind::Newline
                )
            }) || lex_error_in(lexed, start + 1, operand)
            {
                return None;
            }
            if gap
                .clone()
                .any(|raw| lexed.kind(raw) == SyntaxKind::Newline)
                && hole_open_before(lexed, start)
            {
                return None;
            }
            edits.push(delete(token_end(lexed, start), token_start(lexed, operand)));
        }
        ParseViolationKind::SpacedListOpener => {
            let owner = prev_significant(lexed, start)?;
            if !(owner + 1)
                .until(start)
                .all(|raw| lexed.kind(raw) == SyntaxKind::Whitespace)
                || lex_error_in(lexed, owner + 1, start)
            {
                return None;
            }
            edits.push(delete(token_end(lexed, owner), token_start(lexed, start)));
        }
        ParseViolationKind::FunctionNameOnNextLine => {
            let keyword = prev_significant(lexed, start)?;
            let gap = (keyword + 1).until(start);
            if !gap.clone().all(|raw| {
                matches!(
                    lexed.kind(raw),
                    SyntaxKind::Whitespace | SyntaxKind::Newline
                )
            }) || lex_error_in(lexed, keyword + 1, start)
            {
                return None;
            }
            edits.push(replace(
                token_end(lexed, keyword),
                token_start(lexed, start),
                " ",
            ));
        }
        ParseViolationKind::FunctionItemOnSameLine => {
            let previous = prev_significant(lexed, start)?;
            if !(previous + 1)
                .until(start)
                .all(|raw| lexed.kind(raw) == SyntaxKind::Whitespace)
                || lex_error_in(lexed, previous + 1, start)
            {
                return None;
            }
            edits.push(replace(
                token_end(lexed, previous),
                token_start(lexed, start),
                "\n",
            ));
        }
        ParseViolationKind::BindingNameOnNextLine => {
            let before_name = prev_significant(lexed, start)?;
            let has_mut = lexed.kind(before_name) == SyntaxKind::MutKw;
            let let_keyword = if has_mut {
                prev_significant(lexed, before_name)?
            } else {
                before_name
            };
            let head = (let_keyword + 1).until(start);
            if !head.clone().all(|raw| {
                matches!(
                    lexed.kind(raw),
                    SyntaxKind::Whitespace | SyntaxKind::Newline | SyntaxKind::MutKw
                )
            }) || lex_error_in(lexed, let_keyword + 1, start)
            {
                return None;
            }
            let mut gaps = [(let_keyword, start); 2];
            let gap_count = if has_mut {
                gaps = [(let_keyword, before_name), (before_name, start)];
                2
            } else {
                1
            };
            for &(left, right) in &gaps[..gap_count] {
                let gap = (left + 1).until(right);
                if gap
                    .clone()
                    .any(|raw| lexed.kind(raw) == SyntaxKind::Newline)
                {
                    edits.push(replace(
                        token_end(lexed, left),
                        token_start(lexed, right),
                        " ",
                    ));
                }
            }
        }
        ParseViolationKind::ChainedComparison => return None,
    }
    (!edits.is_empty()).then(|| edits.into_boxed_slice())
}

fn insert(at: usize, text: impl Into<Box<str>>) -> TextEdit {
    replace(at, at, text)
}

fn delete(start: usize, end: usize) -> TextEdit {
    replace(start, end, "")
}

fn replace(start: usize, end: usize, text: impl Into<Box<str>>) -> TextEdit {
    TextEdit::new(
        TextRange::new(
            TextSize::new(u32::try_from(start).expect("source offset fits in u32")),
            TextSize::new(u32::try_from(end).expect("source offset fits in u32")),
        ),
        text,
    )
}

fn significant(lexed: &LexedFile, raw: RawIdx) -> bool {
    !lexed.kind(raw).is_trivia()
}

fn lex_error_in(lexed: &LexedFile, start: RawIdx, end: RawIdx) -> bool {
    let errors = lexed.errors();
    let first = errors.partition_point(|error| error.token < start);
    errors.get(first).is_some_and(|error| error.token < end)
}

/// Whether a hole in a string literal is still open where the line of
/// raw token `raw` ends: an unclosed hole reported on that line before
/// `raw`. A hole ends with its line, so its `{` is on the line too.
fn hole_open_before(lexed: &LexedFile, raw: RawIdx) -> bool {
    let line_start = RawIdx::new(0)
        .until(raw)
        .rev()
        .find(|&raw| lexed.kind(raw) == SyntaxKind::Newline)
        .map_or(RawIdx::new(0), |newline| newline + 1);
    let errors = lexed.errors();
    let first = errors.partition_point(|error| error.token < line_start);
    errors[first..]
        .iter()
        .take_while(|error| error.token < raw)
        .any(|error| error.kind == LexErrorKind::UnclosedHole)
}

/// The nearest significant token before `raw`.
fn prev_significant(lexed: &LexedFile, raw: RawIdx) -> Option<RawIdx> {
    RawIdx::new(0)
        .until(raw)
        .rev()
        .find(|&raw| significant(lexed, raw))
}

/// The nearest significant token at or after `raw`.
fn next_significant(lexed: &LexedFile, raw: RawIdx) -> Option<RawIdx> {
    raw.until(lexed.end()).find(|&raw| significant(lexed, raw))
}

fn token_start(lexed: &LexedFile, raw: RawIdx) -> usize {
    lexed.boundary(raw).to_usize()
}

fn token_end(lexed: &LexedFile, raw: RawIdx) -> usize {
    lexed.range(raw).end().to_usize()
}
