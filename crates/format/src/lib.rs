//! Formatting for Sumi.
//!
//! [`format`] lays a file's tokens out afresh: a separator per gap, chosen
//! by rules over the tree and fitted to a width, with comments and retained
//! blank lines kept in place and every gap the parser recovered around left
//! as written. [`rep`] is its contract: the layout-free content of a
//! source, which formatting keeps.

mod plan;
mod print;
mod rep;
mod trivia;

use std::fmt;

use sumi_lexer::{LexedFile, lex};
use sumi_syntax::{NodeIdx, Parse, ParserInput, SyntaxTree, parse};
use sumi_text::TextEdit;

pub use plan::WIDTH;
pub use rep::{Rep, rep};

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
    let input = parsed.input();
    let plan = plan::plan(lexed, parsed);
    let mut edits = print::print(source, lexed, input, &plan);
    let before = rep(source, lexed, parsed);

    let mut text = apply_gap_edits(source, &edits);
    let mut reverted = 0;
    if let Some(disagreeing) = mismatch(&before, &text) {
        // Drop the edits inside every item whose rep changed; the gaps
        // between items stay formatted.
        let tree = parsed.tree();
        let items: Vec<NodeIdx> = tree.children(tree.root()).collect();
        for &index in &disagreeing {
            let first = first_sig(tree, input, items[index]) as usize;
            let end = end_sig(tree, input, items[index]) as usize;
            edits.retain(|edit| edit.gap <= first || edit.gap >= end);
        }
        reverted = disagreeing.len();
        text = apply_gap_edits(source, &edits);
        if mismatch(&before, &text).is_some() {
            return Err(Defect { rejected: text });
        }
    }
    Ok(Formatted {
        text,
        edits: edits.into_iter().map(|edit| edit.edit).collect(),
        reverted,
    })
}

/// The significant index of the first token of `node`.
pub(crate) fn first_sig(tree: &SyntaxTree, input: &ParserInput, node: NodeIdx) -> u32 {
    input.sig_at_or_after(tree.first_token(node)).to_u32()
}

/// The significant index one past the last token of `node`.
pub(crate) fn end_sig(tree: &SyntaxTree, input: &ParserInput, node: NodeIdx) -> u32 {
    input.sig_at_or_after(tree.end_token(node)).to_u32()
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
    let after = rep(candidate, &lexed, &parse(ParserInput::new(&lexed)));
    if after.items.len() != before.items.len() || after.edges != before.edges {
        return Some((0..before.items.len()).collect());
    }
    let disagreeing: Vec<usize> = (0..before.items.len())
        .filter(|&index| after.items[index] != before.items[index])
        .collect();
    (!disagreeing.is_empty()).then_some(disagreeing)
}
