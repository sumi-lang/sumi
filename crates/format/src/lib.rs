//! Formatting: a separator per gap, fitted to a width, comments kept in place. [`rep`](fn@rep) is
//! the contract: the result has the source's layout-free content.

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

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Formatted {
    pub text: String,
    /// Sorted and disjoint; applied to the source, they give `text`.
    pub edits: Box<[TextEdit]>,
    /// Top-level items left as written; formatting them would change their parse.
    pub reverted: usize,
}

/// A formatter bug: the parse changes even with every disagreeing item left as written.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Defect {
    pub rejected: String,
}

impl fmt::Display for Defect {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("formatting would change the parse; the source is left as written")
    }
}

impl std::error::Error for Defect {}

/// The result has the source's [`rep`](fn@rep); an item that would lose it is left as written.
pub fn format(source: &str, lexed: &LexedFile, parsed: &Parse) -> Result<Formatted, Defect> {
    let input = parsed.input();
    let plan = plan::plan(lexed, parsed);
    let mut edits = print::print(source, lexed, input, &plan);
    if edits.is_empty() {
        return Ok(Formatted {
            text: source.to_owned(),
            edits: Box::new([]),
            reverted: 0,
        });
    }
    let before = rep(source, lexed, parsed);

    let mut text = apply_gap_edits(source, &edits);
    let mut reverted = 0;
    if let Some(disagreeing) = mismatch(&before, &text) {
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

pub(crate) fn first_sig(tree: &SyntaxTree, input: &ParserInput, node: NodeIdx) -> u32 {
    input.sig_at_or_after(tree.first_token(node)).to_u32()
}

pub(crate) fn end_sig(tree: &SyntaxTree, input: &ParserInput, node: NodeIdx) -> u32 {
    input.sig_at_or_after(tree.end_token(node)).to_u32()
}

fn apply_gap_edits(source: &str, edits: &[print::GapEdit]) -> String {
    sumi_text::apply(source, edits.iter().map(|edit| &edit.edit))
}

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
