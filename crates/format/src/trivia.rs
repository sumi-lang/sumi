//! The signal a gap retains: its comments, and whether blank lines survive. The printer and
//! [`rep`](fn@crate::rep) both call [`signal`], so the two can't disagree.

use sumi_lexer::{LexedFile, RawIdx};
use sumi_syntax::{ParserInput, SigIdx, SyntaxKind, is_closer};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Comment<'s> {
    pub(crate) text: &'s str,
    pub(crate) trailing: bool,
    pub(crate) blank_before: bool,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct GapSignal<'s> {
    pub(crate) comments: Vec<Comment<'s>>,
    pub(crate) blank_before_token: bool,
}

fn retains_blank(input: &ParserInput, gap: usize) -> bool {
    let n = input.len();
    gap == 0
        || gap == n
        || (input.would_end_statement(SigIdx::new(gap as u32))
            && !input.get(SigIdx::new(gap as u32)).is_some_and(is_closer))
}

/// `trivia` must be the gap's tokens in raw order.
pub(crate) fn signal<'s>(
    source: &'s str,
    lexed: &LexedFile,
    input: &ParserInput,
    gap: usize,
    trivia: impl Iterator<Item = RawIdx>,
) -> GapSignal<'s> {
    let last = gap == input.len();
    let mut comments = Vec::new();
    let mut newlines = 0usize;
    let mut retained = None;
    let mut retained = || *retained.get_or_insert_with(|| retains_blank(input, gap));
    for raw in trivia {
        match lexed.kind(raw) {
            SyntaxKind::Newline => newlines += 1,
            SyntaxKind::LineComment => {
                let first = comments.is_empty();
                comments.push(Comment {
                    text: lexed.text(source, raw),
                    trailing: first && gap > 0 && newlines == 0,
                    blank_before: newlines >= 2 && !(gap == 0 && first) && retained(),
                });
                newlines = 0;
            }
            _ => {}
        }
    }
    let leading = gap == 0 && comments.is_empty();
    GapSignal {
        comments,
        blank_before_token: newlines >= 2 && !last && !leading && retained(),
    }
}
