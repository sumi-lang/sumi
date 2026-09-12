//! The retained signal of a gap: what the formatter reads from the trivia
//! between two significant tokens, and what [`rep`](crate::rep) records.
//! Both read it through one function, so what the formatter keeps is by
//! definition what the oracle compares.

use sumi_lexer::{LexedFile, RawIdx};
use sumi_syntax::{ParserInput, SigIdx, SyntaxKind, is_closer};

/// One line comment in a gap.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Comment<'s> {
    pub text: &'s str,
    /// The comment followed the previous token on its line.
    pub trailing: bool,
    /// A retained blank line precedes the comment.
    pub blank_before: bool,
}

/// The retained signal of one gap: its comments in order, and whether a
/// retained blank line precedes the token after it.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct GapSignal<'s> {
    pub comments: Vec<Comment<'s>>,
    pub blank_before_token: bool,
}

/// Whether gap `gap` retains blank lines: the file's edges, and every gap
/// where a line break would end a statement unless a closer follows. A
/// leading blank line of the file and one before nothing are never kept.
pub fn retains_blank(input: &ParserInput, gap: usize) -> bool {
    let n = input.len();
    gap == 0
        || gap == n
        || (input.would_end_statement(SigIdx::new(gap as u32))
            && !input.get(SigIdx::new(gap as u32)).is_some_and(is_closer))
}

/// Read the signal of gap `gap` from `trivia`, its trivia tokens in order.
pub fn signal<'s>(
    source: &'s str,
    lexed: &LexedFile,
    input: &ParserInput,
    gap: usize,
    trivia: impl Iterator<Item = RawIdx>,
) -> GapSignal<'s> {
    let retained = retains_blank(input, gap);
    let last = gap == input.len();
    let mut comments = Vec::new();
    let mut newlines = 0usize;
    for raw in trivia {
        match lexed.kind(raw) {
            SyntaxKind::Newline => newlines += 1,
            SyntaxKind::LineComment => {
                let first = comments.is_empty();
                comments.push(Comment {
                    text: lexed.text(source, raw),
                    trailing: first && gap > 0 && newlines == 0,
                    blank_before: retained && !(gap == 0 && first) && newlines >= 2,
                });
                newlines = 0;
            }
            _ => {}
        }
    }
    // Blank lines at the head of the file are kept only after a comment.
    let leading = gap == 0 && comments.is_empty();
    GapSignal {
        comments,
        blank_before_token: !last && !leading && retained && newlines >= 2,
    }
}
