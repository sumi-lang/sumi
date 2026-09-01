//! One edit to a well-formed program, made at a significant token, and the
//! mapping that carries unaffected spans into the edited source.

use proptest::prelude::*;
use sumi_syntax::{ParserInput, SigIdx, SyntaxKind, is_bracket};

use crate::front::front;
use crate::program::program;

/// One edit to a well-formed program, made at a significant token.
#[derive(Clone, Copy, Debug)]
pub enum Edit {
    /// Remove the token.
    Delete,
    /// Insert a spaced copy of the token after it.
    Duplicate,
    /// Exchange the token with its neighbour, keeping the trivia between.
    Swap,
    /// Insert this text, spaced, before the token.
    Insert(&'static str),
}

/// Tokens to insert: brackets above all, then keywords and operators that
/// start or continue something.
pub const INSERTS: &[&str] = &[
    "(", ")", "{", "}", ",", "=", "fn", "let", "else", "x", "0", "+", "-",
];

pub fn edit() -> impl Strategy<Value = Edit> {
    prop_oneof![
        3 => Just(Edit::Delete),
        2 => Just(Edit::Duplicate),
        2 => Just(Edit::Swap),
        3 => prop::sample::select(INSERTS).prop_map(Edit::Insert),
    ]
}

/// The significant index of position `index` in a program's spans.
fn sig(index: usize) -> SigIdx {
    SigIdx::new(u32::try_from(index).expect("significant positions fit in u32"))
}

/// Whether `edit` inserts, removes, duplicates, or moves a bracket.
pub fn changes_delimiter(input: &ParserInput, index: usize, edit: Edit) -> bool {
    let bracket_at = |index: usize| input.get(sig(index)).is_some_and(is_bracket);
    match edit {
        Edit::Delete | Edit::Duplicate => bracket_at(index),
        Edit::Insert(inserted) => SyntaxKind::ALL
            .iter()
            .any(|&kind| is_bracket(kind) && kind.text() == Some(inserted)),
        Edit::Swap => {
            let left = if index + 1 < input.len() {
                index
            } else {
                index - 1
            };
            bracket_at(left) || bracket_at(left + 1)
        }
    }
}

/// A well-formed program with at least two significant tokens, the index of
/// one of them, and an edit to make there.
pub fn edited_program() -> impl Strategy<Value = (String, usize, Edit)> {
    program()
        .prop_filter("an edit needs two tokens", |source| {
            front(source).input.len() >= 2
        })
        .prop_flat_map(|source| {
            let count = front(&source).input.len();
            (Just(source), 0..count, edit())
        })
}

pub fn non_delimiter_edited_program() -> impl Strategy<Value = (String, usize, Edit)> {
    edited_program().prop_filter("the edit changes no delimiter", |(source, index, edit)| {
        !changes_delimiter(&front(source).input, *index, *edit)
    })
}

pub fn delimiter_edited_program() -> impl Strategy<Value = (String, usize, Edit)> {
    edited_program().prop_filter("the edit changes a delimiter", |(source, index, edit)| {
        changes_delimiter(&front(source).input, *index, *edit)
    })
}

/// The replaced byte interval in the original and where it ends afterward.
#[derive(Clone, Copy)]
pub struct EditSpan {
    start: usize,
    old_end: usize,
    new_end: usize,
}

impl EditSpan {
    /// Map a span disjoint from the edit into the edited source.
    pub fn map(self, (start, end): (usize, usize)) -> (usize, usize) {
        if end <= self.start {
            return (start, end);
        }
        assert!(start >= self.old_end, "a guarded node overlaps the edit");
        let shift = self.new_end as isize - self.old_end as isize;
        (
            start
                .checked_add_signed(shift)
                .expect("mapped start is in range"),
            end.checked_add_signed(shift)
                .expect("mapped end is in range"),
        )
    }
}

/// Apply `edit` at significant token `index` of `source`: the edited text,
/// the significant indices the edit touches, those it removes or moves, and
/// the replaced byte interval for mapping unaffected nodes.
///
/// The touched indices include two tokens on either side of the edit: an
/// inserted token joins whatever it lands next to — a leading operator or
/// `else` continues the statement above, a `(` after a name makes a call —
/// and a deleted token can leave a dangling operator that takes the next
/// line as its operand. Jointness can change the arity of that neighbouring
/// operator and therefore the boundary after the token before it. Those are
/// the language's rules, not recovery, so this local context is the edit's
/// own business.
pub fn apply(
    source: &str,
    spans: &[(usize, usize)],
    index: usize,
    edit: Edit,
) -> (String, Vec<usize>, Vec<usize>, EditSpan) {
    let (start, end) = spans[index];
    let text = &source[start..end];
    let (edited, left, right, impact) = match edit {
        Edit::Delete => (
            format!("{}{}", &source[..start], &source[end..]),
            index,
            index,
            EditSpan {
                start,
                old_end: end,
                new_end: start,
            },
        ),
        Edit::Duplicate => (
            format!("{} {text}{}", &source[..end], &source[end..]),
            index,
            index,
            EditSpan {
                start: end,
                old_end: end,
                new_end: end + 1 + text.len(),
            },
        ),
        Edit::Insert(inserted) => (
            format!("{}{inserted} {}", &source[..start], &source[start..]),
            index,
            index,
            EditSpan {
                start,
                old_end: start,
                new_end: start + inserted.len() + 1,
            },
        ),
        Edit::Swap => {
            let (left, right) = if index + 1 < spans.len() {
                (index, index + 1)
            } else {
                (index - 1, index)
            };
            let ((ls, le), (rs, re)) = (spans[left], spans[right]);
            let edited = format!(
                "{}{}{}{}{}",
                &source[..ls],
                &source[rs..re],
                &source[le..rs],
                &source[ls..le],
                &source[re..]
            );
            (
                edited,
                left,
                right,
                EditSpan {
                    start: ls,
                    old_end: re,
                    new_end: re,
                },
            )
        }
    };
    let touched = (left.saturating_sub(2)..=(right + 2).min(spans.len() - 1)).collect();
    let moved = match edit {
        Edit::Delete => vec![index],
        Edit::Swap => vec![left, right],
        Edit::Duplicate | Edit::Insert(_) => Vec::new(),
    };
    (edited, touched, moved, impact)
}
