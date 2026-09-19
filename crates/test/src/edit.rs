//! One edit to a well-formed program, made at a significant token, and the mapping that carries
//! unaffected spans into the edited source.

use proptest::prelude::*;
use sumi_syntax::{ParserInput, SigIdx, SyntaxKind, is_bracket};

use crate::front::front;
use crate::program::program;

#[derive(Clone, Copy, Debug)]
pub enum Edit {
    Delete,
    Duplicate,
    Swap,
    Insert(&'static str),
}

pub const INSERTS: &[&str] = &[
    "(", ")", "{", "}", ",", "=", "fn", "let", "else", "x", "0", "+", "-",
];

/// The `edit` fuzz target's input: one byte for the edit, a little-endian `u16` for the significant
/// token it lands on, then the source.
pub fn edit_input(data: &[u8]) -> Option<(Edit, u16, &str)> {
    let [kind, low, high, source @ ..] = data else {
        return None;
    };
    let edit = match kind % 4 {
        0 => Edit::Delete,
        1 => Edit::Duplicate,
        2 => Edit::Swap,
        _ => Edit::Insert(INSERTS[usize::from(kind / 4) % INSERTS.len()]),
    };
    Some((
        edit,
        u16::from_le_bytes([*low, *high]),
        std::str::from_utf8(source).ok()?,
    ))
}

/// One seed per edit kind, at the second significant token, in [`edit_input`]'s layout.
pub fn edit_seeds(source: &str) -> Vec<Vec<u8>> {
    (0u8..4)
        .map(|kind| [&[kind, 1, 0], source.as_bytes()].concat())
        .collect()
}

pub fn edit() -> impl Strategy<Value = Edit> {
    prop_oneof![
        3 => Just(Edit::Delete),
        2 => Just(Edit::Duplicate),
        2 => Just(Edit::Swap),
        3 => prop::sample::select(INSERTS).prop_map(Edit::Insert),
    ]
}

fn sig(index: usize) -> SigIdx {
    SigIdx::new(u32::try_from(index).expect("significant positions fit in u32"))
}

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

/// A program with two or more significant tokens, the index of one of them, and an edit to make
/// there.
pub fn edited_program() -> impl Strategy<Value = (String, usize, Edit)> {
    program()
        .prop_filter("an edit needs two tokens", |source| {
            front(source).input().len() >= 2
        })
        .prop_flat_map(|source| {
            let count = front(&source).input().len();
            (Just(source), 0..count, edit())
        })
}

pub fn non_delimiter_edited_program() -> impl Strategy<Value = (String, usize, Edit)> {
    edited_program().prop_filter("the edit changes no delimiter", |(source, index, edit)| {
        !changes_delimiter(front(source).input(), *index, *edit)
    })
}

pub fn delimiter_edited_program() -> impl Strategy<Value = (String, usize, Edit)> {
    edited_program().prop_filter("the edit changes a delimiter", |(source, index, edit)| {
        changes_delimiter(front(source).input(), *index, *edit)
    })
}

/// The bytes `start..old_end` of the original, replaced by text that ends at `new_end` in the
/// edited source.
#[derive(Clone, Copy)]
pub struct EditSpan {
    start: usize,
    old_end: usize,
    new_end: usize,
}

impl EditSpan {
    pub fn new(start: usize, old_end: usize, new_end: usize) -> Self {
        Self {
            start,
            old_end,
            new_end,
        }
    }

    /// Map a span that does not overlap the edit into the edited source.
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

/// The edited source, the significant indices the edit touches, those it removes or moves, and the
/// replaced byte interval.
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
    // An inserted or deleted token can change a neighbouring operator's arity and with it the
    // boundary a token further out.
    let touched = (left.saturating_sub(2)..=(right + 2).min(spans.len() - 1)).collect();
    let moved = match edit {
        Edit::Delete => vec![index],
        Edit::Swap => vec![left, right],
        Edit::Duplicate | Edit::Insert(_) => Vec::new(),
    };
    (edited, touched, moved, impact)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_seeds_are_inputs() {
        let seeds = edit_seeds("fn f() {}");
        let edits: Vec<_> = seeds
            .iter()
            .map(|seed| {
                let (edit, index, source) = edit_input(seed).expect("a seed is an input");
                assert_eq!((index, source), (1, "fn f() {}"));
                edit
            })
            .collect();
        assert!(matches!(
            edits[..],
            [Edit::Delete, Edit::Duplicate, Edit::Swap, Edit::Insert("(")]
        ));
        assert_eq!(edit_input(b"\x00\x01").map(|_| ()), None);
    }
}
