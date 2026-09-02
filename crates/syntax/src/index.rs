//! The parser's index spaces, kept apart by type: a significant position in
//! a [`ParserInput`](crate::ParserInput), and a node in a
//! [`SyntaxTree`](crate::SyntaxTree). The lexer's raw token index is the
//! third, [`RawIdx`](sumi_lexer::RawIdx), which both of these project into.

use std::ops::{Add, AddAssign, Sub};

macro_rules! index {
    ($(#[$doc:meta])* $name:ident) => {
        $(#[$doc])*
        #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
        pub struct $name(u32);

        impl $name {
            pub const fn new(index: u32) -> Self {
                Self(index)
            }

            pub const fn to_u32(self) -> u32 {
                self.0
            }

            pub const fn to_usize(self) -> usize {
                self.0 as usize
            }

            /// The index `count` further on, if it exists.
            pub fn checked_add(self, count: u32) -> Option<Self> {
                self.0.checked_add(count).map(Self)
            }

            /// The index `count` back, if there is one.
            pub fn checked_sub(self, count: u32) -> Option<Self> {
                self.0.checked_sub(count).map(Self)
            }

            /// The indices from this one up to, not including, `end`.
            pub fn until(
                self,
                end: Self,
            ) -> impl DoubleEndedIterator<Item = Self> + ExactSizeIterator + Clone {
                (self.0..end.0).map(Self)
            }
        }

        impl Add<u32> for $name {
            type Output = Self;

            fn add(self, count: u32) -> Self {
                Self(self.0 + count)
            }
        }

        impl AddAssign<u32> for $name {
            fn add_assign(&mut self, count: u32) {
                self.0 += count;
            }
        }

        impl Sub<u32> for $name {
            type Output = Self;

            fn sub(self, count: u32) -> Self {
                Self(self.0 - count)
            }
        }
    };
}

index! {
    /// The index of a significant token in a [`ParserInput`](crate::ParserInput):
    /// the parser's cursor space, trivia stripped. Every significant index
    /// maps to the raw index of its token; the reverse needs a search.
    SigIdx
}

index! {
    /// The index of a node in a [`SyntaxTree`](crate::SyntaxTree): its
    /// position in postorder, so a node's index is larger than every node
    /// in its subtree, and the root's is the largest.
    NodeIdx
}
