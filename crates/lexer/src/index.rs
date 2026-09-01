use std::ops::{Add, AddAssign, Sub};

/// The index of a token in a [`LexedFile`](crate::LexedFile): a position in
/// the raw token buffer, trivia included.
///
/// The parser's significant index and the tree's node index are other
/// spaces with other types, so an index is never applied to the wrong
/// buffer. Ranges of raw tokens are half-open, and the index one past the
/// last token — [`LexedFile::end`](crate::LexedFile::end) — is where a range
/// running to the end of the file stops.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RawIdx(u32);

impl RawIdx {
    pub const fn new(index: u32) -> Self {
        Self(index)
    }

    pub const fn to_u32(self) -> u32 {
        self.0
    }

    pub const fn to_usize(self) -> usize {
        self.0 as usize
    }

    /// The index `count` tokens back, if there is one.
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

impl Add<u32> for RawIdx {
    type Output = Self;

    fn add(self, count: u32) -> Self {
        Self(self.0 + count)
    }
}

impl AddAssign<u32> for RawIdx {
    fn add_assign(&mut self, count: u32) {
        self.0 += count;
    }
}

impl Sub<u32> for RawIdx {
    type Output = Self;

    fn sub(self, count: u32) -> Self {
        Self(self.0 - count)
    }
}
