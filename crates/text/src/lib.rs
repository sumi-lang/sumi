/// A file-local UTF-8 byte offset or length.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TextSize(u32);
impl TextSize {
    pub const fn new(value: u32) -> Self {
        Self(value)
    }

    pub const fn to_u32(self) -> u32 {
        self.0
    }

    pub const fn to_usize(self) -> usize {
        self.0 as usize
    }
}

/// A half-open `[start, end)` range over UTF-8 bytes in a source file.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct TextRange {
    start: TextSize,
    end: TextSize,
}
impl TextRange {
    pub const fn new(start: TextSize, end: TextSize) -> Self {
        assert!(start.to_u32() <= end.to_u32());

        Self { start, end }
    }

    pub const fn start(self) -> TextSize {
        self.start
    }
    pub const fn end(self) -> TextSize {
        self.end
    }

    pub fn text(self, source: &str) -> &str {
        &source[self.start.to_usize()..self.end.to_usize()]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn range_slices_source() {
        let range = TextRange::new(TextSize::new(3), TextSize::new(6));
        assert_eq!(range.text("fn map"), "map");
    }
}
