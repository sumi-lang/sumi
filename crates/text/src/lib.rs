/// A UTF-8 byte coordinate in a source file.
#[repr(transparent)]
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TextSize(u32);
impl TextSize {
    pub const fn new(value: u32) -> Self {
        Self(value)
    }

    pub const fn to_u32(&self) -> u32 {
        self.0
    }

    pub const fn to_usize(&self) -> usize {
        self.0 as usize
    }
}

/// A half-open range over UTF-8 bytes in a source file.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

    pub const fn is_empty(self) -> bool {
        self.start.to_u32() == self.end.to_u32()
    }

    pub fn text<'src>(&self, source: &'src str) -> &'src str {
        &source[self.start.0 as usize..self.end.0 as usize]
    }
}
