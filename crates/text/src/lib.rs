mod line_index;

pub use line_index::{LineCol, LineIndex, Utf16LineCol};

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

/// A file in a compilation, allocated by whatever owns the set of files —
/// a driver or a language server — and carried by every span and every
/// diagnostic label, so a diagnostic can point into a file other than the
/// one it was produced from. A single-file producer is handed one.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FileId(u32);

impl FileId {
    pub const fn new(value: u32) -> Self {
        Self(value)
    }

    pub const fn to_u32(self) -> u32 {
        self.0
    }
}

/// A byte range in one file.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Span {
    file: FileId,
    range: TextRange,
}

impl Span {
    pub const fn new(file: FileId, range: TextRange) -> Self {
        Self { file, range }
    }

    pub const fn file(self) -> FileId {
        self.file
    }

    pub const fn range(self) -> TextRange {
        self.range
    }
}

/// One replacement of a byte range in a source snapshot.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TextEdit {
    range: TextRange,
    replacement: Box<str>,
}

impl TextEdit {
    pub fn new(range: TextRange, replacement: impl Into<Box<str>>) -> Self {
        Self {
            range,
            replacement: replacement.into(),
        }
    }

    pub const fn range(&self) -> TextRange {
        self.range
    }

    pub fn replacement(&self) -> &str {
        &self.replacement
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

    #[test]
    fn text_edits_retain_their_range_and_replacement() {
        let point = TextSize::new(6);
        let edit = TextEdit::new(TextRange::new(point, point), ")");

        assert_eq!(edit.range(), TextRange::new(point, point));
        assert_eq!(edit.replacement(), ")");
    }
}
