//! Offset ↔ line/column conversion for one source snapshot.
//!
//! A [`LineIndex`] stores where each line starts, plus one bit per line
//! recording whether the line contains a non-ASCII byte. Byte columns
//! convert by arithmetic alone; UTF-16 columns — the editor-protocol
//! convention — convert by arithmetic on ASCII lines and walk the line's
//! characters only where the bit is set, so the index never stores a copy
//! of the text. Line terminators are `\n`, `\r\n`, and lone `\r`, matching
//! the lexer, and a terminator ends its line, so a source ending in one has
//! a final empty line.

use crate::TextSize;

/// A zero-based line and column; the column counts UTF-8 bytes from the
/// line start.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct LineCol {
    pub line: u32,
    pub col: u32,
}

/// A zero-based line and column; the column counts UTF-16 code units, as
/// editor protocols do. Kept a distinct type from [`LineCol`] so the two
/// column units cannot be confused.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Utf16LineCol {
    pub line: u32,
    pub col: u32,
}

/// The line-start table for one source snapshot.
///
/// The index does not retain the source text; the UTF-16 conversions take
/// it back in, and it must be the string the index was built from.
#[derive(Clone, Debug)]
pub struct LineIndex {
    /// Byte offset of each line start; line 0 starts at zero, so the table
    /// is never empty and is strictly increasing.
    line_starts: Box<[TextSize]>,
    /// One bit per line: set when the line holds at least one non-ASCII
    /// byte, so only such lines pay for character walking.
    non_ascii: Box<[u64]>,
    source_len: TextSize,
}

impl LineIndex {
    /// Build the index for `source`. The caller must have validated that
    /// `source.len()` fits in `u32`, as the lexer's entry point does.
    pub fn new(source: &str) -> Self {
        let source_len = u32::try_from(source.len()).expect("source length fits in u32");

        let bytes = source.as_bytes();
        let mut line_starts = vec![TextSize::new(0)];
        let mut non_ascii = vec![0u64; 1];
        let mut line = 0usize;
        for (position, &byte) in bytes.iter().enumerate() {
            if !byte.is_ascii() {
                non_ascii[line / 64] |= 1 << (line % 64);
            }
            let ends_line = match byte {
                b'\n' => true,
                b'\r' => bytes.get(position + 1) != Some(&b'\n'),
                _ => false,
            };
            if ends_line {
                line_starts.push(TextSize::new(position as u32 + 1));
                line += 1;
                if line / 64 == non_ascii.len() {
                    non_ascii.push(0);
                }
            }
        }

        Self {
            line_starts: line_starts.into_boxed_slice(),
            non_ascii: non_ascii.into_boxed_slice(),
            source_len: TextSize::new(source_len),
        }
    }

    /// The number of lines; at least one, even for an empty source.
    pub fn line_count(&self) -> u32 {
        self.line_starts.len() as u32
    }

    /// The line and byte column of `offset`, which must not exceed the
    /// source length. The end of the source belongs to the last line.
    pub fn line_col(&self, offset: TextSize) -> LineCol {
        assert!(offset <= self.source_len, "offset past end of source");
        let line = self
            .line_starts
            .partition_point(|&start| start <= offset)
            .saturating_sub(1);
        LineCol {
            line: line as u32,
            col: offset.to_u32() - self.line_starts[line].to_u32(),
        }
    }

    /// The offset of `position`, or `None` when the line does not exist or
    /// the column runs past the line's bytes (terminator included).
    pub fn offset(&self, position: LineCol) -> Option<TextSize> {
        let start = self.line_starts.get(position.line as usize)?.to_u32();
        let offset = start.checked_add(position.col)?;
        (offset <= self.line_end(position.line).to_u32()).then_some(TextSize::new(offset))
    }

    /// The line and UTF-16 column of `offset`, which must lie on a character
    /// boundary of `source` — the string this index was built from.
    pub fn utf16_line_col(&self, source: &str, offset: TextSize) -> Utf16LineCol {
        let LineCol { line, col } = self.line_col(offset);
        let col = if self.is_ascii_line(line) {
            col
        } else {
            let start = self.line_starts[line as usize].to_usize();
            source[start..offset.to_usize()]
                .chars()
                .map(|ch| ch.len_utf16() as u32)
                .sum()
        };
        Utf16LineCol { line, col }
    }

    /// The offset of `position`, or `None` when the line does not exist or
    /// the column runs past the line's end or splits a surrogate pair.
    /// `source` must be the string this index was built from.
    pub fn utf16_offset(&self, source: &str, position: Utf16LineCol) -> Option<TextSize> {
        if self.is_ascii_line(position.line) {
            return self.offset(LineCol {
                line: position.line,
                col: position.col,
            });
        }
        let start = self.line_starts.get(position.line as usize)?.to_usize();
        let end = self.line_end(position.line).to_usize();
        let mut units = 0u32;
        for (index, ch) in source[start..end].char_indices() {
            if units == position.col {
                return Some(TextSize::new((start + index) as u32));
            }
            units += ch.len_utf16() as u32;
            if units > position.col {
                return None;
            }
        }
        (units == position.col).then_some(TextSize::new(end as u32))
    }

    /// Where line `line` ends: the next line's start, or the end of the
    /// source for the last line. `line` must exist and is not checked here.
    fn line_end(&self, line: u32) -> TextSize {
        self.line_starts
            .get(line as usize + 1)
            .copied()
            .unwrap_or(self.source_len)
    }

    /// Whether the line exists and holds only ASCII bytes, so its UTF-16
    /// columns equal its byte columns. A line past the table is vacuously
    /// ASCII; lookups on it fail on the line-start table instead.
    fn is_ascii_line(&self, line: u32) -> bool {
        let line = line as usize;
        self.non_ascii
            .get(line / 64)
            .is_none_or(|&word| word & (1 << (line % 64)) == 0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn index(source: &str) -> LineIndex {
        LineIndex::new(source)
    }

    #[test]
    fn empty_source_has_one_empty_line() {
        let index = index("");
        assert_eq!(index.line_count(), 1);
        assert_eq!(
            index.line_col(TextSize::new(0)),
            LineCol { line: 0, col: 0 }
        );
        assert_eq!(
            index.offset(LineCol { line: 0, col: 0 }),
            Some(TextSize::new(0))
        );
    }

    #[test]
    fn terminators_match_the_lexer() {
        // "a\n" | "bc\r\n" | "d\r" | "e"
        let index = index("a\nbc\r\nd\re");
        assert_eq!(index.line_count(), 4);
        let lines: Vec<u32> = (0..=9)
            .map(|offset| index.line_col(TextSize::new(offset)).line)
            .collect();
        assert_eq!(lines, [0, 0, 1, 1, 1, 1, 2, 2, 3, 3]);
        assert_eq!(
            index.line_col(TextSize::new(8)),
            LineCol { line: 3, col: 0 }
        );
    }

    #[test]
    fn a_trailing_terminator_opens_an_empty_final_line() {
        let index = index("a\n");
        assert_eq!(index.line_count(), 2);
        assert_eq!(
            index.line_col(TextSize::new(2)),
            LineCol { line: 1, col: 0 }
        );
    }

    #[test]
    fn offsets_round_trip_through_line_col() {
        let source = "let x = 1\nlet y = 2\n";
        let index = index(source);
        for offset in 0..=source.len() as u32 {
            let offset = TextSize::new(offset);
            assert_eq!(index.offset(index.line_col(offset)), Some(offset));
        }
    }

    #[test]
    fn out_of_range_positions_are_rejected() {
        let index = index("ab\ncd");
        assert_eq!(index.offset(LineCol { line: 2, col: 0 }), None);
        assert_eq!(index.offset(LineCol { line: 0, col: 4 }), None);
        assert_eq!(index.offset(LineCol { line: 1, col: 3 }), None);
    }

    #[test]
    #[should_panic(expected = "offset past end of source")]
    fn an_offset_past_the_source_panics() {
        index("ab").line_col(TextSize::new(3));
    }

    #[test]
    fn ascii_lines_convert_utf16_columns_by_arithmetic() {
        let source = "ascii only\nΔx = 1\n";
        let index = index(source);
        let offset = TextSize::new(6);
        assert_eq!(
            index.utf16_line_col(source, offset),
            Utf16LineCol { line: 0, col: 6 }
        );
        assert_eq!(
            index.utf16_offset(source, Utf16LineCol { line: 0, col: 6 }),
            Some(offset)
        );
    }

    #[test]
    fn wide_lines_count_utf16_units() {
        // "😀" is one supplementary character: four UTF-8 bytes, two UTF-16
        // units. "Δ" is two UTF-8 bytes, one UTF-16 unit.
        let source = "😀Δx\n";
        let index = index(source);
        let after_emoji = TextSize::new(4);
        let after_delta = TextSize::new(6);
        assert_eq!(
            index.utf16_line_col(source, after_emoji),
            Utf16LineCol { line: 0, col: 2 }
        );
        assert_eq!(
            index.utf16_line_col(source, after_delta),
            Utf16LineCol { line: 0, col: 3 }
        );
        assert_eq!(
            index.utf16_offset(source, Utf16LineCol { line: 0, col: 2 }),
            Some(after_emoji)
        );
        assert_eq!(
            index.utf16_offset(source, Utf16LineCol { line: 0, col: 3 }),
            Some(after_delta)
        );
    }

    #[test]
    fn a_column_inside_a_surrogate_pair_is_rejected() {
        let source = "😀x";
        let index = index(source);
        assert_eq!(
            index.utf16_offset(source, Utf16LineCol { line: 0, col: 1 }),
            None
        );
    }

    #[test]
    fn utf16_positions_round_trip_on_wide_lines() {
        let source = "let Δ = \"😀\"\nplain\n";
        let index = index(source);
        for offset in 0..=source.len() as u32 {
            let offset = TextSize::new(offset);
            if !source.is_char_boundary(offset.to_usize()) {
                continue;
            }
            let position = index.utf16_line_col(source, offset);
            assert_eq!(index.utf16_offset(source, position), Some(offset));
        }
    }

    #[test]
    fn the_non_ascii_bit_spans_many_lines() {
        // Force the bitset past one 64-bit word: 70 lines alternating ASCII
        // and non-ASCII, each with two bytes of content.
        let source: String = (0..70)
            .map(|i| if i % 2 == 0 { "ok\n" } else { "Δ\n" })
            .collect();
        let index = index(&source);
        for line in 0..70u32 {
            let start = index.offset(LineCol { line, col: 0 }).unwrap();
            let end = TextSize::new(start.to_u32() + 2);
            let col = if line % 2 == 0 { 2 } else { 1 };
            assert_eq!(
                index.utf16_line_col(&source, end),
                Utf16LineCol { line, col },
                "line {line}"
            );
        }
    }
}
