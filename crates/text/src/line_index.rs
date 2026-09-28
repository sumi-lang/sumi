//! Offset to line/column conversion for one source snapshot. Line terminators are `\n`, `\r\n`, and
//! lone `\r`, the lexer's set; a trailing one opens a final empty line.

use std::fmt;

use crate::{TextRange, TextSize};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Encoding {
    Utf8,
    Utf16,
}

/// Zero-based; the conversion's encoding defines `col`'s code units.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct LineCol {
    pub line: u32,
    pub col: u32,
}

#[derive(Clone, Debug)]
pub struct LineIndex<'a> {
    source: &'a str,
    line_starts: Box<[TextSize]>,
}

impl<'a> LineIndex<'a> {
    /// Panics unless `source.len()` fits in `u32`.
    pub fn new(source: &'a str) -> Self {
        u32::try_from(source.len()).expect("source length fits in u32");

        let bytes = source.as_bytes();
        let mut line_starts = vec![TextSize::new(0)];
        for (position, &byte) in bytes.iter().enumerate() {
            let ends_line = match byte {
                b'\n' => true,
                b'\r' => bytes.get(position + 1) != Some(&b'\n'),
                _ => false,
            };
            if ends_line {
                line_starts.push(TextSize::new(position as u32 + 1));
            }
        }

        Self {
            source,
            line_starts: line_starts.into_boxed_slice(),
        }
    }

    /// Clamps offsets in terminators to the content end; panics outside the source or inside a char.
    pub fn line_col(&self, offset: TextSize, encoding: Encoding) -> LineCol {
        assert!(
            offset.to_usize() <= self.source.len(),
            "offset past end of source"
        );
        assert!(
            self.source.is_char_boundary(offset.to_usize()),
            "offset inside a character"
        );
        let line = self
            .line_starts
            .partition_point(|&start| start <= offset)
            .saturating_sub(1);
        let start = self.line_starts[line].to_usize();
        let end = offset.to_usize().min(self.content_end(line));
        let col = match encoding {
            Encoding::Utf8 => end - start,
            Encoding::Utf16 => self.source[start..end].encode_utf16().count(),
        };
        LineCol {
            line: line as u32,
            col: col as u32,
        }
    }

    /// Returns `None` for missing lines or split characters; columns past content clamp to its end.
    pub fn offset(&self, at: LineCol, encoding: Encoding) -> Option<TextSize> {
        let start = self.line_starts.get(at.line as usize)?.to_usize();
        let end = self.content_end(at.line as usize);
        match encoding {
            Encoding::Utf8 => {
                let offset = start + (at.col as usize).min(end - start);
                self.source
                    .is_char_boundary(offset)
                    .then_some(TextSize::new(offset as u32))
            }
            Encoding::Utf16 => {
                let mut units = 0;
                for (byte, character) in self.source[start..end].char_indices() {
                    if units == at.col {
                        return Some(TextSize::new((start + byte) as u32));
                    }
                    units += character.len_utf16() as u32;
                    if units > at.col {
                        return None;
                    }
                }
                Some(TextSize::new(end as u32))
            }
        }
    }

    /// Displays one-based `line:column` in UTF-8 bytes, with `line_col`'s clamping and panics.
    pub fn display_offset(&self, offset: TextSize) -> impl fmt::Display {
        ShownPosition(self.line_col(offset, Encoding::Utf8))
    }

    /// Displays exclusive endpoints as `line:column..line:column`, or one position for an empty range.
    pub fn display_range(&self, range: TextRange) -> impl fmt::Display {
        ShownRange {
            start: ShownPosition(self.line_col(range.start(), Encoding::Utf8)),
            end: (range.start() != range.end())
                .then(|| ShownPosition(self.line_col(range.end(), Encoding::Utf8))),
        }
    }

    fn content_end(&self, line: usize) -> usize {
        let Some(next) = self.line_starts.get(line + 1) else {
            return self.source.len();
        };
        let mut end = next.to_usize() - 1;
        let bytes = self.source.as_bytes();
        if bytes[end] == b'\n' && end > 0 && bytes[end - 1] == b'\r' {
            end -= 1;
        }
        end
    }
}

struct ShownPosition(LineCol);

impl fmt::Display for ShownPosition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}:{}",
            u64::from(self.0.line) + 1,
            u64::from(self.0.col) + 1
        )
    }
}

struct ShownRange {
    start: ShownPosition,
    end: Option<ShownPosition>,
}

impl fmt::Display for ShownRange {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.start)?;
        if let Some(end) = &self.end {
            write!(f, "..{end}")?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn display_uses_one_based_byte_columns_and_exclusive_ends() {
        let index = LineIndex::new("a😀b\r\nΔ\rz\n");
        for (start, end, expected) in [
            (0, 0, "1:1"),
            (5, 6, "1:6..1:7"),
            (5, 10, "1:6..2:3"),
            (6, 7, "1:7..1:7"),
            (7, 8, "1:7..2:1"),
            (11, 12, "3:1..3:2"),
            (13, 13, "4:1"),
        ] {
            let range = TextRange::new(TextSize::new(start), TextSize::new(end));
            assert_eq!(index.display_range(range).to_string(), expected);
        }
        assert_eq!(index.display_offset(TextSize::new(5)).to_string(), "1:6");
        for (source, end, expected) in [("", 0, "1:1"), ("Δ", 2, "1:3")] {
            assert_eq!(
                LineIndex::new(source)
                    .display_offset(TextSize::new(end))
                    .to_string(),
                expected
            );
        }
        assert_eq!(
            ShownPosition(LineCol {
                line: u32::MAX,
                col: u32::MAX
            })
            .to_string(),
            "4294967296:4294967296"
        );
    }

    fn line_col(index: &LineIndex<'_>, offset: u32) -> (u32, u32) {
        let position = index.line_col(TextSize::new(offset), Encoding::Utf8);
        (position.line, position.col)
    }

    #[test]
    fn empty_source_has_one_empty_line() {
        let index = LineIndex::new("");
        for encoding in [Encoding::Utf8, Encoding::Utf16] {
            assert_eq!(
                index.line_col(TextSize::new(0), encoding),
                LineCol { line: 0, col: 0 }
            );
            assert_eq!(
                index.offset(
                    LineCol {
                        line: 0,
                        col: u32::MAX
                    },
                    encoding
                ),
                Some(TextSize::new(0))
            );
            assert_eq!(index.offset(LineCol { line: 1, col: 0 }, encoding), None);
        }
    }

    #[test]
    fn terminators_match_the_lexer() {
        let index = LineIndex::new("a\nbc\r\nd\re");
        let lines: Vec<u32> = (0..=9).map(|offset| line_col(&index, offset).0).collect();
        assert_eq!(lines, [0, 0, 1, 1, 1, 1, 2, 2, 3, 3]);
        assert_eq!(line_col(&index, 8), (3, 0));
    }

    #[test]
    fn a_trailing_terminator_opens_an_empty_final_line() {
        for (source, end) in [("a\n", 2), ("a\r\n", 3), ("a\r", 2)] {
            let index = LineIndex::new(source);
            let end = TextSize::new(end);
            for encoding in [Encoding::Utf8, Encoding::Utf16] {
                assert_eq!(index.line_col(end, encoding), LineCol { line: 1, col: 0 });
                for col in [0, u32::MAX] {
                    assert_eq!(index.offset(LineCol { line: 1, col }, encoding), Some(end));
                }
                assert_eq!(index.offset(LineCol { line: 2, col: 0 }, encoding), None);
            }
        }
    }

    #[test]
    fn columns_count_bytes_from_the_line_start() {
        let source = "let x = 1\nlet Δ = 2\n";
        let index = LineIndex::new(source);
        assert_eq!(line_col(&index, 4), (0, 4));
        assert_eq!(line_col(&index, 10), (1, 0));
        assert_eq!(line_col(&index, source.len() as u32 - 1), (1, 10));
    }

    #[test]
    fn encodings_count_code_units_and_reject_split_characters() {
        let index = LineIndex::new("a😀b\r\nΔ");
        for (encoding, columns) in [
            (Encoding::Utf8, &[0, 1, 5, 6][..]),
            (Encoding::Utf16, &[0, 1, 3, 4][..]),
        ] {
            for (&col, byte) in columns.iter().zip([0, 1, 5, 6]) {
                let at = LineCol { line: 0, col };
                assert_eq!(index.line_col(TextSize::new(byte), encoding), at);
                assert_eq!(index.offset(at, encoding), Some(TextSize::new(byte)));
            }
            assert_eq!(index.offset(LineCol { line: 0, col: 2 }, encoding), None);
            assert_eq!(
                index.line_col(TextSize::new(8), encoding),
                LineCol { line: 1, col: 0 }
            );
        }
        for col in [3, 4] {
            assert_eq!(index.offset(LineCol { line: 0, col }, Encoding::Utf8), None);
        }
        assert_eq!(
            index.offset(LineCol { line: 1, col: 1 }, Encoding::Utf8),
            None
        );
        assert_eq!(
            index.offset(LineCol { line: 1, col: 1 }, Encoding::Utf16),
            Some(TextSize::new(10))
        );
        assert_eq!(
            index.line_col(TextSize::new(10), Encoding::Utf8),
            LineCol { line: 1, col: 2 }
        );
        assert_eq!(
            index.line_col(TextSize::new(10), Encoding::Utf16),
            LineCol { line: 1, col: 1 }
        );
    }

    #[test]
    fn terminator_offsets_and_oversized_columns_clamp_to_content() {
        let index = LineIndex::new("\r\na😀\r\nb\rc\n");
        for encoding in [Encoding::Utf8, Encoding::Utf16] {
            for (line, end) in [0, 7, 10, 12, 13].into_iter().enumerate() {
                for col in [99, u32::MAX] {
                    assert_eq!(
                        index.offset(
                            LineCol {
                                line: line as u32,
                                col
                            },
                            encoding
                        ),
                        Some(TextSize::new(end))
                    );
                }
            }
            for line in [5, u32::MAX] {
                assert_eq!(index.offset(LineCol { line, col: 0 }, encoding), None);
            }
            let col = match encoding {
                Encoding::Utf8 => 5,
                Encoding::Utf16 => 3,
            };
            for byte in [7, 8] {
                assert_eq!(
                    index.line_col(TextSize::new(byte), encoding),
                    LineCol { line: 1, col }
                );
            }
            for byte in [0, 1] {
                assert_eq!(
                    index.line_col(TextSize::new(byte), encoding),
                    LineCol { line: 0, col: 0 }
                );
            }
            assert_eq!(
                index.line_col(TextSize::new(10), encoding),
                LineCol { line: 2, col: 1 }
            );
            assert_eq!(
                index.line_col(TextSize::new(12), encoding),
                LineCol { line: 3, col: 1 }
            );
            assert_eq!(
                index.line_col(TextSize::new(13), encoding),
                LineCol { line: 4, col: 0 }
            );
        }
    }

    #[test]
    #[should_panic(expected = "offset inside a character")]
    fn an_offset_inside_a_character_panics() {
        LineIndex::new("😀").line_col(TextSize::new(1), Encoding::Utf16);
    }

    #[test]
    #[should_panic(expected = "offset past end of source")]
    fn an_offset_past_the_source_panics() {
        LineIndex::new("ab").line_col(TextSize::new(3), Encoding::Utf8);
    }
}
