//! Offset to line/column conversion for one source snapshot. Line terminators are `\n`, `\r\n`, and
//! lone `\r`, the lexer's set; a trailing one opens a final empty line.

use crate::TextSize;

/// Zero-based; `col` counts UTF-8 bytes from the line start.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct LineCol {
    pub line: u32,
    pub col: u32,
}

#[derive(Clone, Debug)]
pub struct LineIndex {
    line_starts: Box<[TextSize]>,
    source_len: TextSize,
}

impl LineIndex {
    /// Panics unless `source.len()` fits in `u32`.
    pub fn new(source: &str) -> Self {
        let source_len = u32::try_from(source.len()).expect("source length fits in u32");

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
            line_starts: line_starts.into_boxed_slice(),
            source_len: TextSize::new(source_len),
        }
    }

    /// Panics if `offset` exceeds the source length.
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
}

#[cfg(test)]
mod tests {
    use super::*;

    fn line_col(index: &LineIndex, offset: u32) -> (u32, u32) {
        let position = index.line_col(TextSize::new(offset));
        (position.line, position.col)
    }

    #[test]
    fn empty_source_has_one_empty_line() {
        assert_eq!(line_col(&LineIndex::new(""), 0), (0, 0));
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
        assert_eq!(line_col(&LineIndex::new("a\n"), 2), (1, 0));
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
    #[should_panic(expected = "offset past end of source")]
    fn an_offset_past_the_source_panics() {
        LineIndex::new("ab").line_col(TextSize::new(3));
    }
}
