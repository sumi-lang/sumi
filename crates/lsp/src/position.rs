use lsp_types::{Position, Range};
use sumi_text::{TextRange, TextSize};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Encoding {
    Utf8,
    Utf16,
}

pub(crate) struct Positions<'a> {
    source: &'a str,
    lines: Vec<(usize, usize)>,
    encoding: Encoding,
}

impl<'a> Positions<'a> {
    pub(crate) fn new(source: &'a str, encoding: Encoding) -> Self {
        let bytes = source.as_bytes();
        let mut lines = Vec::new();
        let mut start = 0;
        let mut cursor = 0;
        while cursor < bytes.len() {
            match bytes[cursor] {
                b'\n' => {
                    lines.push((start, cursor));
                    cursor += 1;
                    start = cursor;
                }
                b'\r' => {
                    lines.push((start, cursor));
                    cursor += usize::from(bytes.get(cursor + 1) == Some(&b'\n')) + 1;
                    start = cursor;
                }
                _ => cursor += 1,
            }
        }
        lines.push((start, source.len()));
        Self {
            source,
            lines,
            encoding,
        }
    }

    pub(crate) fn offset(&self, position: Position) -> Option<usize> {
        let &(start, end) = self.lines.get(position.line as usize)?;
        let line = &self.source[start..end];
        let mut units = 0u32;
        for (byte, character) in line.char_indices() {
            if units == position.character {
                return Some(start + byte);
            }
            units += match self.encoding {
                Encoding::Utf8 => character.len_utf8() as u32,
                Encoding::Utf16 => character.len_utf16() as u32,
            };
            if units > position.character {
                return None;
            }
        }
        Some(end)
    }

    pub(crate) fn position(&self, offset: TextSize) -> Position {
        let offset = offset.to_usize();
        assert!(offset <= self.source.len() && self.source.is_char_boundary(offset));
        let line = self
            .lines
            .partition_point(|&(start, _)| start <= offset)
            .saturating_sub(1);
        let (start, end) = self.lines[line];
        let content_offset = offset.min(end);
        let text = &self.source[start..content_offset];
        let character = match self.encoding {
            Encoding::Utf8 => text.len() as u32,
            Encoding::Utf16 => text.encode_utf16().count() as u32,
        };
        Position::new(line as u32, character)
    }

    pub(crate) fn range(&self, range: TextRange) -> Range {
        Range::new(self.position(range.start()), self.position(range.end()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn utf16_positions_respect_non_bmp_characters_and_crlf() {
        let source = "a😀b\r\nΔ";
        let positions = Positions::new(source, Encoding::Utf16);
        assert_eq!(positions.offset(Position::new(0, 1)), Some(1));
        assert_eq!(positions.offset(Position::new(0, 3)), Some(5));
        assert_eq!(positions.offset(Position::new(0, 2)), None);
        assert_eq!(positions.offset(Position::new(1, 1)), Some(source.len()));
        assert_eq!(positions.position(TextSize::new(5)), Position::new(0, 3));
        assert_eq!(positions.position(TextSize::new(8)), Position::new(1, 0));
    }

    #[test]
    fn utf8_positions_count_bytes() {
        let positions = Positions::new("😀x", Encoding::Utf8);
        assert_eq!(positions.offset(Position::new(0, 4)), Some(4));
        assert_eq!(positions.offset(Position::new(0, 1)), None);
        assert_eq!(positions.position(TextSize::new(4)), Position::new(0, 4));
    }

    #[test]
    fn positions_past_a_line_clamp_to_its_end() {
        for encoding in [Encoding::Utf8, Encoding::Utf16] {
            let positions = Positions::new("\r\na😀\r\n", encoding);
            assert_eq!(positions.offset(Position::new(0, 99)), Some(0));
            assert_eq!(positions.offset(Position::new(1, 99)), Some(7));
            assert_eq!(positions.offset(Position::new(2, 99)), Some(9));
        }
    }
}
