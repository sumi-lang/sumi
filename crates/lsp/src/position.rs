use lsp_types::{Position, Range};
use sumi_text::{Encoding, LineCol, LineIndex, TextRange, TextSize};

pub(crate) struct Positions<'a> {
    index: LineIndex<'a>,
    encoding: Encoding,
}

impl<'a> Positions<'a> {
    pub(crate) fn new(source: &'a str, encoding: Encoding) -> Self {
        Self {
            index: LineIndex::new(source),
            encoding,
        }
    }

    pub(crate) fn offset(&self, position: Position) -> Option<usize> {
        self.index
            .offset(
                LineCol {
                    line: position.line,
                    col: position.character,
                },
                self.encoding,
            )
            .map(TextSize::to_usize)
    }

    pub(crate) fn position(&self, offset: TextSize) -> Position {
        let at = self.index.line_col(offset, self.encoding);
        Position::new(at.line, at.col)
    }

    pub(crate) fn range(&self, range: TextRange) -> Range {
        Range::new(self.position(range.start()), self.position(range.end()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn adapter_converts_positions_and_ranges() {
        for (encoding, col) in [(Encoding::Utf8, 5), (Encoding::Utf16, 3)] {
            let positions = Positions::new("a😀\r\nΔ", encoding);
            assert_eq!(positions.offset(Position::new(0, col)), Some(5));
            assert_eq!(
                positions.range(TextRange::new(TextSize::new(5), TextSize::new(7))),
                Range::new(Position::new(0, col), Position::new(1, 0)),
            );
        }
    }
}
