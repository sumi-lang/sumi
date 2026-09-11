use sumi_text::TextSize;

use crate::file::LexErrorKind;
use crate::generated::SyntaxKind;
use crate::token::{RawKind, RawToken, TokenFlags};

/// A string literal whose text the scan has left for the code of a hole.
/// The scan resumes its text at the `}` that closes the hole, or at the
/// line break that leaves it open.
struct Frame {
    /// The literal's `StringStart`, as its index among the tokens emitted.
    start: u32,
    /// The hole's `{`, likewise: where a hole left open is reported.
    hole: u32,
    /// Braces opened in the hole's code and not yet closed; the `}` at
    /// depth zero closes the hole.
    depth: u32,
}

/// A string literal whose text the scan is in between tokens: after a
/// hole's `}`, the next token is more of its text, its next hole's `{`, or
/// its end.
#[derive(Clone, Copy)]
struct Text {
    start: u32,
}

/// Where the text of a string literal stopped.
enum Stop {
    /// At a `{`, not consumed: a hole opens.
    Hole,
    /// At the closing quotes, consumed.
    Closer,
    /// At the line break or the end of input, not consumed: the literal is
    /// unterminated.
    End,
}

/// An error known only after its token was emitted: a hole left open at its
/// line break, or a literal with holes never closed, reported at its
/// opener as a whole literal is.
pub(crate) struct LateError {
    /// The token's index among those emitted.
    pub(crate) token: u32,
    /// How many of the token's leading bytes the error covers, or the
    /// whole token.
    pub(crate) prefix: Option<usize>,
    pub(crate) kind: LexErrorKind,
}

/// Identifiers are ASCII: a letter or `_`, then letters, digits, and `_`.
/// Any other character has no meaning in the language.
const fn is_ident_start(byte: u8) -> bool {
    byte == b'_' || byte.is_ascii_alphabetic()
}

const fn is_ident_continue(byte: u8) -> bool {
    byte == b'_' || byte.is_ascii_alphanumeric()
}

pub(crate) struct Lexer<'src> {
    source: &'src str,
    position: usize,
    /// The literals whose holes the scan is inside, innermost last.
    frames: Vec<Frame>,
    /// The literal whose text the next token continues, if any.
    text: Option<Text>,
    /// The tokens emitted so far: the index the next one takes.
    emitted: u32,
    late: Vec<LateError>,
}
impl<'src> Lexer<'src> {
    /// The caller must have validated that `source.len()` fits in `u32`.
    pub(crate) const fn new(source: &'src str) -> Self {
        Self {
            source,
            position: 0,
            frames: Vec::new(),
            text: None,
            emitted: 0,
            late: Vec::new(),
        }
    }

    /// The errors known only after their tokens were emitted, once the
    /// scan has reached the end of input.
    pub(crate) fn into_late_errors(self) -> Vec<LateError> {
        debug_assert_eq!(self.position, self.source.len());
        self.late
    }

    fn remaining(&self) -> &'src str {
        &self.source[self.position..]
    }

    fn peek_byte(&self) -> Option<u8> {
        self.source.as_bytes().get(self.position).copied()
    }

    fn peek_byte_at(&self, offset: usize) -> Option<u8> {
        self.source.as_bytes().get(self.position + offset).copied()
    }

    fn bump_ascii(&mut self) -> u8 {
        let byte = self.source.as_bytes()[self.position];
        debug_assert!(byte.is_ascii());
        self.position += 1;
        byte
    }

    fn bump_char(&mut self) -> char {
        let ch = self.remaining().chars().next().expect("cannot bump at EOF");
        self.position += ch.len_utf8();
        ch
    }

    fn scan_token(&mut self) -> RawToken {
        let start = self.position;

        // Inside a literal with holes — its text to resume, or a hole's code
        // — the literal owes tokens before any other; the check is two
        // loads, and the rest stays off the path every other token takes.
        let literal = if self.text.is_some() || !self.frames.is_empty() {
            self.scan_literal_token()
        } else {
            None
        };
        let (kind, raw, mut flags) = if let Some(token) = literal {
            token
        } else if self.position == 0 && self.remaining().starts_with('\u{feff}') {
            self.bump_char();
            // The BOM is ignorable trivia to every downstream phase; its
            // identity stays recoverable through the raw kind.
            (SyntaxKind::Whitespace, RawKind::Bom, TokenFlags::EMPTY)
        } else {
            match self.peek_byte().expect("scan_token called at EOF") {
                b' ' | b'\t' => {
                    self.scan_horizontal_space();
                    (
                        SyntaxKind::Whitespace,
                        RawKind::HorizontalSpace,
                        TokenFlags::EMPTY,
                    )
                }
                b'\n' | b'\r' => (SyntaxKind::Newline, RawKind::Newline, self.scan_newline()),
                b'/' if self.remaining().starts_with("//") => (
                    SyntaxKind::LineComment,
                    RawKind::LineComment,
                    self.scan_line_comment(),
                ),
                b'0'..=b'9' => (SyntaxKind::IntLiteral, RawKind::Number, self.scan_number()),
                b'"' => self.scan_string(),
                byte if is_ident_start(byte) => {
                    self.scan_ident();
                    (
                        self.classify_ident(start),
                        RawKind::Ident,
                        TokenFlags::EMPTY,
                    )
                }
                byte if byte.is_ascii_punctuation() => {
                    self.bump_ascii();
                    let kind = SyntaxKind::from_punct(byte).unwrap_or(SyntaxKind::Error);
                    (kind, RawKind::Punct, TokenFlags::EMPTY)
                }
                _ => {
                    self.bump_char();
                    (SyntaxKind::Error, RawKind::Unknown, TokenFlags::EMPTY)
                }
            }
        };

        let len = self.position - start;
        debug_assert!(len > 0, "scan_token must always make progress");

        if !self.frames.is_empty() {
            flags |= TokenFlags::HOLE_AFTER;
        }
        RawToken {
            kind,
            raw,
            len: TextSize::new(u32::try_from(len).expect("source length fits in u32")),
            flags,
        }
    }

    fn scan_horizontal_space(&mut self) {
        while matches!(self.peek_byte(), Some(b' ' | b'\t')) {
            self.position += 1;
        }
    }

    fn scan_newline(&mut self) -> TokenFlags {
        match self.bump_ascii() {
            b'\n' => TokenFlags::EMPTY,
            b'\r' if self.peek_byte() == Some(b'\n') => {
                self.bump_ascii();
                TokenFlags::EMPTY
            }
            b'\r' => TokenFlags::LONE_CR,
            _ => unreachable!("scan_newline called off a newline byte"),
        }
    }

    fn scan_line_comment(&mut self) -> TokenFlags {
        self.bump_ascii();
        self.bump_ascii();

        let flags = match (self.peek_byte(), self.peek_byte_at(1)) {
            // `///` is an outer doc comment, but `////...` is decoration.
            (Some(b'/'), next) if next != Some(b'/') => TokenFlags::DOC_OUTER,
            (Some(b'!'), _) => TokenFlags::DOC_INNER,
            _ => TokenFlags::EMPTY,
        };

        let rest = self.remaining();
        let line_end = rest.find(['\n', '\r']).unwrap_or(rest.len());
        self.position += line_end;

        flags
    }

    /// Scan an integer literal: a run of digits, with any identifier
    /// characters after it attached as a suffix. The scan also decides
    /// whether the token breaks a literal rule, so canonical numbers — the
    /// overwhelming majority — never get re-scanned by the collector.
    fn scan_number(&mut self) -> TokenFlags {
        let start = self.position;
        let first = self.bump_ascii();
        debug_assert!(first.is_ascii_digit());

        while self.peek_byte().is_some_and(|byte| byte.is_ascii_digit()) {
            self.position += 1;
        }

        // A leading zero is a literal error: `0123` means octal in several
        // other languages.
        let mut malformed = first == b'0' && self.position > start + 1;

        // Trailing identifier characters attach as a literal suffix (`1u32`,
        // `1_000`, `1e5`) for the collector to reject: a `.` never joins,
        // so `1.5` is three tokens.
        let suffix_start = self.position;
        self.eat_ident_continue();
        malformed |= self.position > suffix_start;

        if malformed {
            TokenFlags::MALFORMED_NUMBER
        } else {
            TokenFlags::EMPTY
        }
    }

    /// The token a string literal with holes owes before any other: inside
    /// a hole, the braces, the line break, and the quotes belong to the
    /// literal around the hole; between a hole and the next, its text.
    #[inline(never)]
    fn scan_literal_token(&mut self) -> Option<(SyntaxKind, RawKind, TokenFlags)> {
        if let Some(text) = self.text.take()
            && let Some(token) = self.scan_text_token(text)
        {
            return Some(token);
        }
        let frame = self.frames.last_mut()?;
        match self.source.as_bytes().get(self.position)? {
            b'{' => {
                frame.depth += 1;
                self.position += 1;
                Some((SyntaxKind::LBrace, RawKind::Punct, TokenFlags::EMPTY))
            }
            b'}' if frame.depth > 0 => {
                frame.depth -= 1;
                self.position += 1;
                Some((SyntaxKind::RBrace, RawKind::Punct, TokenFlags::EMPTY))
            }
            b'}' => {
                let frame = self.frames.pop().expect("a frame is open");
                self.text = Some(Text { start: frame.start });
                self.position += 1;
                Some((SyntaxKind::HoleClose, RawKind::Punct, TokenFlags::EMPTY))
            }
            // A hole ends with its line, and so do the literals around it;
            // the break lexes as usual.
            b'\n' | b'\r' => {
                self.leave_holes();
                None
            }
            b'"' => Some(self.scan_quote_in_hole()),
            _ => None,
        }
    }

    /// Leave every hole the scan is inside, each reported at its `{`. The
    /// literals around them end with the line.
    fn leave_holes(&mut self) {
        while let Some(frame) = self.frames.pop() {
            self.late.push(LateError {
                token: frame.hole,
                prefix: Some(1),
                kind: LexErrorKind::UnclosedHole,
            });
        }
    }

    /// Leave the holes and the literal text the scan is inside at the end
    /// of input: every hole is left open, and a literal between holes is
    /// unterminated.
    fn finish(&mut self) {
        self.leave_holes();
        if let Some(text) = self.text.take() {
            self.late.push(unterminated(text));
        }
    }

    /// A quote inside a hole: a literal of the hole's code, or the end of
    /// the literal around the hole. A literal inside the hole that its line
    /// never closes is the outer literal's closer instead, which leaves the
    /// hole open.
    fn scan_quote_in_hole(&mut self) -> (SyntaxKind, RawKind, TokenFlags) {
        let quote = self.position;
        self.position += 1;
        let (stop, flags) = self.scan_string_text();
        match stop {
            Stop::Closer => (SyntaxKind::StringLiteral, RawKind::String, flags),
            Stop::Hole => {
                self.text = Some(Text {
                    start: self.emitted,
                });
                (SyntaxKind::StringStart, RawKind::String, flags)
            }
            Stop::End => {
                self.position = quote + 1;
                self.leave_hole_at_closer();
                (SyntaxKind::StringEnd, RawKind::String, TokenFlags::EMPTY)
            }
        }
    }

    /// Leave the innermost hole at its literal's closer, which leaves the
    /// hole open.
    fn leave_hole_at_closer(&mut self) {
        let frame = self.frames.pop().expect("a frame is open");
        self.late.push(LateError {
            token: frame.hole,
            prefix: Some(1),
            kind: LexErrorKind::UnclosedHole,
        });
    }

    /// Scan a `"…"` literal from its opener: whole, when it has no hole,
    /// and otherwise up to its first `{`, as its start, with its text to
    /// resume after the hole. Every literal is bounded by its line, so a
    /// stray quote costs its line and never the file.
    fn scan_string(&mut self) -> (SyntaxKind, RawKind, TokenFlags) {
        self.position += 1;
        let (stop, flags) = self.scan_string_text();
        match stop {
            Stop::Closer => (SyntaxKind::StringLiteral, RawKind::String, flags),
            Stop::End => (
                SyntaxKind::StringLiteral,
                RawKind::String,
                flags | TokenFlags::UNTERMINATED,
            ),
            Stop::Hole => {
                self.text = Some(Text {
                    start: self.emitted,
                });
                (SyntaxKind::StringStart, RawKind::String, flags)
            }
        }
    }

    /// The next token of a literal's text after a hole: the next hole's
    /// `{`, more text up to one, or the text through the closer. `None` at
    /// the line break, or the end of input, that leaves the literal
    /// unterminated with no text to take: the literal is reported and the
    /// break lexes as usual.
    fn scan_text_token(&mut self, text: Text) -> Option<(SyntaxKind, RawKind, TokenFlags)> {
        if self.peek_byte() == Some(b'{') {
            self.position += 1;
            self.frames.push(Frame {
                start: text.start,
                hole: self.emitted,
                depth: 0,
            });
            return Some((SyntaxKind::HoleOpen, RawKind::Punct, TokenFlags::EMPTY));
        }
        let start = self.position;
        let (stop, flags) = self.scan_string_text();
        match stop {
            Stop::Hole => {
                self.text = Some(text);
                Some((SyntaxKind::StringMiddle, RawKind::String, flags))
            }
            Stop::Closer => Some((SyntaxKind::StringEnd, RawKind::String, flags)),
            Stop::End => {
                self.late.push(unterminated(text));
                (self.position > start).then_some((
                    SyntaxKind::StringEnd,
                    RawKind::String,
                    flags | TokenFlags::UNTERMINATED,
                ))
            }
        }
    }

    /// Scan the text of a literal from the current position to its first
    /// unescaped `{`, its closer, or its end: the line break or the end of
    /// input. A `\` protects the byte after it, so an escaped quote never
    /// closes and an escaped brace opens nothing.
    fn scan_string_text(&mut self) -> (Stop, TokenFlags) {
        let mut flags = TokenFlags::EMPTY;
        loop {
            match self.peek_byte() {
                None | Some(b'\n' | b'\r') => return (Stop::End, flags),
                Some(b'"') => {
                    self.position += 1;
                    return (Stop::Closer, flags);
                }
                Some(b'{') => return (Stop::Hole, flags),
                Some(b'\\') => {
                    flags |= TokenFlags::HAS_ESCAPE;
                    self.bump_ascii();
                    // A backslash before the line break protects nothing:
                    // the break ends the literal.
                    if !matches!(self.peek_byte(), None | Some(b'\n' | b'\r')) {
                        self.bump_char();
                    }
                }
                // Only ASCII delimiters are inspected, so a byte-wise skip
                // cannot leave the final position mid-character.
                Some(_) => self.position += 1,
            }
        }
    }

    fn scan_ident(&mut self) {
        self.bump_ascii();
        self.eat_ident_continue();
    }

    /// Classify the identifier just scanned from `start`, while its bytes
    /// are still cache-hot: a reserved word — `_` included — or a plain
    /// identifier.
    fn classify_ident(&self, start: usize) -> SyntaxKind {
        SyntaxKind::from_keyword(&self.source[start..self.position]).unwrap_or(SyntaxKind::Ident)
    }

    fn eat_ident_continue(&mut self) {
        while self.peek_byte().is_some_and(is_ident_continue) {
            self.position += 1;
        }
    }
}

/// The error for a literal with holes that its text never closes,
/// reported at its opener as a whole literal is.
fn unterminated(text: Text) -> LateError {
    LateError {
        token: text.start,
        prefix: None,
        kind: LexErrorKind::UnterminatedString,
    }
}

impl Iterator for Lexer<'_> {
    type Item = RawToken;

    /// `Some` always consumes at least one byte; `None` means the cursor
    /// reached `source.len()`. Malformed input never ends iteration early.
    fn next(&mut self) -> Option<Self::Item> {
        if self.position == self.source.len() {
            self.finish();
            return None;
        }

        let start = self.position;
        let token = self.scan_token();
        self.emitted += 1;

        debug_assert!(self.position > start);
        debug_assert!(self.position <= self.source.len());

        Some(token)
    }
}
