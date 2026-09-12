use sumi_text::TextSize;

use crate::generated::SyntaxKind;
use crate::token::{RawKind, RawToken, TokenFlags};

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
}
impl<'src> Lexer<'src> {
    /// The caller must have validated that `source.len()` fits in `u32`.
    pub(crate) const fn new(source: &'src str) -> Self {
        Self {
            source,
            position: 0,
        }
    }

    fn remaining(&self) -> &'src str {
        &self.source[self.position..]
    }

    fn peek_byte(&self) -> Option<u8> {
        self.source.as_bytes().get(self.position).copied()
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

        let (kind, raw, flags) = {
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
        let rest = self.remaining();
        let line_end = rest.find(['\n', '\r']).unwrap_or(rest.len());
        self.position += line_end;
        TokenFlags::EMPTY
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

    /// Scan a `"…"` literal from its opener to its closer, or to its end:
    /// the line break or the end of input, which leaves it unterminated.
    /// Every literal is bounded by its line, so a stray quote costs its
    /// line and never the file. A `\` protects the byte after it, so an
    /// escaped quote never closes; one before the line break protects
    /// nothing.
    fn scan_string(&mut self) -> (SyntaxKind, RawKind, TokenFlags) {
        self.position += 1;
        let mut flags = TokenFlags::EMPTY;
        loop {
            match self.peek_byte() {
                None | Some(b'\n' | b'\r') => {
                    return (
                        SyntaxKind::StringLiteral,
                        RawKind::String,
                        flags | TokenFlags::UNTERMINATED,
                    );
                }
                Some(b'"') => {
                    self.position += 1;
                    return (SyntaxKind::StringLiteral, RawKind::String, flags);
                }
                Some(b'\\') => {
                    flags |= TokenFlags::HAS_ESCAPE;
                    self.bump_ascii();
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

impl Iterator for Lexer<'_> {
    type Item = RawToken;

    /// `Some` always consumes at least one byte; `None` means the cursor
    /// reached `source.len()`. Malformed input never ends iteration early.
    fn next(&mut self) -> Option<Self::Item> {
        if self.position == self.source.len() {
            return None;
        }

        let start = self.position;
        let token = self.scan_token();

        debug_assert!(self.position > start);
        debug_assert!(self.position <= self.source.len());

        Some(token)
    }
}
