use sumi_text::TextSize;

use crate::token::{RawKind, RawToken, TokenFlags};

const fn is_ascii_ident_start(byte: u8) -> bool {
    byte == b'_' || byte.is_ascii_alphabetic()
}

fn is_ident_continue(ch: char) -> bool {
    ch == '_'
        || ch.is_ascii_alphanumeric()
        || (!ch.is_ascii() && unicode_ident::is_xid_continue(ch))
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

        let (kind, flags) = if self.position == 0 && self.remaining().starts_with('\u{feff}') {
            self.bump_char();
            (RawKind::Bom, TokenFlags::EMPTY)
        } else {
            match self.peek_byte().expect("scan_token called at EOF") {
                b' ' | b'\t' => {
                    self.scan_horizontal_space();
                    (RawKind::HorizontalSpace, TokenFlags::EMPTY)
                }
                b'\n' | b'\r' => (RawKind::Newline, self.scan_newline()),
                b'/' if self.remaining().starts_with("//") => {
                    (RawKind::LineComment, self.scan_line_comment())
                }
                b'0'..=b'9' => {
                    self.scan_number();
                    (RawKind::Number, TokenFlags::EMPTY)
                }
                b'"' => (RawKind::String, self.scan_string()),
                b'\'' => (RawKind::Char, self.scan_char()),
                b'r' if self.looks_like_raw_string() => {
                    (RawKind::RawString, self.scan_raw_string())
                }
                byte if is_ascii_ident_start(byte) => {
                    self.scan_ident();
                    (RawKind::Ident, TokenFlags::EMPTY)
                }
                byte if byte.is_ascii_punctuation() => {
                    self.bump_ascii();
                    (RawKind::Punct, TokenFlags::EMPTY)
                }
                byte if !byte.is_ascii() => self.scan_unicode(),
                _ => {
                    self.bump_ascii();
                    (RawKind::Unknown, TokenFlags::EMPTY)
                }
            }
        };

        let len = self.position - start;
        debug_assert!(len > 0, "scan_token must always make progress");

        RawToken {
            kind,
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

    fn scan_number(&mut self) {
        let first = self.bump_ascii();
        debug_assert!(first.is_ascii_digit());

        self.eat_decimal_digits();

        // A `.` continues the number only when a digit follows, so `1..2`
        // and `1.foo` leave the dot to punctuation.
        if self.peek_byte() == Some(b'.')
            && self
                .peek_byte_at(1)
                .is_some_and(|byte| byte.is_ascii_digit())
        {
            self.bump_ascii();
            self.eat_decimal_digits();
        }

        // An exponent needs a digit after the optional sign; otherwise the
        // `e` is left to the suffix, as in `1em`.
        if matches!(self.peek_byte(), Some(b'e' | b'E')) {
            let has_exponent = match (self.peek_byte_at(1), self.peek_byte_at(2)) {
                (Some(byte), _) if byte.is_ascii_digit() => true,
                (Some(b'+' | b'-'), Some(byte)) => byte.is_ascii_digit(),
                _ => false,
            };
            if has_exponent {
                self.bump_ascii();
                if matches!(self.peek_byte(), Some(b'+' | b'-')) {
                    self.bump_ascii();
                }
                self.eat_decimal_digits();
            }
        }

        // Trailing identifier characters attach as a literal suffix (`1u32`)
        // for the cooker to validate.
        self.eat_ident_continue();
    }

    fn eat_decimal_digits(&mut self) {
        while let Some(byte) = self.peek_byte() {
            if byte.is_ascii_digit() || byte == b'_' {
                self.position += 1;
            } else {
                break;
            }
        }
    }

    /// Strings may span lines; an unterminated one runs to the end of input.
    fn scan_string(&mut self) -> TokenFlags {
        self.bump_ascii();

        let mut flags = TokenFlags::EMPTY;
        loop {
            match self.peek_byte() {
                None => {
                    flags |= TokenFlags::UNTERMINATED;
                    break;
                }
                Some(b'"') => {
                    self.bump_ascii();
                    break;
                }
                Some(b'\\') => {
                    flags |= TokenFlags::HAS_ESCAPE;
                    self.bump_ascii();
                    if self.peek_byte().is_some() {
                        self.bump_char();
                    }
                }
                // Only ASCII delimiters are inspected, so a byte-wise skip
                // cannot leave the final position mid-character.
                Some(_) => self.position += 1,
            }
        }
        flags
    }

    /// Character literals are line-bounded: an unterminated one ends at the
    /// newline so the rest of the line lexes normally.
    fn scan_char(&mut self) -> TokenFlags {
        self.bump_ascii();

        let mut flags = TokenFlags::EMPTY;
        loop {
            match self.peek_byte() {
                None | Some(b'\n' | b'\r') => {
                    flags |= TokenFlags::UNTERMINATED;
                    break;
                }
                Some(b'\'') => {
                    self.bump_ascii();
                    break;
                }
                Some(b'\\') => {
                    flags |= TokenFlags::HAS_ESCAPE;
                    self.bump_ascii();
                    if !matches!(self.peek_byte(), None | Some(b'\n' | b'\r')) {
                        self.bump_char();
                    }
                }
                Some(_) => self.position += 1,
            }
        }
        flags
    }

    fn looks_like_raw_string(&self) -> bool {
        let bytes = &self.source.as_bytes()[self.position..];
        debug_assert_eq!(bytes.first(), Some(&b'r'));

        let mut index = 1;
        while bytes.get(index) == Some(&b'#') {
            index += 1;
        }
        bytes.get(index) == Some(&b'"')
    }

    fn scan_raw_string(&mut self) -> TokenFlags {
        self.bump_ascii();

        let mut hashes = 0usize;
        while self.peek_byte() == Some(b'#') {
            self.position += 1;
            hashes += 1;
        }

        debug_assert_eq!(self.peek_byte(), Some(b'"'));
        self.bump_ascii();

        let bytes = self.source.as_bytes();
        let mut index = self.position;
        while index < bytes.len() {
            if bytes[index] == b'"' {
                let closing = &bytes[index + 1..];
                if closing.len() >= hashes && closing[..hashes].iter().all(|&byte| byte == b'#') {
                    self.position = index + 1 + hashes;
                    return TokenFlags::EMPTY;
                }
            }
            index += 1;
        }

        self.position = bytes.len();
        TokenFlags::UNTERMINATED
    }

    fn scan_ident(&mut self) {
        self.bump_char();
        self.eat_ident_continue();
    }

    fn eat_ident_continue(&mut self) {
        while let Some(ch) = self.remaining().chars().next() {
            if !is_ident_continue(ch) {
                break;
            }
            self.position += ch.len_utf8();
        }
    }

    fn scan_unicode(&mut self) -> (RawKind, TokenFlags) {
        let ch = self
            .remaining()
            .chars()
            .next()
            .expect("scan_unicode called at EOF");
        debug_assert!(!ch.is_ascii());

        if unicode_ident::is_xid_start(ch) {
            self.scan_ident();
            (RawKind::Ident, TokenFlags::EMPTY)
        } else {
            self.bump_char();
            (RawKind::Unknown, TokenFlags::EMPTY)
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
