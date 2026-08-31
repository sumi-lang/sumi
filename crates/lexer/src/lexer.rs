use sumi_text::TextSize;

use crate::kind::SyntaxKind;
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

        let (kind, raw, flags) = if self.position == 0 && self.remaining().starts_with('\u{feff}') {
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
                b'0'..=b'9' => {
                    let (kind, flags) = self.scan_number();
                    (kind, RawKind::Number, flags)
                }
                b'"' => (
                    SyntaxKind::StringLiteral,
                    RawKind::String,
                    self.scan_string(),
                ),
                b'\'' => (SyntaxKind::CharLiteral, RawKind::Char, self.scan_char()),
                b'r' if self.looks_like_raw_string() => (
                    SyntaxKind::RawStringLiteral,
                    RawKind::RawString,
                    self.scan_raw_string(),
                ),
                byte if is_ascii_ident_start(byte) => {
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
                byte if !byte.is_ascii() => self.scan_unicode(start),
                _ => {
                    self.bump_ascii();
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

    /// Scan a number and classify it as an int or float literal. The scan
    /// also decides whether the token breaks a literal rule, so canonical
    /// numbers — the overwhelming majority — never get re-scanned by the
    /// validator.
    fn scan_number(&mut self) -> (SyntaxKind, TokenFlags) {
        let start = self.position;
        let first = self.bump_ascii();
        debug_assert!(first.is_ascii_digit());

        let mut malformed = false;
        self.eat_decimal_digits(&mut malformed);

        // A leading zero is a literal error (`0123` means octal in several
        // other languages); `0_` alone is only a misplaced underscore.
        if first == b'0'
            && self.source.as_bytes()[start + 1..self.position]
                .iter()
                .any(u8::is_ascii_digit)
        {
            malformed = true;
        }

        let mut is_float = false;

        // A `.` continues the number only when a digit follows, so `1..2`
        // and `1.foo` leave the dot to punctuation.
        if self.peek_byte() == Some(b'.')
            && self
                .peek_byte_at(1)
                .is_some_and(|byte| byte.is_ascii_digit())
        {
            is_float = true;
            self.bump_ascii();
            self.eat_decimal_digits(&mut malformed);
        }

        // An exponent needs a digit after the optional sign; otherwise the
        // `e` is left to the suffix, as in `1em`.
        let mut has_exponent = false;
        if matches!(self.peek_byte(), Some(b'e' | b'E')) {
            has_exponent = match (self.peek_byte_at(1), self.peek_byte_at(2)) {
                (Some(byte), _) if byte.is_ascii_digit() => true,
                (Some(b'+' | b'-'), Some(byte)) => byte.is_ascii_digit(),
                _ => false,
            };
            if has_exponent {
                is_float = true;
                // The shape munches `1E5` and `1e+5` so the token stays
                // whole; an uppercase marker or a `+` sign is an error.
                if self.bump_ascii() == b'E' {
                    malformed = true;
                }
                if matches!(self.peek_byte(), Some(b'+' | b'-')) && self.bump_ascii() == b'+' {
                    malformed = true;
                }
                let exponent_start = self.position;
                self.eat_decimal_digits(&mut malformed);
                let digits = &self.source.as_bytes()[exponent_start..self.position];
                if digits[0] == b'0' && digits[1..].iter().any(u8::is_ascii_digit) {
                    malformed = true;
                }
            }
        }

        // Trailing identifier characters attach as a literal suffix (`1u32`)
        // for the validator to reject. An `e`-leading suffix on a number with
        // no exponent is a broken exponent, and the intended shape was a
        // float.
        let suffix_start = self.position;
        self.eat_ident_continue();
        if self.position > suffix_start {
            malformed = true;
            if !has_exponent && matches!(self.source.as_bytes()[suffix_start], b'e' | b'E') {
                is_float = true;
            }
        }

        (
            if is_float {
                SyntaxKind::FloatLiteral
            } else {
                SyntaxKind::IntLiteral
            },
            if malformed {
                TokenFlags::MALFORMED_NUMBER
            } else {
                TokenFlags::EMPTY
            },
        )
    }

    /// Advance over a digit run, flagging any `_` that is not surrounded by
    /// digits on both sides: grouping style is free, but `1_`, `1__0`, and
    /// `1_.5` are typo-shaped.
    fn eat_decimal_digits(&mut self, malformed: &mut bool) {
        while let Some(byte) = self.peek_byte() {
            match byte {
                b'0'..=b'9' => self.position += 1,
                b'_' => {
                    // A number's first byte is a digit, so `position - 1`
                    // stays inside the token.
                    let digit_before = self.source.as_bytes()[self.position - 1].is_ascii_digit();
                    let digit_after = self
                        .peek_byte_at(1)
                        .is_some_and(|byte| byte.is_ascii_digit());
                    if !(digit_before && digit_after) {
                        *malformed = true;
                    }
                    self.position += 1;
                }
                _ => break,
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

    /// Classify the identifier just scanned from `start`, while its bytes
    /// are still cache-hot: a discard, a keyword, or a plain identifier.
    fn classify_ident(&self, start: usize) -> SyntaxKind {
        match &self.source[start..self.position] {
            "_" => SyntaxKind::Underscore,
            text => SyntaxKind::from_keyword(text).unwrap_or(SyntaxKind::Ident),
        }
    }

    fn eat_ident_continue(&mut self) {
        while let Some(ch) = self.remaining().chars().next() {
            if !is_ident_continue(ch) {
                break;
            }
            self.position += ch.len_utf8();
        }
    }

    fn scan_unicode(&mut self, start: usize) -> (SyntaxKind, RawKind, TokenFlags) {
        let ch = self
            .remaining()
            .chars()
            .next()
            .expect("scan_unicode called at EOF");
        debug_assert!(!ch.is_ascii());

        if unicode_ident::is_xid_start(ch) {
            self.scan_ident();
            (
                self.classify_ident(start),
                RawKind::Ident,
                TokenFlags::EMPTY,
            )
        } else {
            self.bump_char();
            (SyntaxKind::Error, RawKind::Unknown, TokenFlags::EMPTY)
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
