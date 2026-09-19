use std::error::Error;
use std::fmt;
use std::ops::Range;

use sumi_text::{TextRange, TextSize};

use crate::generated::SyntaxKind;
use crate::index::RawIdx;
use crate::token::TokenFlags;

/// Lex `source` into a [`LexedFile`], with its faults in
/// [`errors`](LexedFile::errors).
pub fn lex(source: &str) -> Result<LexedFile, SourceTooLarge> {
    let Ok(source_len) = u32::try_from(source.len()) else {
        return Err(SourceTooLarge {
            source_len: source.len(),
        });
    };

    let mut lexer = Lexer {
        source,
        position: 0,
        tokens: Vec::new(),
        errors: Vec::new(),
    };
    while lexer.position < source.len() {
        lexer.scan_token();
    }

    Ok(LexedFile {
        source_len: TextSize::new(source_len),
        tokens: lexer.tokens.into_boxed_slice(),
        errors: lexer.errors.into_boxed_slice(),
    })
}

/// Identifiers are ASCII: a letter or `_`, then letters, digits, and `_`.
/// Any other character has no meaning in the language.
const fn is_ident_start(byte: u8) -> bool {
    byte == b'_' || byte.is_ascii_alphabetic()
}

const fn is_ident_continue(byte: u8) -> bool {
    byte == b'_' || byte.is_ascii_alphanumeric()
}

/// The scan in progress: a cursor over the source, and the tokens and
/// errors behind it. `source.len()` fits in `u32`.
struct Lexer<'src> {
    source: &'src str,
    position: usize,
    tokens: Vec<StoredToken>,
    errors: Vec<LexError>,
}

impl Lexer<'_> {
    fn remaining(&self) -> &str {
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

    fn bump_char(&mut self) {
        let ch = self.remaining().chars().next().expect("cannot bump at EOF");
        self.position += ch.len_utf8();
    }

    /// Report an error of the token being scanned, over `range`.
    fn error(&mut self, range: Range<usize>, kind: LexErrorKind) {
        self.errors.push(LexError {
            token: RawIdx::new(self.tokens.len() as u32),
            range: TextRange::new(
                TextSize::new(range.start as u32),
                TextSize::new(range.end as u32),
            ),
            kind,
        });
    }

    /// Scan one token from the cursor, which is not at the end of the
    /// source, and push it with any errors it has.
    fn scan_token(&mut self) {
        let start = self.position;

        let (kind, flags) = match self.peek_byte().expect("scan_token called at EOF") {
            b' ' | b'\t' => {
                self.scan_horizontal_space();
                (SyntaxKind::Whitespace, TokenFlags::EMPTY)
            }
            b'\n' | b'\r' => {
                self.scan_newline();
                (SyntaxKind::Newline, TokenFlags::EMPTY)
            }
            b'/' if self.remaining().starts_with("//") => {
                self.scan_line_comment();
                (SyntaxKind::LineComment, TokenFlags::EMPTY)
            }
            b'0'..=b'9' => (SyntaxKind::IntLiteral, self.scan_number()),
            b'"' => (SyntaxKind::StringLiteral, self.scan_string()),
            byte if is_ident_start(byte) => {
                self.scan_ident();
                (self.classify_ident(start), TokenFlags::EMPTY)
            }
            byte if byte.is_ascii_punctuation() => {
                self.bump_ascii();
                let kind = match SyntaxKind::from_punct(byte) {
                    Some(kind) => kind,
                    None => {
                        self.error(start..self.position, LexErrorKind::UnknownPunctuation);
                        SyntaxKind::Error
                    }
                };
                (kind, TokenFlags::EMPTY)
            }
            _ => {
                self.bump_char();
                self.error(start..self.position, LexErrorKind::UnknownCharacter);
                (SyntaxKind::Error, TokenFlags::EMPTY)
            }
        };

        debug_assert!(
            self.position > start,
            "scan_token must always make progress"
        );
        self.tokens.push(StoredToken {
            start: TextSize::new(start as u32),
            kind,
            flags,
        });
    }

    fn scan_horizontal_space(&mut self) {
        while matches!(self.peek_byte(), Some(b' ' | b'\t')) {
            self.position += 1;
        }
    }

    /// One `\n`, `\r\n`, or lone `\r`, the last an error.
    fn scan_newline(&mut self) {
        let start = self.position;
        if self.bump_ascii() == b'\r' {
            if self.peek_byte() == Some(b'\n') {
                self.position += 1;
            } else {
                self.error(start..self.position, LexErrorKind::LoneCarriageReturn);
            }
        }
    }

    fn scan_line_comment(&mut self) {
        let rest = self.remaining();
        let line_end = rest.find(['\n', '\r']).unwrap_or(rest.len());
        self.position += line_end;
    }

    /// Scan an integer literal: a run of digits, with any identifier
    /// characters after it attached as a suffix.
    fn scan_number(&mut self) -> TokenFlags {
        let start = self.position;
        let first = self.bump_ascii();
        debug_assert!(first.is_ascii_digit());

        while self.peek_byte().is_some_and(|byte| byte.is_ascii_digit()) {
            self.position += 1;
        }
        let mut flags = TokenFlags::EMPTY;

        // A leading zero is a literal error: `0123` means octal in several
        // other languages.
        if first == b'0' && self.position > start + 1 {
            self.error(start..start + 1, LexErrorKind::LeadingZero);
            flags = TokenFlags::MALFORMED_NUMBER;
        }

        // Trailing identifier characters attach as a suffix (`1u32`,
        // `1_000`, `1e5`) and are rejected as one: a `.` never joins, so
        // `1.5` is three tokens.
        let suffix_start = self.position;
        self.eat_ident_continue();
        if self.position > suffix_start {
            self.error(suffix_start..self.position, LexErrorKind::UnknownSuffix);
            flags = TokenFlags::MALFORMED_NUMBER;
        }

        flags
    }

    /// Scan a `"…"` literal from its opener to its closer, or to its end:
    /// the line break or the end of input, which leaves it unterminated.
    /// Every literal is bounded by its line, so a stray quote costs its
    /// line and never the file. A `\` protects the byte after it, so an
    /// escaped quote never closes; one before the line break protects
    /// nothing. An escape outside the supported set is an error, unless the
    /// literal is unterminated: then the missing closer is its only fault.
    fn scan_string(&mut self) -> TokenFlags {
        let start = self.position;
        let errors_before = self.errors.len();
        self.position += 1;
        loop {
            match self.peek_byte() {
                None | Some(b'\n' | b'\r') => {
                    self.errors.truncate(errors_before);
                    self.error(start..self.position, LexErrorKind::UnterminatedString);
                    return TokenFlags::UNTERMINATED;
                }
                Some(b'"') => {
                    self.position += 1;
                    return TokenFlags::EMPTY;
                }
                Some(b'\\') => {
                    let escape_start = self.position;
                    self.position += 1;
                    match self.peek_byte() {
                        Some(b'n' | b'r' | b't' | b'\\' | b'"' | b'0') => self.position += 1,
                        None | Some(b'\n' | b'\r') => {}
                        Some(_) => {
                            self.bump_char();
                            self.error(escape_start..self.position, LexErrorKind::UnknownEscape);
                        }
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

    /// Classify the identifier just scanned from `start`: a reserved word —
    /// `_` included — or a plain identifier.
    fn classify_ident(&self, start: usize) -> SyntaxKind {
        SyntaxKind::from_keyword(&self.source[start..self.position]).unwrap_or(SyntaxKind::Ident)
    }

    fn eat_ident_continue(&mut self) {
        while self.peek_byte().is_some_and(is_ident_continue) {
            self.position += 1;
        }
    }
}

/// The token buffer for one source file.
///
/// Tokens exactly partition the source: the first starts at zero, each ends
/// where the next begins, and the last ends at
/// [`source_len`](LexedFile::source_len). The file does not retain the source
/// text; pass it back in to [`text`](LexedFile::text).
#[derive(Clone, Debug)]
pub struct LexedFile {
    source_len: TextSize,
    tokens: Box<[StoredToken]>,
    errors: Box<[LexError]>,
}

impl LexedFile {
    /// The number of tokens.
    pub fn len(&self) -> usize {
        self.tokens.len()
    }

    pub fn is_empty(&self) -> bool {
        self.tokens.is_empty()
    }

    /// The length of the lexed source in UTF-8 bytes.
    pub fn source_len(&self) -> TextSize {
        self.source_len
    }

    /// The index one past the last token: where a range running to the end
    /// of the file stops.
    pub fn end(&self) -> RawIdx {
        RawIdx::new(self.tokens.len() as u32)
    }

    /// Every token's index, in order.
    pub fn indices(&self) -> impl DoubleEndedIterator<Item = RawIdx> + ExactSizeIterator {
        RawIdx::new(0).until(self.end())
    }

    /// The language-level kind of the token, assigned during the scan.
    pub fn kind(&self, index: RawIdx) -> SyntaxKind {
        self.tokens[index.to_usize()].kind
    }

    /// Every token's language-level kind, in order: the stream a
    /// whole-file pass reads without per-index bounds checks.
    pub fn kinds(&self) -> impl ExactSizeIterator<Item = SyntaxKind> + Clone + '_ {
        self.tokens.iter().map(|token| token.kind)
    }

    pub fn flags(&self, index: RawIdx) -> TokenFlags {
        self.tokens[index.to_usize()].flags
    }

    pub fn range(&self, index: RawIdx) -> TextRange {
        let start = self.tokens[index.to_usize()].start;
        TextRange::new(start, self.boundary(index + 1))
    }

    /// The byte offset where token `index` begins, or the end of the source
    /// for the boundary one past the last token: one load, for the ranges
    /// of the constructs above that are all token-aligned.
    pub fn boundary(&self, index: RawIdx) -> TextSize {
        self.tokens
            .get(index.to_usize())
            .map_or(self.source_len, |token| token.start)
    }

    /// Slice `source` to this token's text. `source` must be the string this
    /// file was lexed from.
    pub fn text<'src>(&self, source: &'src str, index: RawIdx) -> &'src str {
        self.range(index).text(source)
    }

    pub fn errors(&self) -> &[LexError] {
        &self.errors
    }

    /// The token containing the byte at `offset`, by binary search over the
    /// token starts. `None` at or past the end of the source, where there is
    /// no byte. A cursor sitting on a token boundary gets the token to its
    /// right; [`token_before`](Self::token_before) is the left-biased
    /// counterpart.
    pub fn token_at(&self, offset: TextSize) -> Option<RawIdx> {
        if offset >= self.source_len {
            return None;
        }
        // Tokens partition the source, so the last token starting at or
        // before `offset` contains it; the first token starts at zero, so
        // one always exists.
        let index = self.tokens.partition_point(|token| token.start <= offset) - 1;
        Some(RawIdx::new(index as u32))
    }

    /// The token containing the byte before `offset`: the one a cursor at
    /// `offset` touches on its left. `None` at the start of the source.
    pub fn token_before(&self, offset: TextSize) -> Option<RawIdx> {
        let previous = offset.to_u32().checked_sub(1)?;
        self.token_at(TextSize::new(previous))
    }
}

/// The compact per-token entry: eight bytes, with end offsets derived from
/// the next token's start.
#[repr(C)]
#[derive(Clone, Copy, Debug)]
struct StoredToken {
    start: TextSize,
    kind: SyntaxKind,
    flags: TokenFlags,
}

const _: () = assert!(size_of::<StoredToken>() == 8, "tokens stay eight bytes");

/// A context-free token error, attached to the token that produced it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct LexError {
    /// The offending token in the [`LexedFile`].
    pub token: RawIdx,
    /// The relevant file-local UTF-8 byte range, nonempty, contained within
    /// `token`, and ending on character boundaries.
    pub range: TextRange,
    pub kind: LexErrorKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum LexErrorKind {
    UnterminatedString,
    /// A `\r` line ending not followed by `\n`.
    LoneCarriageReturn,
    /// A character with no lexical meaning in the language.
    UnknownCharacter,
    /// A numeric literal carries trailing identifier characters, as in
    /// `1u32`, `1_000`, or `1e5`; Sumi has no literal suffixes, separators,
    /// or floats.
    UnknownSuffix,
    /// A leading zero in an integer literal, as in `0123`.
    LeadingZero,
    /// A `\` escape outside the supported set: `\n`, `\r`, `\t`, `\\`,
    /// `\"`, and `\0`.
    UnknownEscape,
    /// Punctuation with no role in the language, such as `;` or `[`.
    UnknownPunctuation,
}

/// Repair the mechanically canonicalizable part of a numeric token, its
/// leading zeros. Any suffix remains byte-for-byte as written.
pub fn canonicalize_number_literal(text: &str) -> Option<Box<str>> {
    if !text.as_bytes().first().is_some_and(u8::is_ascii_digit) {
        return None;
    }
    let digits = text
        .bytes()
        .position(|byte| !byte.is_ascii_digit())
        .unwrap_or(text.len());
    let nonzero = text[..digits]
        .bytes()
        .position(|byte| byte != b'0')
        .unwrap_or(digits - 1);
    (nonzero > 0).then(|| text[nonzero..].into())
}

/// `source.len()` exceeds the `u32` coordinate space of [`TextSize`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SourceTooLarge {
    pub source_len: usize,
}

impl fmt::Display for SourceTooLarge {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "source is {} bytes but the maximum is {} bytes",
            self.source_len,
            u32::MAX
        )
    }
}

impl Error for SourceTooLarge {}
