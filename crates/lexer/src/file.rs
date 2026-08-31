use std::error::Error;
use std::fmt;

use sumi_text::{TextRange, TextSize};

use crate::lexer::Lexer;
use crate::token::{RawKind, RawToken, TokenFlags};

/// Lex `source` into a [`LexedFile`].
///
/// Lexing is total: any input produces a token stream that exactly partitions
/// the source, with malformed constructs reported through
/// [`errors`](LexedFile::errors) rather than aborting.
pub fn lex(source: &str) -> Result<LexedFile, SourceTooLarge> {
    let Ok(source_len) = u32::try_from(source.len()) else {
        return Err(SourceTooLarge {
            source_len: source.len(),
        });
    };

    let mut tokens = Vec::new();
    let mut errors = Vec::new();
    let mut position = 0;

    for token in Lexer::new(source) {
        let start = position;
        position += token.len.to_u32();

        let text = &source[start as usize..position as usize];
        if let Some(kind) = lex_error(&token, text) {
            errors.push(LexError {
                token: tokens.len() as u32,
                kind,
            });
        }

        tokens.push(StoredToken {
            start: TextSize::new(start),
            kind: token.kind,
            flags: token.flags,
        });
    }

    debug_assert_eq!(position, source_len);

    Ok(LexedFile {
        source_len: TextSize::new(source_len),
        tokens: tokens.into_boxed_slice(),
        errors: errors.into_boxed_slice(),
    })
}

fn lex_error(token: &RawToken, text: &str) -> Option<LexErrorKind> {
    let unterminated = token.flags.contains(TokenFlags::UNTERMINATED);
    match token.kind {
        RawKind::String if unterminated => Some(LexErrorKind::UnterminatedString),
        RawKind::RawString if unterminated => Some(LexErrorKind::UnterminatedRawString),
        RawKind::Char if unterminated => Some(LexErrorKind::UnterminatedChar),
        RawKind::Newline if token.flags.contains(TokenFlags::LONE_CR) => {
            Some(LexErrorKind::LoneCarriageReturn)
        }
        RawKind::Unknown if text == "\u{feff}" => Some(LexErrorKind::MisplacedBom),
        RawKind::Unknown => Some(LexErrorKind::UnknownCharacter),
        _ => None,
    }
}

/// The raw token buffer for one source file.
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
    /// The number of raw tokens.
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

    pub fn kind(&self, index: usize) -> RawKind {
        self.tokens[index].kind
    }

    pub fn flags(&self, index: usize) -> TokenFlags {
        self.tokens[index].flags
    }

    pub fn range(&self, index: usize) -> TextRange {
        let start = self.tokens[index].start;
        let end = self
            .tokens
            .get(index + 1)
            .map_or(self.source_len, |next| next.start);

        TextRange::new(start, end)
    }

    /// Slice `source` to this token's text. `source` must be the string this
    /// file was lexed from.
    pub fn text<'src>(&self, source: &'src str, index: usize) -> &'src str {
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
    pub fn token_at(&self, offset: TextSize) -> Option<usize> {
        if offset >= self.source_len {
            return None;
        }
        // Tokens partition the source, so the last token starting at or
        // before `offset` contains it; the first token starts at zero, so
        // one always exists.
        Some(self.tokens.partition_point(|token| token.start <= offset) - 1)
    }

    /// The token containing the byte before `offset`: the one a cursor at
    /// `offset` touches on its left. `None` at the start of the source.
    pub fn token_before(&self, offset: TextSize) -> Option<usize> {
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
    kind: RawKind,
    flags: TokenFlags,
}

/// A context-free lexical error, attached to the token that produced it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct LexError {
    /// Index of the offending token in the [`LexedFile`].
    pub token: u32,
    pub kind: LexErrorKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum LexErrorKind {
    UnterminatedString,
    UnterminatedRawString,
    UnterminatedChar,
    /// A `\r` line ending not followed by `\n`.
    LoneCarriageReturn,
    /// A U+FEFF byte-order mark somewhere other than byte zero.
    MisplacedBom,
    /// A character with no lexical meaning in the language.
    UnknownCharacter,
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
