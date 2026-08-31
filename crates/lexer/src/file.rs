use std::error::Error;
use std::fmt;
use std::ops::Range;

use sumi_text::{TextRange, TextSize};

use crate::kind::SyntaxKind;
use crate::lexer::Lexer;
use crate::literal;
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

        let needs_errors = match token.raw {
            RawKind::Number => {
                token.flags.contains(TokenFlags::MALFORMED_NUMBER) || cfg!(debug_assertions)
            }
            RawKind::String => {
                token.flags.contains(TokenFlags::UNTERMINATED)
                    || token.flags.contains(TokenFlags::HAS_ESCAPE)
            }
            RawKind::RawString => token.flags.contains(TokenFlags::UNTERMINATED),
            RawKind::Char | RawKind::Unknown => true,
            RawKind::Newline => token.flags.contains(TokenFlags::LONE_CR),
            RawKind::Punct => token.kind == SyntaxKind::Error,
            _ => false,
        };
        if needs_errors {
            let text = &source[start as usize..position as usize];
            collect_errors(
                &token,
                text,
                tokens.len() as u32,
                TextSize::new(start),
                &mut errors,
            );
        }

        tokens.push(StoredToken {
            start: TextSize::new(start),
            kind: token.kind,
            raw: token.raw,
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

fn collect_errors(
    token: &RawToken,
    text: &str,
    index: u32,
    start: TextSize,
    errors: &mut Vec<LexError>,
) {
    let unterminated = token.flags.contains(TokenFlags::UNTERMINATED);
    let primary = match token.raw {
        RawKind::String if unterminated => Some(LexErrorKind::UnterminatedString),
        RawKind::RawString if unterminated => Some(LexErrorKind::UnterminatedRawString),
        RawKind::Char if unterminated => Some(LexErrorKind::UnterminatedChar),
        RawKind::Newline if token.flags.contains(TokenFlags::LONE_CR) => {
            Some(LexErrorKind::LoneCarriageReturn)
        }
        RawKind::Unknown if text == "\u{feff}" => Some(LexErrorKind::MisplacedBom),
        RawKind::Unknown => Some(LexErrorKind::UnknownCharacter),
        _ => None,
    };
    if let Some(kind) = primary {
        errors.push(LexError {
            token: index,
            range: absolute_range(start, text.len(), 0..text.len()),
            kind,
        });
        return;
    }

    let mut error = |relative, kind| {
        errors.push(LexError {
            token: index,
            range: absolute_range(start, text.len(), relative),
            kind,
        });
    };
    match token.kind {
        SyntaxKind::IntLiteral | SyntaxKind::FloatLiteral => {
            if token.flags.contains(TokenFlags::MALFORMED_NUMBER) {
                let derived = literal::number_errors(text, &mut error);
                debug_assert_eq!(derived, token.kind, "the lexer passes must agree");
            } else if cfg!(debug_assertions) {
                let mut faults = 0usize;
                let derived = literal::number_errors(text, &mut |_, _| faults += 1);
                debug_assert_eq!(faults, 0, "an unflagged number must be canonical");
                debug_assert_eq!(derived, token.kind, "the lexer passes must agree");
            }
        }
        SyntaxKind::StringLiteral if token.flags.contains(TokenFlags::HAS_ESCAPE) => {
            literal::validate_string(text, &mut error);
        }
        SyntaxKind::CharLiteral => literal::validate_char(text, &mut error),
        SyntaxKind::Error if token.raw == RawKind::Punct => {
            error(0..1, LexErrorKind::UnknownPunctuation);
        }
        _ => {}
    }
}

fn absolute_range(start: TextSize, token_len: usize, relative: Range<usize>) -> TextRange {
    assert!(relative.start <= relative.end && relative.end <= token_len);
    let relative_start = u32::try_from(relative.start).expect("token offset fits in u32");
    let relative_end = u32::try_from(relative.end).expect("token offset fits in u32");
    TextRange::new(
        TextSize::new(start.to_u32() + relative_start),
        TextSize::new(start.to_u32() + relative_end),
    )
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

    /// The language-level kind of the token, assigned during the scan.
    pub fn kind(&self, index: usize) -> SyntaxKind {
        self.tokens[index].kind
    }

    /// Every token's language-level kind, in order: the stream a
    /// whole-file pass reads without per-index bounds checks.
    pub fn kinds(&self) -> impl ExactSizeIterator<Item = SyntaxKind> + Clone + '_ {
        self.tokens.iter().map(|token| token.kind)
    }

    /// The shape-only kind of the token, for phases that reason about
    /// lexical shape rather than language meaning.
    pub fn raw_kind(&self, index: usize) -> RawKind {
        self.tokens[index].raw
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
    kind: SyntaxKind,
    raw: RawKind,
    flags: TokenFlags,
}

const _: () = assert!(size_of::<StoredToken>() == 8, "tokens stay eight bytes");

/// A context-free token error, attached to the token that produced it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct LexError {
    /// Index of the offending token in the [`LexedFile`].
    pub token: u32,
    /// The relevant file-local UTF-8 byte range, contained within `token` and
    /// ending on character boundaries. May be empty when content is missing.
    pub range: TextRange,
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
    /// A numeric literal carries trailing characters; Sumi has no literal
    /// suffixes.
    UnknownSuffix,
    /// An `e` with no exponent digits after it, as in `1e` or `2.5e`.
    MissingExponent,
    /// An uppercase exponent marker, as in `1E5`; exponents are lowercase.
    UppercaseExponent,
    /// A redundant `+` sign in an exponent, as in `1e+5`.
    ExponentPlusSign,
    /// A zero-padded exponent, as in `1e05`.
    ExponentLeadingZero,
    /// A leading zero in an integer literal, as in `0123`.
    LeadingZero,
    /// A digit-separator underscore without digits on both sides, as in `1_`.
    MisplacedUnderscore,
    /// A `\` escape outside the supported set.
    UnknownEscape,
    /// A `\u` escape without a well-formed `{1-6 hex digits}` payload.
    MalformedUnicodeEscape,
    /// A `\u` escape naming a surrogate or a value beyond U+10FFFF.
    InvalidUnicodeScalar,
    /// A character literal with nothing in it: `''`.
    EmptyCharLiteral,
    /// A character literal containing more than one character.
    MoreThanOneChar,
    /// Punctuation with no role in the language, such as `;` or `[`.
    UnknownPunctuation,
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
