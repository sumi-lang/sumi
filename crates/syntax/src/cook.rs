use sumi_lexer::{LexedFile, RawKind};

use crate::kind::SyntaxKind;
use crate::literal;

/// Cook `lexed` into language-level token kinds. `source` must be the string
/// it was lexed from.
///
/// Cooking is total and strictly 1:1: token `index` in the result classifies
/// token `index` of `lexed`, so ranges, text, and flags stay queryable
/// through the [`LexedFile`]. Invalid literals keep their literal kind and
/// report through [`errors`](CookedFile::errors).
pub fn cook(source: &str, lexed: &LexedFile) -> CookedFile {
    let mut kinds = Vec::with_capacity(lexed.len());
    let mut errors = Vec::new();

    for index in 0..lexed.len() {
        let mut error = |kind| {
            errors.push(SyntaxError {
                token: index as u32,
                kind,
            });
        };

        let kind = match lexed.kind(index) {
            // The BOM is ignorable trivia to every downstream phase; its
            // identity stays recoverable through the raw kind.
            RawKind::Bom | RawKind::HorizontalSpace => SyntaxKind::Whitespace,
            RawKind::Newline => SyntaxKind::Newline,
            RawKind::LineComment => SyntaxKind::LineComment,
            RawKind::Ident => match lexed.text(source, index) {
                "_" => SyntaxKind::Underscore,
                text => SyntaxKind::from_keyword(text).unwrap_or(SyntaxKind::Ident),
            },
            RawKind::Number => literal::classify_number(lexed.text(source, index), &mut error),
            RawKind::String => {
                literal::validate_string(lexed.text(source, index), lexed.flags(index), &mut error);
                SyntaxKind::StringLiteral
            }
            RawKind::RawString => SyntaxKind::RawStringLiteral,
            RawKind::Char => {
                literal::validate_char(lexed.text(source, index), lexed.flags(index), &mut error);
                SyntaxKind::CharLiteral
            }
            RawKind::Punct => {
                let byte = lexed.text(source, index).as_bytes()[0];
                match SyntaxKind::from_punct(byte) {
                    Some(kind) => kind,
                    None => {
                        error(SyntaxErrorKind::UnknownPunctuation);
                        SyntaxKind::Error
                    }
                }
            }
            RawKind::Unknown => SyntaxKind::Error,
        };
        kinds.push(kind);
    }

    CookedFile {
        kinds: kinds.into_boxed_slice(),
        errors: errors.into_boxed_slice(),
    }
}

/// The cooked token kinds for one source file, parallel to its [`LexedFile`].
#[derive(Clone, Debug)]
pub struct CookedFile {
    kinds: Box<[SyntaxKind]>,
    errors: Box<[SyntaxError]>,
}

impl CookedFile {
    /// The number of cooked tokens; always equal to the lexed token count.
    pub fn len(&self) -> usize {
        self.kinds.len()
    }

    pub fn is_empty(&self) -> bool {
        self.kinds.is_empty()
    }

    pub fn kind(&self, index: usize) -> SyntaxKind {
        self.kinds[index]
    }

    pub fn errors(&self) -> &[SyntaxError] {
        &self.errors
    }
}

/// A language-level error, attached to the token that produced it.
///
/// Lexical errors (unterminated literals, lone carriage returns) stay in the
/// [`LexedFile`]; a token the lexer already reported gets no further errors
/// here.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct SyntaxError {
    /// Index of the offending token in the file's token buffer.
    pub token: u32,
    pub kind: SyntaxErrorKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SyntaxErrorKind {
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
