use std::ops::Range;

use sumi_lexer::{LexedFile, RawKind, TokenFlags};
use sumi_text::{TextRange, TextSize};

use crate::kind::SyntaxKind;
use crate::literal;

/// Validate `lexed`'s literals. `source` must be the string it was lexed
/// from.
///
/// The fused lexer already assigned language-level kinds; what remains is
/// judging validity under Sumi's literal rules. Only tokens the scan
/// flagged, escaped strings, character literals, and roleless punctuation
/// are re-examined — on a canonical file this touches nothing and allocates
/// nothing. Invalid literals keep their literal kind; each error names its
/// token and the byte range at fault.
pub fn validate(source: &str, lexed: &LexedFile) -> Box<[SyntaxError]> {
    let mut errors = Vec::new();

    for index in 0..lexed.len() {
        let flags = lexed.flags(index);
        let mut error = |relative, kind| {
            errors.push(SyntaxError {
                token: index as u32,
                range: absolute_range(lexed.range(index), relative),
                kind,
            });
        };

        match lexed.kind(index) {
            SyntaxKind::IntLiteral | SyntaxKind::FloatLiteral => {
                if flags.contains(TokenFlags::MALFORMED_NUMBER) {
                    let derived = literal::number_errors(lexed.text(source, index), &mut error);
                    debug_assert_eq!(
                        derived,
                        lexed.kind(index),
                        "the lexer and validator must agree"
                    );
                } else if cfg!(debug_assertions) {
                    // The validator's re-scan must mirror the lexer's munch;
                    // check the unflagged side of that invariant in debug
                    // builds, where the flagged side is checked above.
                    let mut faults = 0usize;
                    let derived =
                        literal::number_errors(lexed.text(source, index), &mut |_, _| faults += 1);
                    debug_assert_eq!(faults, 0, "an unflagged number must be canonical");
                    debug_assert_eq!(
                        derived,
                        lexed.kind(index),
                        "the lexer and validator must agree"
                    );
                }
            }
            // A token the lexer already reported (unterminated literals)
            // gets no further errors here.
            SyntaxKind::StringLiteral => {
                if flags.contains(TokenFlags::HAS_ESCAPE)
                    && !flags.contains(TokenFlags::UNTERMINATED)
                {
                    literal::validate_string(lexed.text(source, index), &mut error);
                }
            }
            SyntaxKind::CharLiteral => {
                if !flags.contains(TokenFlags::UNTERMINATED) {
                    literal::validate_char(lexed.text(source, index), &mut error);
                }
            }
            // Punctuation without a role is reported here, where every
            // later phase can treat an `Error` token as already diagnosed;
            // other `Error` shapes carry a lexer error instead.
            SyntaxKind::Error if lexed.raw_kind(index) == RawKind::Punct => {
                error(0..1, SyntaxErrorKind::UnknownPunctuation);
            }
            _ => {}
        }
    }

    errors.into_boxed_slice()
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
    /// The relevant file-local UTF-8 byte range, contained within `token` and
    /// ending on character boundaries. May be empty when content is missing,
    /// as in an empty character literal.
    pub range: TextRange,
    pub kind: SyntaxErrorKind,
}

fn absolute_range(token: TextRange, relative: Range<usize>) -> TextRange {
    let start = u32::try_from(relative.start).expect("token offset fits in u32");
    let end = u32::try_from(relative.end).expect("token offset fits in u32");
    let token_start = token.start().to_u32();
    let token_len = token.end().to_u32() - token_start;
    assert!(start <= end && end <= token_len);
    TextRange::new(
        TextSize::new(token_start + start),
        TextSize::new(token_start + end),
    )
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
