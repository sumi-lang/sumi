//! Validation of literal token text.
//!
//! The raw lexer establishes literal *shape* and classification; these
//! checks establish *validity* under Sumi's rules: canonical numbers (no
//! suffixes, no leading zeros, lowercase `e` exponents with no `+` and no
//! zero padding, underscores only between digits) and the v0 escape set
//! (`\n`, `\r`, `\t`, `\\`, `\"`, `\'`, `\0`, `\u{…}`). The escape walker is
//! the single definition of the escape grammar; value decoding will reuse it
//! when lowering needs it.
//!
//! The validator filters: numbers are re-scanned only when the lexer flagged
//! them malformed, strings only when escaped and terminated, and characters
//! only when terminated, so a token the lexer already reported gets no
//! further errors here.

use std::ops::Range;

use crate::kind::SyntaxKind;
use crate::validate::SyntaxErrorKind;

/// Report the errors of a number token the lexer flagged as malformed, and
/// return the kind its shape implies so callers can check it against the
/// lexer's classification.
///
/// The shape re-scan must mirror the raw lexer's maximal munch exactly, so
/// the suffix boundary lands where the lexer stopped attaching digits and
/// every error range stays inside the token.
pub(crate) fn number_errors(
    text: &str,
    mut error: impl FnMut(Range<usize>, SyntaxErrorKind),
) -> SyntaxKind {
    let bytes = text.as_bytes();
    let mut misplaced_underscore = None;

    let mut position = eat_digits(bytes, 0, &mut misplaced_underscore);
    let mut is_float = false;

    // A leading zero is rejected rather than accepted as decimal, because
    // `0123` means octal in several other languages.
    if bytes[0] == b'0' && bytes[1..position].iter().any(u8::is_ascii_digit) {
        error(0..1, SyntaxErrorKind::LeadingZero);
    }

    if bytes.get(position) == Some(&b'.')
        && bytes
            .get(position + 1)
            .is_some_and(|byte| byte.is_ascii_digit())
    {
        is_float = true;
        position = eat_digits(bytes, position + 1, &mut misplaced_underscore);
    }

    let mut consumed_exponent = false;
    if matches!(bytes.get(position), Some(b'e' | b'E')) {
        let has_exponent = match (bytes.get(position + 1), bytes.get(position + 2)) {
            (Some(byte), _) if byte.is_ascii_digit() => true,
            (Some(b'+' | b'-'), Some(byte)) => byte.is_ascii_digit(),
            _ => false,
        };
        if has_exponent {
            consumed_exponent = true;
            is_float = true;
            // Syntax markers are lowercase: the shape munches `1E5` so the
            // token stays whole, and the marker's case is rejected here.
            if bytes[position] == b'E' {
                error(position..position + 1, SyntaxErrorKind::UppercaseExponent);
            }
            position += 1;
            if matches!(bytes.get(position), Some(b'+' | b'-')) {
                if bytes[position] == b'+' {
                    error(position..position + 1, SyntaxErrorKind::ExponentPlusSign);
                }
                position += 1;
            }
            let exponent_start = position;
            position = eat_digits(bytes, position, &mut misplaced_underscore);
            if bytes[exponent_start] == b'0'
                && bytes[exponent_start + 1..position]
                    .iter()
                    .any(u8::is_ascii_digit)
            {
                error(
                    exponent_start..exponent_start + 1,
                    SyntaxErrorKind::ExponentLeadingZero,
                );
            }
        }
    }

    if position < text.len() {
        // An `e`-leading suffix on a number with no exponent is almost
        // certainly a broken exponent, and the intended shape was a float;
        // after a real exponent (`1e5e5`) it is just an unknown suffix.
        if !consumed_exponent && matches!(bytes[position], b'e' | b'E') {
            is_float = true;
            error(position..position + 1, SyntaxErrorKind::MissingExponent);
        } else {
            error(position..text.len(), SyntaxErrorKind::UnknownSuffix);
        }
    }

    if let Some(position) = misplaced_underscore {
        error(position..position + 1, SyntaxErrorKind::MisplacedUnderscore);
    }

    if is_float {
        SyntaxKind::FloatLiteral
    } else {
        SyntaxKind::IntLiteral
    }
}

/// Advance over a digit run, flagging any `_` that is not surrounded by
/// digits on both sides. Reported at most once per token: grouping style is
/// free, but `1_`, `1__0`, and `1_.5` are typo-shaped.
fn eat_digits(bytes: &[u8], start: usize, misplaced_underscore: &mut Option<usize>) -> usize {
    let mut position = start;
    while position < bytes.len() {
        match bytes[position] {
            b'0'..=b'9' => position += 1,
            b'_' => {
                let digit_before = position > 0 && bytes[position - 1].is_ascii_digit();
                let digit_after = bytes
                    .get(position + 1)
                    .is_some_and(|byte| byte.is_ascii_digit());
                if !(digit_before && digit_after) {
                    misplaced_underscore.get_or_insert(position);
                }
                position += 1;
            }
            _ => break,
        }
    }
    position
}

/// Validate the escapes of a terminated string literal.
pub(crate) fn validate_string(text: &str, mut error: impl FnMut(Range<usize>, SyntaxErrorKind)) {
    let body = &text[1..text.len() - 1];
    walk_escapes(body, |start, end, result| {
        if let Err(kind) = result {
            error(start + 1..end + 1, kind);
        }
    });
}

/// Validate the escapes and content length of a terminated character literal.
pub(crate) fn validate_char(text: &str, mut error: impl FnMut(Range<usize>, SyntaxErrorKind)) {
    let body = &text[1..text.len() - 1];
    let mut pieces = 0usize;
    let mut extra_start = None;
    walk_escapes(body, |start, end, result| {
        if pieces == 1 {
            extra_start = Some(start);
        }
        pieces += 1;
        if let Err(kind) = result {
            error(start + 1..end + 1, kind);
        }
    });

    match pieces {
        0 => error(1..1, SyntaxErrorKind::EmptyCharLiteral),
        1 => {}
        _ => error(
            extra_start.expect("a second piece was seen") + 1..text.len() - 1,
            SyntaxErrorKind::MoreThanOneChar,
        ),
    }
}

/// Walk the body of a string or character literal, invoking `piece` once per
/// literal character or escape sequence with its body-relative byte range and
/// validity.
fn walk_escapes(body: &str, mut piece: impl FnMut(usize, usize, Result<(), SyntaxErrorKind>)) {
    let mut chars = body.chars();
    while !chars.as_str().is_empty() {
        let start = body.len() - chars.as_str().len();
        let ch = chars.next().expect("the remaining body is not empty");
        if ch != '\\' {
            let end = body.len() - chars.as_str().len();
            piece(start, end, Ok(()));
            continue;
        }

        let result = match chars.next() {
            Some('n' | 'r' | 't' | '\\' | '"' | '\'' | '0') => Ok(()),
            Some('u') => scan_unicode_escape(&mut chars),
            // Includes a backslash at the very end of the body.
            _ => Err(SyntaxErrorKind::UnknownEscape),
        };
        let end = body.len() - chars.as_str().len();
        piece(start, end, result);
    }
}

/// Scan the `{1-6 hex digits}` payload of a `\u` escape. A malformed payload
/// is consumed through its closing `}` when one exists, so it still counts as
/// a single piece.
fn scan_unicode_escape(chars: &mut std::str::Chars<'_>) -> Result<(), SyntaxErrorKind> {
    if !chars.as_str().starts_with('{') {
        return Err(SyntaxErrorKind::MalformedUnicodeEscape);
    }
    chars.next();

    let mut digits = 0usize;
    let mut value = 0u32;
    let mut malformed = false;
    loop {
        match chars.next() {
            None => return Err(SyntaxErrorKind::MalformedUnicodeEscape),
            Some('}') => break,
            Some(ch) => match ch.to_digit(16) {
                Some(digit) if digits < 6 => {
                    digits += 1;
                    value = value * 16 + digit;
                }
                _ => malformed = true,
            },
        }
    }

    if malformed || digits == 0 {
        Err(SyntaxErrorKind::MalformedUnicodeEscape)
    } else if char::from_u32(value).is_none() {
        Err(SyntaxErrorKind::InvalidUnicodeScalar)
    } else {
        Ok(())
    }
}
