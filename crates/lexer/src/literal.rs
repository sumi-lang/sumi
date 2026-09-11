//! Validation of literal token text.
//!
//! The raw lexer establishes literal *shape* and classification; these
//! checks establish *validity* under Sumi's rules: canonical integers (no
//! leading zeros, no suffixes) and the v0 escape set (`\n`, `\r`, `\t`,
//! `\\`, `\"`, `\0`). The escape walker is the single definition of the
//! escape grammar; value decoding will reuse it when lowering needs it.
//!
//! The collector filters: numbers are re-scanned only when the scanner flagged
//! them malformed and strings only when escaped and terminated, so a token
//! with a scanner error gets no further errors here.

use std::ops::Range;

use crate::file::LexErrorKind;

/// Report the errors of a number token the lexer flagged as malformed.
///
/// The re-scan must mirror the raw lexer's maximal munch exactly, so the
/// suffix boundary lands where the lexer stopped attaching digits and every
/// error range stays inside the token.
pub(crate) fn number_errors(text: &str, mut error: impl FnMut(Range<usize>, LexErrorKind)) {
    let digits = digit_run(text);
    // A leading zero is rejected rather than accepted as decimal, because
    // `0123` means octal in several other languages.
    if text.starts_with('0') && digits > 1 {
        error(0..1, LexErrorKind::LeadingZero);
    }
    if digits < text.len() {
        error(digits..text.len(), LexErrorKind::UnknownSuffix);
    }
}

/// Repair the mechanically canonicalizable part of a numeric token, its
/// leading zeros. Any suffix remains byte-for-byte as written.
pub fn canonicalize_number_literal(text: &str) -> Option<Box<str>> {
    if !text.as_bytes().first().is_some_and(u8::is_ascii_digit) {
        return None;
    }
    let digits = digit_run(text);
    let nonzero = text[..digits]
        .bytes()
        .position(|byte| byte != b'0')
        .unwrap_or(digits - 1);
    (nonzero > 0).then(|| text[nonzero..].into())
}

/// The length of the digit run a number token begins with.
fn digit_run(text: &str) -> usize {
    text.bytes()
        .position(|byte| !byte.is_ascii_digit())
        .unwrap_or(text.len())
}

/// Validate the escapes of a terminated string literal.
pub(crate) fn validate_string(text: &str, error: impl FnMut(Range<usize>, LexErrorKind)) {
    validate_string_body(text, 1..text.len() - 1, error);
}

/// Validate the escapes of `text[body]`, the text of a `"…"` literal or
/// of one part of one with holes.
pub(crate) fn validate_string_body(
    text: &str,
    body: Range<usize>,
    mut error: impl FnMut(Range<usize>, LexErrorKind),
) {
    let offset = body.start;
    walk_escapes(&text[body], |start, end, result| {
        if let Err(kind) = result {
            error(offset + start..offset + end, kind);
        }
    });
}

/// Walk the body of a string literal, invoking `piece` once per literal
/// character or escape sequence with its body-relative byte range and
/// validity.
fn walk_escapes(body: &str, mut piece: impl FnMut(usize, usize, Result<(), LexErrorKind>)) {
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
            Some('n' | 'r' | 't' | '\\' | '"' | '0' | '{' | '}') => Ok(()),
            // Includes a backslash at the very end of the body.
            _ => Err(LexErrorKind::UnknownEscape),
        };
        let end = body.len() - chars.as_str().len();
        piece(start, end, result);
    }
}
