//! Validation of literal token text.
//!
//! The raw lexer establishes literal *shape* and classification; these
//! checks establish *validity* under Sumi's rules: canonical integers (no
//! leading zeros, no suffixes) and the v0 escape set (`\n`, `\r`, `\t`,
//! `\\`, `\"`, `\'`, `\0`, `\u{…}`). The escape walker is the single
//! definition of the escape grammar; value decoding will reuse it when
//! lowering needs it.
//!
//! Multi-line literals add layout: the content begins on the line after the
//! opening `"""`, the closing `"""` begins its own line, and every content
//! line that is not blank starts with the closing line's indentation.
//!
//! The collector filters: numbers are re-scanned only when the scanner flagged
//! them malformed, strings only when escaped and terminated, characters and
//! multi-line literals only when terminated, so a token with a scanner error
//! gets no further errors here.

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
    walk_escapes(&text[body], false, |start, end, result| {
        if let Err(kind) = result {
            error(offset + start..offset + end, kind);
        }
    });
}

/// Validate the escapes and content length of a terminated character literal.
pub(crate) fn validate_char(text: &str, mut error: impl FnMut(Range<usize>, LexErrorKind)) {
    let body = &text[1..text.len() - 1];
    let mut pieces = 0usize;
    let mut extra_start = None;
    walk_escapes(body, false, |start, end, result| {
        if pieces == 1 {
            extra_start = Some(start);
        }
        pieces += 1;
        if let Err(kind) = result {
            error(start + 1..end + 1, kind);
        }
    });

    match pieces {
        0 => error(1..1, LexErrorKind::EmptyCharLiteral),
        1 => {}
        _ => error(
            extra_start.expect("a second piece was seen") + 1..text.len() - 1,
            LexErrorKind::MoreThanOneChar,
        ),
    }
}

/// Validate a terminated multi-line literal, `"""` to `"""`: its layout
/// and its escapes. Line breaks split the text into the opener's line, the
/// content lines, and the closer's line, and a lone `\r` is one too.
/// `parts` yields the literal's text ranges, excluding interpolation code;
/// escapes cannot cross from one part to the next.
pub(crate) fn validate_block_string(
    text: &str,
    parts: impl Iterator<Item = Range<usize>>,
    mut error: impl FnMut(Range<usize>, LexErrorKind),
) {
    let open = 3;
    let close = text.len() - 3;
    let body = &text[open..close];
    // Preserve diagnostic phase order: line endings, delimiters, indentation,
    // then escapes. Finding the two edge lines needs no line table.
    for (offset, _) in body.match_indices('\r') {
        let position = open + offset;
        if text.as_bytes().get(position + 1) != Some(&b'\n') {
            error(position..position + 1, LexErrorKind::LoneCarriageReturn);
        }
    }
    let opener_end = open + body.find(['\r', '\n']).unwrap_or(body.len());
    let closer_start = body
        .rfind(['\r', '\n'])
        .map_or(open, |offset| open + offset + 1);
    let opener = &text[open..opener_end];
    let opener_content = opener.trim_start_matches([' ', '\t']);
    if !opener_content.is_empty() {
        error(
            opener_end - opener_content.len()..opener_end,
            LexErrorKind::BlockStringOpenerContent,
        );
    }
    let multiline = opener_end < close;
    let prefix = &text[closer_start..close];
    let closer_own_line = multiline && prefix.trim_start_matches([' ', '\t']).is_empty();
    if !closer_own_line {
        error(close..text.len(), LexErrorKind::BlockStringCloserContent);
    }
    if !multiline {
        return;
    }
    let content_start = opener_end
        + if text[opener_end..].starts_with("\r\n") {
            2
        } else {
            1
        };
    let content = content_start..closer_start;
    if closer_own_line {
        let mut start = content.start;
        for line in text[content.clone()].split_inclusive(['\r', '\n']) {
            let end = start + line.len();
            let line = line.trim_end_matches(['\r', '\n']);
            let unindented = line.trim_start_matches([' ', '\t']);
            if !unindented.is_empty() && !line.starts_with(prefix) {
                error(
                    start..start + line.len() - unindented.len(),
                    LexErrorKind::BlockStringIndentation,
                );
            }
            start = end;
        }
    }
    for part in parts {
        let part = part.start.max(content.start)..part.end.min(content.end);
        if part.start >= part.end {
            continue;
        }
        walk_escapes(&text[part.clone()], true, |start, end, result| {
            if let Err(kind) = result {
                error(part.start + start..part.start + end, kind);
            }
        });
    }
}

/// Walk the body of a string or character literal, invoking `piece` once per
/// literal character or escape sequence with its body-relative byte range and
/// validity. In a `multiline` literal a `\` before a line break joins the
/// lines and is an escape like any other.
fn walk_escapes(
    body: &str,
    multiline: bool,
    mut piece: impl FnMut(usize, usize, Result<(), LexErrorKind>),
) {
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
            Some('n' | 'r' | 't' | '\\' | '"' | '\'' | '0' | '{' | '}') => Ok(()),
            Some('u') => scan_unicode_escape(&mut chars),
            Some('\n') if multiline => Ok(()),
            Some('\r') if multiline => {
                if chars.as_str().starts_with('\n') {
                    chars.next();
                }
                Ok(())
            }
            // Includes a backslash at the very end of the body.
            _ => Err(LexErrorKind::UnknownEscape),
        };
        let end = body.len() - chars.as_str().len();
        piece(start, end, result);
    }
}

/// Scan the `{1-6 hex digits}` payload of a `\u` escape. A malformed payload
/// is consumed through its closing `}` when one exists, so it still counts as
/// a single piece.
fn scan_unicode_escape(chars: &mut std::str::Chars<'_>) -> Result<(), LexErrorKind> {
    if !chars.as_str().starts_with('{') {
        return Err(LexErrorKind::MalformedUnicodeEscape);
    }
    chars.next();

    let mut digits = 0usize;
    let mut value = 0u32;
    let mut malformed = false;
    loop {
        match chars.next() {
            None => return Err(LexErrorKind::MalformedUnicodeEscape),
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
        Err(LexErrorKind::MalformedUnicodeEscape)
    } else if char::from_u32(value).is_none() {
        Err(LexErrorKind::InvalidUnicodeScalar)
    } else {
        Ok(())
    }
}
