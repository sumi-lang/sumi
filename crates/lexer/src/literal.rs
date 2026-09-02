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
use crate::generated::SyntaxKind;

struct NumberShape {
    integer: Range<usize>,
    fraction: Option<Range<usize>>,
    exponent: Option<ExponentShape>,
    suffix_start: usize,
    kind: SyntaxKind,
}

struct ExponentShape {
    sign: Option<usize>,
    digits: Range<usize>,
}

/// Report the errors of a number token the lexer flagged as malformed, and
/// return the kind its shape implies so callers can check it against the
/// lexer's classification.
///
/// The shape re-scan must mirror the raw lexer's maximal munch exactly, so
/// the suffix boundary lands where the lexer stopped attaching digits and
/// every error range stays inside the token.
pub(crate) fn number_errors(
    text: &str,
    error: impl FnMut(Range<usize>, LexErrorKind),
) -> SyntaxKind {
    scan_number(text, error).kind
}

/// Repair the mechanically canonicalizable parts of a numeric token. Any
/// suffix or incomplete exponent remains byte-for-byte as written.
pub fn canonicalize_number_literal(text: &str) -> Option<Box<str>> {
    if !text.as_bytes().first().is_some_and(u8::is_ascii_digit) {
        return None;
    }
    let shape = scan_number(text, |_, _| {});
    let mut canonical = String::with_capacity(text.len());
    canonical.push_str(&canonical_digit_run(&text[shape.integer.clone()], true));
    if let Some(fraction) = shape.fraction {
        canonical.push('.');
        canonical.push_str(&canonical_digit_run(&text[fraction], false));
    }
    if let Some(exponent) = shape.exponent {
        canonical.push('e');
        if exponent
            .sign
            .is_some_and(|sign| text.as_bytes()[sign] == b'-')
        {
            canonical.push('-');
        }
        canonical.push_str(&canonical_digit_run(&text[exponent.digits], true));
    }
    canonical.push_str(&text[shape.suffix_start..]);

    (canonical != text).then(|| canonical.into_boxed_str())
}

fn scan_number(text: &str, mut error: impl FnMut(Range<usize>, LexErrorKind)) -> NumberShape {
    let bytes = text.as_bytes();
    let mut misplaced_underscore = None;

    let mut position = eat_digits(bytes, 0, &mut misplaced_underscore);
    let integer = 0..position;
    let mut is_float = false;
    let mut fraction = None;

    // A leading zero is rejected rather than accepted as decimal, because
    // `0123` means octal in several other languages.
    if bytes[0] == b'0' && bytes[1..position].iter().any(u8::is_ascii_digit) {
        error(0..1, LexErrorKind::LeadingZero);
    }

    if bytes.get(position) == Some(&b'.')
        && bytes
            .get(position + 1)
            .is_some_and(|byte| byte.is_ascii_digit())
    {
        is_float = true;
        let fraction_start = position + 1;
        position = eat_digits(bytes, fraction_start, &mut misplaced_underscore);
        fraction = Some(fraction_start..position);
    }

    let mut consumed_exponent = false;
    let mut exponent = None;
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
                error(position..position + 1, LexErrorKind::UppercaseExponent);
            }
            position += 1;
            let mut sign = None;
            if matches!(bytes.get(position), Some(b'+' | b'-')) {
                sign = Some(position);
                if bytes[position] == b'+' {
                    error(position..position + 1, LexErrorKind::ExponentPlusSign);
                }
                position += 1;
            }
            let exponent_start = position;
            position = eat_digits(bytes, position, &mut misplaced_underscore);
            exponent = Some(ExponentShape {
                sign,
                digits: exponent_start..position,
            });
            if bytes[exponent_start] == b'0'
                && bytes[exponent_start + 1..position]
                    .iter()
                    .any(u8::is_ascii_digit)
            {
                error(
                    exponent_start..exponent_start + 1,
                    LexErrorKind::ExponentLeadingZero,
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
            error(position..position + 1, LexErrorKind::MissingExponent);
        } else {
            error(position..text.len(), LexErrorKind::UnknownSuffix);
        }
    }

    if let Some(position) = misplaced_underscore {
        error(position..position + 1, LexErrorKind::MisplacedUnderscore);
    }

    let kind = if is_float {
        SyntaxKind::FloatLiteral
    } else {
        SyntaxKind::IntLiteral
    };
    NumberShape {
        integer,
        fraction,
        exponent,
        suffix_start: position,
        kind,
    }
}

fn canonical_digit_run(run: &str, trim_zeros: bool) -> String {
    let bytes = run.as_bytes();
    let mut clean = String::with_capacity(run.len());
    for (position, &byte) in bytes.iter().enumerate() {
        if byte != b'_'
            || (position > 0
                && bytes[position - 1].is_ascii_digit()
                && bytes
                    .get(position + 1)
                    .is_some_and(|next| next.is_ascii_digit()))
        {
            clean.push(byte as char);
        }
    }
    if !trim_zeros || !clean.as_bytes().starts_with(b"0") {
        return clean;
    }
    if let Some(nonzero) = clean.bytes().position(|byte| matches!(byte, b'1'..=b'9')) {
        clean[nonzero..].to_owned()
    } else {
        "0".to_owned()
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
pub(crate) fn validate_string(text: &str, mut error: impl FnMut(Range<usize>, LexErrorKind)) {
    let body = &text[1..text.len() - 1];
    walk_escapes(body, false, |start, end, result| {
        if let Err(kind) = result {
            error(start + 1..end + 1, kind);
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

/// Validate a terminated multi-line literal, `"""` or `r"""` to `"""`: its
/// layout, and its escapes unless it is `raw`. Line breaks split the text
/// into the opener's line, the content lines, and the closer's line, and a
/// lone `\r` is one too, reported as it goes.
pub(crate) fn validate_block_string(
    text: &str,
    raw: bool,
    mut error: impl FnMut(Range<usize>, LexErrorKind),
) {
    let open = if raw { 4 } else { 3 };
    let close = text.len() - 3;
    let bytes = text.as_bytes();

    let mut lines: Vec<Range<usize>> = Vec::new();
    let mut line_start = open;
    let mut position = open;
    while position < close {
        match bytes[position] {
            b'\n' => {
                lines.push(line_start..position);
                position += 1;
                line_start = position;
            }
            b'\r' => {
                lines.push(line_start..position);
                if bytes.get(position + 1) == Some(&b'\n') {
                    position += 2;
                } else {
                    error(position..position + 1, LexErrorKind::LoneCarriageReturn);
                    position += 1;
                }
                line_start = position;
            }
            _ => position += 1,
        }
    }
    lines.push(line_start..close);
    let blank = |line: &Range<usize>| {
        text[line.clone()]
            .bytes()
            .all(|byte| byte == b' ' || byte == b'\t')
    };
    let indentation = |line: &Range<usize>| {
        line.start + text[line.clone()].len()
            - text[line.clone()].trim_start_matches([' ', '\t']).len()
    };

    let opener_line = lines[0].clone();
    if !blank(&opener_line) {
        error(
            indentation(&opener_line)..opener_line.end,
            LexErrorKind::BlockStringOpenerContent,
        );
    }
    let closer_line = lines[lines.len() - 1].clone();
    let closer_own_line = lines.len() > 1 && blank(&closer_line);
    if !closer_own_line {
        error(close..text.len(), LexErrorKind::BlockStringCloserContent);
    }

    if closer_own_line {
        let prefix = &text[closer_line.clone()];
        for line in &lines[1..lines.len() - 1] {
            if !blank(line) && !text[line.clone()].starts_with(prefix) {
                error(
                    line.start..indentation(line),
                    LexErrorKind::BlockStringIndentation,
                );
            }
        }
    }

    if !raw && lines.len() > 1 {
        // The content, from after the opener's line to the closer's line.
        let content = lines[1].start..closer_line.start;
        walk_escapes(&text[content.clone()], true, |start, end, result| {
            if let Err(kind) = result {
                error(content.start + start..content.start + end, kind);
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
            Some('n' | 'r' | 't' | '\\' | '"' | '\'' | '0') => Ok(()),
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
