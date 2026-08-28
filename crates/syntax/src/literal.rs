//! Validation of literal token text.
//!
//! The raw lexer establishes literal *shape*; these checks establish
//! *validity* under Jolt's rules: canonical numbers (no suffixes, no leading
//! zeros, lowercase `e` exponents with no `+` and no zero padding,
//! underscores only between digits).

use crate::cook::SyntaxErrorKind;
use crate::kind::SyntaxKind;

/// Classify a raw number token as an int or float literal, reporting any
/// trailing suffix.
///
/// The shape re-scan must mirror the raw lexer's maximal munch exactly, so
/// the suffix boundary lands where the lexer stopped attaching digits.
pub(crate) fn classify_number(text: &str, mut error: impl FnMut(SyntaxErrorKind)) -> SyntaxKind {
    let bytes = text.as_bytes();
    let mut misplaced_underscore = false;

    let mut position = eat_digits(bytes, 0, &mut misplaced_underscore);
    let mut is_float = false;

    // A leading zero is rejected rather than accepted as decimal, because
    // `0123` means octal in several other languages.
    if bytes[0] == b'0' && bytes[1..position].iter().any(u8::is_ascii_digit) {
        error(SyntaxErrorKind::LeadingZero);
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
                error(SyntaxErrorKind::UppercaseExponent);
            }
            position += 1;
            if matches!(bytes.get(position), Some(b'+' | b'-')) {
                if bytes[position] == b'+' {
                    error(SyntaxErrorKind::ExponentPlusSign);
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
                error(SyntaxErrorKind::ExponentLeadingZero);
            }
        }
    }

    if position < text.len() {
        // An `e`-leading suffix on a number with no exponent is almost
        // certainly a broken exponent, and the intended shape was a float;
        // after a real exponent (`1e5e5`) it is just an unknown suffix.
        if !consumed_exponent && matches!(bytes[position], b'e' | b'E') {
            is_float = true;
            error(SyntaxErrorKind::MissingExponent);
        } else {
            error(SyntaxErrorKind::UnknownSuffix);
        }
    }

    if misplaced_underscore {
        error(SyntaxErrorKind::MisplacedUnderscore);
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
fn eat_digits(bytes: &[u8], start: usize, misplaced_underscore: &mut bool) -> usize {
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
                    *misplaced_underscore = true;
                }
                position += 1;
            }
            _ => break,
        }
    }
    position
}
