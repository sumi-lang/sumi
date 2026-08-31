//! Literal validation: the errors owed to the tokens the scan flagged.
//! Classification goldens live with the lexer, which assigns the kinds.

use sumi_lexer::lex;
use sumi_syntax::{SyntaxErrorKind, validate};

#[track_caller]
fn check_errors(source: &str, expected: &[(u32, SyntaxErrorKind)]) {
    let lexed = lex(source).expect("test sources fit in u32");
    let errors = validate(source, &lexed);
    for error in &errors {
        let token = lexed.range(error.token as usize);
        assert!(token.start() <= error.range.start());
        assert!(error.range.end() <= token.end());
        assert!(source.is_char_boundary(error.range.start().to_usize()));
        assert!(source.is_char_boundary(error.range.end().to_usize()));
    }
    let actual: Vec<(u32, SyntaxErrorKind)> = errors
        .iter()
        .map(|error| (error.token, error.kind))
        .collect();
    assert_eq!(actual, expected, "for source {source:?}");
}

#[track_caller]
fn check_error_ranges(source: &str, expected: &[(u32, u32, u32, SyntaxErrorKind)]) {
    let lexed = lex(source).expect("test sources fit in u32");
    let errors = validate(source, &lexed);
    let actual: Vec<_> = errors
        .iter()
        .map(|error| {
            (
                error.token,
                error.range.start().to_u32(),
                error.range.end().to_u32(),
                error.kind,
            )
        })
        .collect();
    assert_eq!(actual, expected, "for source {source:?}");
}

#[test]
fn clean_sources_validate_to_nothing() {
    check_errors("", &[]);
    check_errors("( ) { } , : . = < > ! + - * / % & |", &[]);
    check_errors("0 123 1_000 1.5 1e5 2.5e-3", &[]);
}

#[test]
fn unused_punctuation_validates_to_error() {
    // Reported here, where every later phase can treat an `Error` token as
    // already diagnosed.
    check_errors(";", &[(0, SyntaxErrorKind::UnknownPunctuation)]);
}

#[test]
fn exponent_plus_and_padding_are_rejected() {
    check_errors("1e+5", &[(0, SyntaxErrorKind::ExponentPlusSign)]);
    check_errors("1e-5", &[]);
    check_errors("1e05", &[(0, SyntaxErrorKind::ExponentLeadingZero)]);
    check_errors("1e-05", &[(0, SyntaxErrorKind::ExponentLeadingZero)]);
    check_errors("1e0", &[]);
}

#[test]
fn multiple_number_errors_report_in_source_order() {
    check_errors(
        "1E+05",
        &[
            (0, SyntaxErrorKind::UppercaseExponent),
            (0, SyntaxErrorKind::ExponentPlusSign),
            (0, SyntaxErrorKind::ExponentLeadingZero),
        ],
    );
}

#[test]
fn errors_locate_the_offending_source_text() {
    use SyntaxErrorKind as E;

    check_error_ranges(
        "x 1E+05",
        &[
            (2, 3, 4, E::UppercaseExponent),
            (2, 4, 5, E::ExponentPlusSign),
            (2, 5, 6, E::ExponentLeadingZero),
        ],
    );
    check_error_ranges(
        r#"Δ "é\q" ''"#,
        &[
            (2, 6, 8, E::UnknownEscape),
            (4, 11, 11, E::EmptyCharLiteral),
        ],
    );
    check_error_ranges("0123", &[(0, 0, 1, E::LeadingZero)]);
    check_error_ranges("1_", &[(0, 1, 2, E::MisplacedUnderscore)]);
    check_error_ranges("1u32", &[(0, 1, 4, E::UnknownSuffix)]);
    check_error_ranges("1e", &[(0, 1, 2, E::MissingExponent)]);
    check_error_ranges(r#""\uX""#, &[(0, 1, 3, E::MalformedUnicodeEscape)]);
    check_error_ranges(r#""\u{}""#, &[(0, 1, 5, E::MalformedUnicodeEscape)]);
    check_error_ranges(r#""\u{d800}""#, &[(0, 1, 9, E::InvalidUnicodeScalar)]);
    check_error_ranges("'éx'", &[(0, 3, 4, E::MoreThanOneChar)]);
    check_error_ranges(";", &[(0, 0, 1, E::UnknownPunctuation)]);
}

#[test]
fn leading_zeros_are_rejected() {
    check_errors("0123", &[(0, SyntaxErrorKind::LeadingZero)]);
    // The digit count ignores separators: `0_0` is padded, `0_` is not.
    check_errors("0_0", &[(0, SyntaxErrorKind::LeadingZero)]);
    check_errors("0_", &[(0, SyntaxErrorKind::MisplacedUnderscore)]);
    check_errors("0", &[]);
    check_errors("0.5", &[]);
    check_errors("0e5", &[]);
    check_errors("1.05", &[]);
}

#[test]
fn misplaced_underscores_are_rejected() {
    check_errors("1_000 1_000_000", &[]);
    check_errors("1_", &[(0, SyntaxErrorKind::MisplacedUnderscore)]);
    check_errors("1__0", &[(0, SyntaxErrorKind::MisplacedUnderscore)]);
    check_errors("1_.5", &[(0, SyntaxErrorKind::MisplacedUnderscore)]);
    check_errors("1e5_", &[(0, SyntaxErrorKind::MisplacedUnderscore)]);
}

#[test]
fn suffixes_are_rejected() {
    check_errors("1u32", &[(0, SyntaxErrorKind::UnknownSuffix)]);
    check_errors("x 1_5f", &[(2, SyntaxErrorKind::UnknownSuffix)]);
    // Base prefixes are not part of the language; `x…` is just a suffix.
    check_errors("0x1F", &[(0, SyntaxErrorKind::UnknownSuffix)]);
    check_errors("0b10", &[(0, SyntaxErrorKind::UnknownSuffix)]);
    check_errors("0x", &[(0, SyntaxErrorKind::UnknownSuffix)]);
}

#[test]
fn exponent_markers_are_lowercase_only() {
    check_errors("1e5", &[]);
    check_errors("1E5", &[(0, SyntaxErrorKind::UppercaseExponent)]);
    check_errors("1E-5", &[(0, SyntaxErrorKind::UppercaseExponent)]);
    // `1E` has both problems; the missing digits are the primary error.
    check_errors("1E", &[(0, SyntaxErrorKind::MissingExponent)]);
}

#[test]
fn broken_exponents_get_a_targeted_error() {
    check_errors("1e", &[(0, SyntaxErrorKind::MissingExponent)]);
    check_errors("2.5e", &[(0, SyntaxErrorKind::MissingExponent)]);
    // The raw token is just `1e`: the lexer declined `+x` as an exponent.
    check_errors("1e+x", &[(0, SyntaxErrorKind::MissingExponent)]);
    // After a real exponent, a trailing `e5` is an ordinary unknown suffix.
    check_errors("1e5e5", &[(0, SyntaxErrorKind::UnknownSuffix)]);
    check_errors("1.5e5f", &[(0, SyntaxErrorKind::UnknownSuffix)]);
}

#[test]
fn lexer_reported_tokens_get_no_validation_errors() {
    // Unterminated literals already carry a LexError.
    check_errors("\"a\\q", &[]);
    check_errors("'ab", &[]);
}

#[test]
fn valid_escapes_pass() {
    check_errors(r#""a\n\r\t\\\"\'\0b" '\n' '\u{1F600}'"#, &[]);
}

#[test]
fn unknown_escapes_are_reported() {
    check_errors(r#""a\qb""#, &[(0, SyntaxErrorKind::UnknownEscape)]);
    check_errors(
        r#""\q\q""#,
        &[
            (0, SyntaxErrorKind::UnknownEscape),
            (0, SyntaxErrorKind::UnknownEscape),
        ],
    );
}

#[test]
fn unicode_escape_validation() {
    check_errors(r#""\u{41}""#, &[]);
    check_errors(r#""\uX""#, &[(0, SyntaxErrorKind::MalformedUnicodeEscape)]);
    check_errors(r#""\u{}""#, &[(0, SyntaxErrorKind::MalformedUnicodeEscape)]);
    check_errors(
        r#""\u{1234567}""#,
        &[(0, SyntaxErrorKind::MalformedUnicodeEscape)],
    );
    check_errors(
        r#""\u{zz}""#,
        &[(0, SyntaxErrorKind::MalformedUnicodeEscape)],
    );
    check_errors(
        r#""\u{d800}""#,
        &[(0, SyntaxErrorKind::InvalidUnicodeScalar)],
    );
    check_errors(
        r#""\u{110000}""#,
        &[(0, SyntaxErrorKind::InvalidUnicodeScalar)],
    );
}

#[test]
fn char_content_validation() {
    check_errors("'a'", &[]);
    check_errors(r"'\''", &[]);
    check_errors("''", &[(0, SyntaxErrorKind::EmptyCharLiteral)]);
    check_errors("'ab'", &[(0, SyntaxErrorKind::MoreThanOneChar)]);
    check_errors(r"'\u{41}b'", &[(0, SyntaxErrorKind::MoreThanOneChar)]);
    // A bad escape is one piece: no cascading length error.
    check_errors(r"'\q'", &[(0, SyntaxErrorKind::UnknownEscape)]);
}
