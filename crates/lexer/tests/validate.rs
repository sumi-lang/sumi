//! Token-local validity: the errors collected before `lex` returns.

use sumi_lexer::{LexErrorKind, canonicalize_number_literal, lex};

#[track_caller]
fn check_errors(source: &str, expected: &[(u32, LexErrorKind)]) {
    let lexed = lex(source).expect("test sources fit in u32");
    for error in lexed.errors() {
        let token = lexed.range(error.token);
        assert!(token.start() <= error.range.start());
        assert!(error.range.end() <= token.end());
        assert!(source.is_char_boundary(error.range.start().to_usize()));
        assert!(source.is_char_boundary(error.range.end().to_usize()));
    }
    let actual: Vec<(u32, LexErrorKind)> = lexed
        .errors()
        .iter()
        .map(|error| (error.token.to_u32(), error.kind))
        .collect();
    assert_eq!(actual, expected, "for source {source:?}");
}

#[track_caller]
fn check_error_ranges(source: &str, expected: &[(u32, u32, u32, LexErrorKind)]) {
    let lexed = lex(source).expect("test sources fit in u32");
    let actual: Vec<_> = lexed
        .errors()
        .iter()
        .map(|error| {
            (
                error.token.to_u32(),
                error.range.start().to_u32(),
                error.range.end().to_u32(),
                error.kind,
            )
        })
        .collect();
    assert_eq!(actual, expected, "for source {source:?}");
}

#[test]
fn clean_sources_have_no_errors() {
    check_errors("", &[]);
    check_errors("( ) { } , : . = < > ! + - * / % & |", &[]);
    check_errors("0 123 1_000 1.5 1e5 2.5e-3", &[]);
}

#[test]
fn unused_punctuation_has_an_error() {
    // Reported here, where every later phase can treat an `Error` token as
    // already diagnosed.
    check_errors(";", &[(0, LexErrorKind::UnknownPunctuation)]);
}

#[test]
fn exponent_plus_and_padding_are_rejected() {
    check_errors("1e+5", &[(0, LexErrorKind::ExponentPlusSign)]);
    check_errors("1e-5", &[]);
    check_errors("1e05", &[(0, LexErrorKind::ExponentLeadingZero)]);
    check_errors("1e-05", &[(0, LexErrorKind::ExponentLeadingZero)]);
    check_errors("1e0", &[]);
}

#[test]
fn multiple_number_errors_report_in_source_order() {
    check_errors(
        "1E+05",
        &[
            (0, LexErrorKind::UppercaseExponent),
            (0, LexErrorKind::ExponentPlusSign),
            (0, LexErrorKind::ExponentLeadingZero),
        ],
    );
}

#[test]
fn number_canonicalization_repairs_spelling_and_preserves_suffixes() {
    for (source, expected) in [
        ("", None),
        ("name", None),
        ("0123", Some("123")),
        ("000", Some("0")),
        ("0_0", Some("0")),
        ("01_000", Some("1_000")),
        ("00_0.50", Some("0.50")),
        ("1__0", Some("10")),
        ("1_.5", Some("1.5")),
        ("1E+05", Some("1e5")),
        ("1e-00_5", Some("1e-5")),
        ("01u32", Some("1u32")),
        ("01Δ", Some("1Δ")),
        ("01E", Some("1E")),
        ("1E", None),
        ("1u32", None),
        ("1_000.50e-5", None),
    ] {
        assert_eq!(
            canonicalize_number_literal(source).as_deref(),
            expected,
            "canonicalization of {source:?}"
        );
    }
}

#[test]
fn canonicalized_numbers_have_no_remaining_canonicalization_errors() {
    for source in [
        "0123", "000", "0_0", "01_000", "00_0.50", "1__0", "1_.5", "1E+05", "1e-00_5", "01u32",
        "01E",
    ] {
        let replacement = canonicalize_number_literal(source).expect("source is noncanonical");
        let lexed = lex(&replacement).expect("replacement fits in u32");
        assert!(lexed.errors().iter().all(|error| {
            !matches!(
                error.kind,
                LexErrorKind::LeadingZero
                    | LexErrorKind::MisplacedUnderscore
                    | LexErrorKind::UppercaseExponent
                    | LexErrorKind::ExponentPlusSign
                    | LexErrorKind::ExponentLeadingZero
            )
        }));
    }
}

#[test]
fn errors_locate_the_offending_source_text() {
    use LexErrorKind as E;

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
    check_errors("0123", &[(0, LexErrorKind::LeadingZero)]);
    // The digit count ignores separators: `0_0` is padded, `0_` is not.
    check_errors("0_0", &[(0, LexErrorKind::LeadingZero)]);
    check_errors("0_", &[(0, LexErrorKind::MisplacedUnderscore)]);
    check_errors("0", &[]);
    check_errors("0.5", &[]);
    check_errors("0e5", &[]);
    check_errors("1.05", &[]);
}

#[test]
fn misplaced_underscores_are_rejected() {
    check_errors("1_000 1_000_000", &[]);
    check_errors("1_", &[(0, LexErrorKind::MisplacedUnderscore)]);
    check_errors("1__0", &[(0, LexErrorKind::MisplacedUnderscore)]);
    check_errors("1_.5", &[(0, LexErrorKind::MisplacedUnderscore)]);
    check_errors("1e5_", &[(0, LexErrorKind::MisplacedUnderscore)]);
}

#[test]
fn suffixes_are_rejected() {
    check_errors("1u32", &[(0, LexErrorKind::UnknownSuffix)]);
    check_errors("x 1_5f", &[(2, LexErrorKind::UnknownSuffix)]);
    // Base prefixes are not part of the language; `x…` is just a suffix.
    check_errors("0x1F", &[(0, LexErrorKind::UnknownSuffix)]);
    check_errors("0b10", &[(0, LexErrorKind::UnknownSuffix)]);
    check_errors("0x", &[(0, LexErrorKind::UnknownSuffix)]);
}

#[test]
fn exponent_markers_are_lowercase_only() {
    check_errors("1e5", &[]);
    check_errors("1E5", &[(0, LexErrorKind::UppercaseExponent)]);
    check_errors("1E-5", &[(0, LexErrorKind::UppercaseExponent)]);
    // `1E` has both problems; the missing digits are the primary error.
    check_errors("1E", &[(0, LexErrorKind::MissingExponent)]);
}

#[test]
fn broken_exponents_get_a_targeted_error() {
    check_errors("1e", &[(0, LexErrorKind::MissingExponent)]);
    check_errors("2.5e", &[(0, LexErrorKind::MissingExponent)]);
    // The raw token is just `1e`: the lexer declined `+x` as an exponent.
    check_errors("1e+x", &[(0, LexErrorKind::MissingExponent)]);
    // After a real exponent, a trailing `e5` is an ordinary unknown suffix.
    check_errors("1e5e5", &[(0, LexErrorKind::UnknownSuffix)]);
    check_errors("1.5e5f", &[(0, LexErrorKind::UnknownSuffix)]);
}

#[test]
fn unterminated_literals_get_only_the_scanner_error() {
    check_errors("\"a\\q", &[(0, LexErrorKind::UnterminatedString)]);
    check_errors("'ab", &[(0, LexErrorKind::UnterminatedChar)]);
}

#[test]
fn valid_escapes_pass() {
    check_errors(r#""a\n\r\t\\\"\'\0b" '\n' '\u{1F600}'"#, &[]);
}

#[test]
fn unknown_escapes_are_reported() {
    check_errors(r#""a\qb""#, &[(0, LexErrorKind::UnknownEscape)]);
    check_errors(
        r#""\q\q""#,
        &[
            (0, LexErrorKind::UnknownEscape),
            (0, LexErrorKind::UnknownEscape),
        ],
    );
}

#[test]
fn unicode_escape_validation() {
    check_errors(r#""\u{41}""#, &[]);
    check_errors(r#""\uX""#, &[(0, LexErrorKind::MalformedUnicodeEscape)]);
    check_errors(r#""\u{}""#, &[(0, LexErrorKind::MalformedUnicodeEscape)]);
    check_errors(
        r#""\u{1234567}""#,
        &[(0, LexErrorKind::MalformedUnicodeEscape)],
    );
    check_errors(r#""\u{zz}""#, &[(0, LexErrorKind::MalformedUnicodeEscape)]);
    check_errors(r#""\u{d800}""#, &[(0, LexErrorKind::InvalidUnicodeScalar)]);
    check_errors(
        r#""\u{110000}""#,
        &[(0, LexErrorKind::InvalidUnicodeScalar)],
    );
}

#[test]
fn char_content_validation() {
    check_errors("'a'", &[]);
    check_errors(r"'\''", &[]);
    check_errors("''", &[(0, LexErrorKind::EmptyCharLiteral)]);
    check_errors("'ab'", &[(0, LexErrorKind::MoreThanOneChar)]);
    check_errors(r"'\u{41}b'", &[(0, LexErrorKind::MoreThanOneChar)]);
    // A bad escape is one piece: no cascading length error.
    check_errors(r"'\q'", &[(0, LexErrorKind::UnknownEscape)]);
}
