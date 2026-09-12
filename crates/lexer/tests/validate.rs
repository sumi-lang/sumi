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
    check_errors("0 123 9999", &[]);
}

#[test]
fn unused_punctuation_has_an_error() {
    // Reported here, where every later phase can treat an `Error` token as
    // already diagnosed.
    check_errors(";", &[(0, LexErrorKind::UnknownPunctuation)]);
    // A quote mark opens nothing: there are no character literals.
    check_errors("'", &[(0, LexErrorKind::UnknownPunctuation)]);
}

#[test]
fn number_errors_report_in_source_order() {
    check_errors(
        "01u32",
        &[
            (0, LexErrorKind::LeadingZero),
            (0, LexErrorKind::UnknownSuffix),
        ],
    );
}

#[test]
fn number_canonicalization_strips_leading_zeros_and_preserves_suffixes() {
    for (source, expected) in [
        ("", None),
        ("name", None),
        ("0123", Some("123")),
        ("000", Some("0")),
        ("0010", Some("10")),
        ("01u32", Some("1u32")),
        ("01_000", Some("1_000")),
        ("00e5", Some("0e5")),
        ("0", None),
        ("10", None),
        ("1u32", None),
        ("1_000", None),
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
    for source in ["0123", "000", "0010", "01u32", "01_000", "00e5"] {
        let replacement = canonicalize_number_literal(source).expect("source is noncanonical");
        let lexed = lex(&replacement).expect("replacement fits in u32");
        assert!(
            lexed
                .errors()
                .iter()
                .all(|error| error.kind != LexErrorKind::LeadingZero)
        );
    }
}

#[test]
fn errors_locate_the_offending_source_text() {
    use LexErrorKind as E;

    check_error_ranges(
        "x 01u32",
        &[(2, 2, 3, E::LeadingZero), (2, 4, 7, E::UnknownSuffix)],
    );
    check_error_ranges(
        r#"Δ "é\q""#,
        &[(0, 0, 2, E::UnknownCharacter), (2, 6, 8, E::UnknownEscape)],
    );
    check_error_ranges("0123", &[(0, 0, 1, E::LeadingZero)]);
    check_error_ranges("1u32", &[(0, 1, 4, E::UnknownSuffix)]);
    check_error_ranges(";", &[(0, 0, 1, E::UnknownPunctuation)]);
}

#[test]
fn leading_zeros_are_rejected() {
    check_errors("0123", &[(0, LexErrorKind::LeadingZero)]);
    check_errors("00", &[(0, LexErrorKind::LeadingZero)]);
    check_errors("0", &[]);
    // A suffix does not count as padding: `0x` is only a suffix.
    check_errors("0x", &[(0, LexErrorKind::UnknownSuffix)]);
}

#[test]
fn suffixes_are_rejected() {
    check_errors("1u32", &[(0, LexErrorKind::UnknownSuffix)]);
    check_errors("x 15f", &[(2, LexErrorKind::UnknownSuffix)]);
    // Base prefixes are not part of the language; `x…` is just a suffix.
    check_errors("0x1F", &[(0, LexErrorKind::UnknownSuffix)]);
    check_errors("0b10", &[(0, LexErrorKind::UnknownSuffix)]);
    // Neither are digit separators or exponents: `_000` and `e5` are
    // suffixes too, and `.5` is two tokens after the integer.
    check_errors("1_000", &[(0, LexErrorKind::UnknownSuffix)]);
    check_errors("1e5", &[(0, LexErrorKind::UnknownSuffix)]);
    check_errors("1.5", &[]);
}

#[test]
fn unterminated_literals_get_only_the_scanner_error() {
    check_errors("\"a\\q", &[(0, LexErrorKind::UnterminatedString)]);
}

#[test]
fn valid_escapes_pass() {
    check_errors(r#""a\n\r\t\\\"\0b""#, &[]);
    // A quote needs no escape in a `"…"` literal: there is no `\'`.
    check_errors(r#""\'""#, &[(0, LexErrorKind::UnknownEscape)]);
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
fn line_literals_get_only_their_unterminated_error() {
    check_errors(
        "\"a\\\nb\"",
        &[
            (0, LexErrorKind::UnterminatedString),
            (3, LexErrorKind::UnterminatedString),
        ],
    );
}

#[test]
fn every_unknown_escape_of_a_literal_is_reported() {
    check_error_ranges(
        "\"\\q{x}\\p\"",
        &[
            (0, 1, 3, LexErrorKind::UnknownEscape),
            (0, 6, 8, LexErrorKind::UnknownEscape),
        ],
    );
}
