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

#[test]
fn block_string_layout_is_checked() {
    check_errors("\"\"\"\n  a\n  \"\"\"", &[]);
    check_errors("\"\"\"\n\"\"\"", &[]);
    // Blank lines of any whitespace count as empty.
    check_errors("\"\"\"\n  a\n\n\t\n  b\n  \"\"\"", &[]);
    check_error_ranges(
        "\"\"\"a\n  \"\"\"",
        &[(0, 3, 4, LexErrorKind::BlockStringOpenerContent)],
    );
    check_error_ranges(
        "\"\"\" \n  a\"\"\"",
        &[(0, 8, 11, LexErrorKind::BlockStringCloserContent)],
    );
    check_errors(
        "\"\"\"a\"\"\"",
        &[
            (0, LexErrorKind::BlockStringOpenerContent),
            (0, LexErrorKind::BlockStringCloserContent),
        ],
    );
    check_errors(
        "\"\"\"\"\"\"",
        &[(0, LexErrorKind::BlockStringCloserContent)],
    );
    check_error_ranges(
        "\"\"\"\n  a\n b\n  \"\"\"",
        &[(0, 8, 9, LexErrorKind::BlockStringIndentation)],
    );
    // Indentation is compared byte for byte: a tab is not two spaces.
    check_errors(
        "\"\"\"\n  a\n\t\"\"\"",
        &[(0, LexErrorKind::BlockStringIndentation)],
    );
    // A line with no indentation at all is reported at its start.
    check_error_ranges(
        "\"\"\"\n  a\nb\n  \"\"\"",
        &[(0, 8, 8, LexErrorKind::BlockStringIndentation)],
    );
    // Raw multi-line literals share the layout rules.
    check_errors("r\"\"\"\n  \\d\n  \"\"\"", &[]);
    check_errors(
        "r\"\"\"x\n  \"\"\"",
        &[(0, LexErrorKind::BlockStringOpenerContent)],
    );
}

#[test]
fn block_string_escapes_join_lines() {
    check_errors("\"\"\"\n  a\\\n  b\n  \"\"\"", &[]);
    check_errors("\"\"\"\n  a\\\r\n  b\n  \"\"\"", &[]);
    check_errors("\"\"\"\n  \\\"\"\"\n  \"\"\"", &[]);
    check_errors("\"\"\"\n  \\u{41}\n  \"\"\"", &[]);
    check_error_ranges(
        "\"\"\"\n  \\q\n  \"\"\"",
        &[(0, 6, 8, LexErrorKind::UnknownEscape)],
    );
    // An unterminated one gets only its own error.
    check_errors(
        "\"\"\"x\n \\q",
        &[(0, LexErrorKind::UnterminatedBlockString)],
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
    check_errors("r\"a\nb", &[(0, LexErrorKind::UnterminatedRawString)]);
}

#[test]
fn holes_left_open_are_reported_at_their_brace() {
    check_error_ranges("\"a {b\nc", &[(1, 3, 4, LexErrorKind::UnclosedHole)]);
    check_error_ranges("\"{a}\n", &[(0, 0, 1, LexErrorKind::UnterminatedString)]);
    // The end of input leaves a hole open and a `"""` literal unterminated,
    // the latter reported at its opener as a whole one is.
    check_error_ranges(
        "\"\"\"\n  {x",
        &[
            (0, 0, 3, LexErrorKind::UnterminatedBlockString),
            (1, 6, 7, LexErrorKind::UnclosedHole),
        ],
    );
    check_error_ranges(
        "\"\"\"\n  {x}",
        &[(0, 0, 3, LexErrorKind::UnterminatedBlockString)],
    );
}

#[test]
fn escapes_and_layout_are_judged_over_the_parts_of_a_literal() {
    // Each part of a `"…"` literal is judged on its own text.
    check_error_ranges(
        "\"\\q{x}\\p\"",
        &[
            (0, 1, 3, LexErrorKind::UnknownEscape),
            (4, 6, 8, LexErrorKind::UnknownEscape),
        ],
    );
    // A `"""` literal is judged whole once its end arrives, with the
    // holes' code left out; an error lands on the part it begins in.
    check_error_ranges(
        "\"\"\"\n  \\q{x}\n  \"\"\"",
        &[(0, 6, 8, LexErrorKind::UnknownEscape)],
    );
    check_error_ranges(
        "\"\"\"\n{x}\n \"\"\"",
        &[(1, 4, 4, LexErrorKind::BlockStringIndentation)],
    );
    check_errors("\"\"\"\n  {x}\n  \"\"\"", &[]);
}

#[test]
fn validation_over_many_interpolated_block_strings_is_linear() {
    let source = "\"\"\"\n  {x}\n  \"\"\"\n".repeat(50_000);
    check_errors(&source, &[]);
}
