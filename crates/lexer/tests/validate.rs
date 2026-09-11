//! Token-local validity: the errors collected before `lex` returns.

use sumi_lexer::{LexErrorKind, SyntaxKind, canonicalize_number_literal, lex};

#[test]
fn normalized_keywords_are_invalid_identifiers_not_keywords() {
    for (source, keyword) in [
        ("ｅｌｓｅ", SyntaxKind::ElseKw),
        ("falſe", SyntaxKind::FalseKw),
        ("ｆｎ", SyntaxKind::FnKw),
        ("ｉｆ", SyntaxKind::IfKw),
        ("ｌｅｔ", SyntaxKind::LetKw),
        ("ｍｕｔ", SyntaxKind::MutKw),
        ("ｒｅｔｕｒｎ", SyntaxKind::ReturnKw),
        ("ｔｒｕｅ", SyntaxKind::TrueKw),
    ] {
        let lexed = lex(source).unwrap();
        let error = &lexed.errors()[0];
        assert_eq!(lexed.errors().len(), 1);
        assert_eq!(error.kind, LexErrorKind::ReservedIdentifier(keyword));
        assert_eq!(lexed.kind(error.token), SyntaxKind::Ident);
        assert_eq!(lexed.text(source, error.token), source);
        assert_eq!(error.range, lexed.range(error.token));
    }
    for source in [
        "true",
        "false",
        "fn",
        "_",
        "ｉｎｔ",
        "ﬀ",
        "é",
        "e\u{301}",
        "ｔｒｕｅ_value",
        "True",
    ] {
        check_errors(source, &[]);
    }
    check_errors("// ｔｒｕｅ\n\"ｆｎ\"", &[]);
}

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
        ("01Δ", Some("1Δ")),
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
    for source in ["0123", "000", "0010", "01u32", "01Δ", "01_000", "00e5"] {
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
    check_error_ranges(r#"Δ "é\q""#, &[(2, 6, 8, E::UnknownEscape)]);
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
}

#[test]
fn block_string_escapes_join_lines() {
    check_errors("\"\"\"\n  a\\\n  b\n  \"\"\"", &[]);
    check_errors("\"\"\"\n  a\\\r\n  b\n  \"\"\"", &[]);
    check_errors("\"\"\"\n  \\\"\"\"\n  \"\"\"", &[]);
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
fn block_validation_keeps_error_phase_order_across_mixed_line_endings() {
    // All errors belong to one token, so stable token sorting must preserve
    // line-ending errors before layout errors before escape errors.
    check_error_ranges(
        "\"\"\"x\r\n a\\q\r b\\p\r\n  \"\"\"",
        &[
            (0, 10, 11, LexErrorKind::LoneCarriageReturn),
            (0, 3, 4, LexErrorKind::BlockStringOpenerContent),
            (0, 6, 7, LexErrorKind::BlockStringIndentation),
            (0, 11, 12, LexErrorKind::BlockStringIndentation),
            (0, 8, 10, LexErrorKind::UnknownEscape),
            (0, 13, 15, LexErrorKind::UnknownEscape),
        ],
    );
    for newline in ["\n", "\r\n"] {
        check_errors(&format!("\"\"\"{newline}\t\"\"\""), &[]);
        check_errors(&format!("\"\"\"{newline}\tα{newline}\t\"\"\""), &[]);
    }
}

#[test]
fn block_escapes_exclude_hole_code_and_resume_after_each_hole() {
    let source = "\"\"\"\n  {\"\\q\"}\\p{x}\\z\n  \"\"\"";
    let lexed = lex(source).unwrap();
    let errors: Vec<_> = lexed
        .errors()
        .iter()
        .map(|error| {
            let range = error.range;
            (
                error.kind,
                &source[range.start().to_usize()..range.end().to_usize()],
            )
        })
        .collect();
    // The hole's literal reports its own `\q` once; the block's text scan
    // does not see it again.
    assert_eq!(
        errors,
        [
            (LexErrorKind::UnknownEscape, "\\q"),
            (LexErrorKind::UnknownEscape, "\\p"),
            (LexErrorKind::UnknownEscape, "\\z"),
        ]
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
