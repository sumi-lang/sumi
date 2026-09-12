use sumi_lexer::{LexError, LexErrorKind, RawIdx, lex};
use sumi_text::{TextRange, TextSize};

fn error(token: u32, start: u32, end: u32, kind: LexErrorKind) -> LexError {
    LexError {
        token: RawIdx::new(token),
        range: TextRange::new(TextSize::new(start), TextSize::new(end)),
        kind,
    }
}

/// Lex `source`, assert the partition invariants every lex must uphold, and
/// render one line per token: `RawKind start..end "text"` plus any flags.
fn dump(source: &str) -> Vec<String> {
    let file = lex(source).expect("test sources fit in u32");

    let mut concatenated = String::new();
    for index in file.indices() {
        let range = file.range(index);
        assert!(range.start() < range.end(), "token {index:?} is empty");
        assert!(source.is_char_boundary(range.start().to_usize()));
        assert!(source.is_char_boundary(range.end().to_usize()));

        if index == RawIdx::new(0) {
            assert_eq!(range.start().to_u32(), 0, "first token must start at 0");
        } else {
            assert_eq!(
                range.start(),
                file.range(index - 1).end(),
                "token {index:?} is not contiguous"
            );
        }

        concatenated.push_str(file.text(source, index));
    }
    assert_eq!(concatenated, source, "tokens must reproduce the source");

    if let Some(last) = file.end().checked_sub(1) {
        assert_eq!(file.range(last).end(), file.source_len());
    }
    for error in file.errors() {
        assert!(error.token < file.end());
    }

    file.indices()
        .map(|index| {
            let range = file.range(index);
            let flags = file.flags(index);
            let mut line = format!(
                "{:?} {}..{} {:?}",
                file.raw_kind(index),
                range.start().to_u32(),
                range.end().to_u32(),
                file.text(source, index),
            );
            if !flags.is_empty() {
                line.push_str(&format!(" {flags:?}"));
            }
            line
        })
        .collect()
}

#[track_caller]
fn check(source: &str, expected: &[&str]) {
    assert_eq!(dump(source), expected, "for source {source:?}");
}

#[test]
fn empty_source_has_no_tokens() {
    check("", &[]);
    assert!(lex("").unwrap().is_empty());
}

#[test]
fn keywords_lex_as_plain_idents() {
    check(
        "fn map",
        &[
            r#"Ident 0..2 "fn""#,
            r#"HorizontalSpace 2..3 " ""#,
            r#"Ident 3..6 "map""#,
        ],
    );
}

#[test]
fn compound_punct_lexes_as_single_chars() {
    check(
        "x >>= 2",
        &[
            r#"Ident 0..1 "x""#,
            r#"HorizontalSpace 1..2 " ""#,
            r#"Punct 2..3 ">""#,
            r#"Punct 3..4 ">""#,
            r#"Punct 4..5 "=""#,
            r#"HorizontalSpace 5..6 " ""#,
            r#"Number 6..7 "2""#,
        ],
    );
}

#[test]
fn ascii_punct_lexes_individually() {
    check(
        "(;)",
        &[
            r#"Punct 0..1 "(""#,
            r#"Punct 1..2 ";""#,
            r#"Punct 2..3 ")""#,
        ],
    );
}

#[test]
fn horizontal_space_lexes_as_one_run() {
    check(
        "  \t x",
        &[r#"HorizontalSpace 0..4 "  \t ""#, r#"Ident 4..5 "x""#],
    );
}

#[test]
fn underscore_starts_idents() {
    check(
        "_ _x",
        &[
            r#"Ident 0..1 "_""#,
            r#"HorizontalSpace 1..2 " ""#,
            r#"Ident 2..4 "_x""#,
        ],
    );
}

#[test]
fn identifiers_are_ascii() {
    // A non-ASCII letter is no part of a name: it lexes alone, as any
    // character without a role does.
    check(
        "Δx aé",
        &[
            r#"Unknown 0..2 "Δ""#,
            r#"Ident 2..3 "x""#,
            r#"HorizontalSpace 3..4 " ""#,
            r#"Ident 4..5 "a""#,
            r#"Unknown 5..7 "é""#,
        ],
    );
    assert_eq!(
        lex("Δx aé").unwrap().errors(),
        &[
            error(0, 0, 2, LexErrorKind::UnknownCharacter),
            error(4, 5, 7, LexErrorKind::UnknownCharacter),
        ],
    );
}

#[test]
fn non_ascii_non_ident_is_unknown() {
    check(
        "a€b",
        &[
            r#"Ident 0..1 "a""#,
            r#"Unknown 1..4 "€""#,
            r#"Ident 4..5 "b""#,
        ],
    );
    assert_eq!(
        lex("a€b").unwrap().errors(),
        &[error(1, 1, 4, LexErrorKind::UnknownCharacter)],
    );
}

#[test]
fn control_chars_are_unknown() {
    check("\u{1}", &[r#"Unknown 0..1 "\u{1}""#]);
    assert_eq!(
        lex("\u{1}").unwrap().errors(),
        &[error(0, 0, 1, LexErrorKind::UnknownCharacter)],
    );
}

#[test]
fn a_byte_order_mark_is_an_unknown_character() {
    // Even at byte zero: a source is UTF-8 without a signature.
    let source = "\u{feff}x";
    check(source, &[r#"Unknown 0..3 "\u{feff}""#, r#"Ident 3..4 "x""#]);
    assert_eq!(
        lex(source).unwrap().errors(),
        &[error(0, 0, 3, LexErrorKind::UnknownCharacter)],
    );
}

#[test]
fn newline_variants() {
    check(
        "a\nb\r\nc",
        &[
            r#"Ident 0..1 "a""#,
            r#"Newline 1..2 "\n""#,
            r#"Ident 2..3 "b""#,
            r#"Newline 3..5 "\r\n""#,
            r#"Ident 5..6 "c""#,
        ],
    );
}

#[test]
fn consecutive_newlines_stay_separate() {
    check("\n\n", &[r#"Newline 0..1 "\n""#, r#"Newline 1..2 "\n""#]);
}

#[test]
fn lone_carriage_return_is_an_error() {
    check("\r", &[r#"Newline 0..1 "\r" TokenFlags(LONE_CR)"#]);
    assert_eq!(
        lex("\r").unwrap().errors(),
        &[error(0, 0, 1, LexErrorKind::LoneCarriageReturn)],
    );
}

#[test]
fn line_comments_end_at_newline() {
    check(
        "// c\nx",
        &[
            r#"LineComment 0..4 "// c""#,
            r#"Newline 4..5 "\n""#,
            r#"Ident 5..6 "x""#,
        ],
    );
}

#[test]
fn line_comments_have_no_flavors() {
    check("//", &[r#"LineComment 0..2 "//""#]);
    check("/// d", &[r#"LineComment 0..5 "/// d""#]);
    check("//! d", &[r#"LineComment 0..5 "//! d""#]);
    check("//// d", &[r#"LineComment 0..6 "//// d""#]);
}

#[test]
fn slash_star_is_just_punctuation() {
    // Sumi has line comments only; there is no block-comment syntax.
    check(
        "/* x",
        &[
            r#"Punct 0..1 "/""#,
            r#"Punct 1..2 "*""#,
            r#"HorizontalSpace 2..3 " ""#,
            r#"Ident 3..4 "x""#,
        ],
    );
}

#[test]
fn integer_shapes() {
    check(
        "0 123",
        &[
            r#"Number 0..1 "0""#,
            r#"HorizontalSpace 1..2 " ""#,
            r#"Number 2..5 "123""#,
        ],
    );
}

#[test]
fn a_dot_never_continues_a_number() {
    check(
        "1.5",
        &[
            r#"Number 0..1 "1""#,
            r#"Punct 1..2 ".""#,
            r#"Number 2..3 "5""#,
        ],
    );
    check(
        "1.foo",
        &[
            r#"Number 0..1 "1""#,
            r#"Punct 1..2 ".""#,
            r#"Ident 2..5 "foo""#,
        ],
    );
    check("1.", &[r#"Number 0..1 "1""#, r#"Punct 1..2 ".""#]);
}

#[test]
fn number_suffixes_attach() {
    check(
        "1u32",
        &[r#"Number 0..4 "1u32" TokenFlags(MALFORMED_NUMBER)"#],
    );
    // Separators and exponents are suffixes too: `_` and `e` continue an
    // identifier, and there are no floats.
    check(
        "1_000",
        &[r#"Number 0..5 "1_000" TokenFlags(MALFORMED_NUMBER)"#],
    );
    check(
        "1e-5",
        &[
            r#"Number 0..2 "1e" TokenFlags(MALFORMED_NUMBER)"#,
            r#"Punct 2..3 "-""#,
            r#"Number 3..4 "5""#,
        ],
    );
    // With no base prefixes in the language, `x1F` is just a suffix.
    check(
        "0x1F",
        &[r#"Number 0..4 "0x1F" TokenFlags(MALFORMED_NUMBER)"#],
    );
    assert_eq!(
        lex("0x1F").unwrap().errors(),
        &[error(0, 1, 4, LexErrorKind::UnknownSuffix)],
    );
}

#[test]
fn string_shapes() {
    check(r#""abc""#, &[r#"String 0..5 "\"abc\"""#]);
}

#[test]
fn line_literals_end_at_the_line() {
    // A literal never crosses a line break: what follows lexes as usual,
    // and a backslash before the break does not carry it over.
    check(
        "\"a\nb\"",
        &[
            r#"String 0..2 "\"a" TokenFlags(UNTERMINATED)"#,
            r#"Newline 2..3 "\n""#,
            r#"Ident 3..4 "b""#,
            r#"String 4..5 "\"" TokenFlags(UNTERMINATED)"#,
        ],
    );
    assert_eq!(
        lex("\"a\nb\"").unwrap().errors(),
        &[
            error(0, 0, 2, LexErrorKind::UnterminatedString),
            error(3, 4, 5, LexErrorKind::UnterminatedString),
        ],
    );
    check(
        "\"a\\\nb",
        &[
            r#"String 0..3 "\"a\\" TokenFlags(UNTERMINATED | HAS_ESCAPE)"#,
            r#"Newline 3..4 "\n""#,
            r#"Ident 4..5 "b""#,
        ],
    );
}

#[test]
fn string_escapes_are_flagged() {
    check(
        r#""a\"b""#,
        &[r#"String 0..6 "\"a\\\"b\"" TokenFlags(HAS_ESCAPE)"#],
    );
}

#[test]
fn unterminated_string() {
    check("\"ab", &[r#"String 0..3 "\"ab" TokenFlags(UNTERMINATED)"#]);
    assert_eq!(
        lex("\"ab").unwrap().errors(),
        &[error(0, 0, 3, LexErrorKind::UnterminatedString)],
    );
}

#[test]
fn r_without_quote_is_an_ident() {
    check("r", &[r#"Ident 0..1 "r""#]);
    check("raw", &[r#"Ident 0..3 "raw""#]);
    check(
        "r#x",
        &[
            r#"Ident 0..1 "r""#,
            r##"Punct 1..2 "#""##,
            r#"Ident 2..3 "x""#,
        ],
    );
}

#[test]
fn clean_source_has_no_errors() {
    let source = "fn main() {\n    x >>= 2\n}\n";
    assert_eq!(lex(source).unwrap().errors(), &[]);
}

#[test]
fn partition_smoke() {
    let source = "fn main() {\r\n\tlet s = \"raw\"; // trailing\n\t\"str\" 25 0xFF\n}\n";
    dump(source);
}
