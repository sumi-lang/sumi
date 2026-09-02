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
fn unicode_idents_use_xid() {
    check(
        "Δx μ2",
        &[
            r#"Ident 0..3 "Δx""#,
            r#"HorizontalSpace 3..4 " ""#,
            r#"Ident 4..7 "μ2""#,
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
fn bom_at_byte_zero() {
    check(
        "\u{feff}x",
        &[r#"Bom 0..3 "\u{feff}""#, r#"Ident 3..4 "x""#],
    );
    assert_eq!(lex("\u{feff}x").unwrap().errors(), &[]);
}

#[test]
fn bom_elsewhere_is_unknown_with_error() {
    let source = "x\u{feff}";
    check(source, &[r#"Ident 0..1 "x""#, r#"Unknown 1..4 "\u{feff}""#]);
    assert_eq!(
        lex(source).unwrap().errors(),
        &[error(1, 1, 4, LexErrorKind::MisplacedBom)],
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
fn line_comment_doc_flavors() {
    check("//", &[r#"LineComment 0..2 "//""#]);
    check(
        "/// d",
        &[r#"LineComment 0..5 "/// d" TokenFlags(DOC_OUTER)"#],
    );
    check(
        "//! d",
        &[r#"LineComment 0..5 "//! d" TokenFlags(DOC_INNER)"#],
    );
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
        "0 123 1_000",
        &[
            r#"Number 0..1 "0""#,
            r#"HorizontalSpace 1..2 " ""#,
            r#"Number 2..5 "123""#,
            r#"HorizontalSpace 5..6 " ""#,
            r#"Number 6..11 "1_000""#,
        ],
    );
}

#[test]
fn float_shapes() {
    check("1.5", &[r#"Number 0..3 "1.5""#]);
    check("2.5e-3", &[r#"Number 0..6 "2.5e-3""#]);
    check("1e5", &[r#"Number 0..3 "1e5""#]);
    // Boundaries must not depend on marker case; collection rejects `E`.
    check(
        "1E-5",
        &[r#"Number 0..4 "1E-5" TokenFlags(MALFORMED_NUMBER)"#],
    );
}

#[test]
fn dot_continues_a_number_only_before_a_digit() {
    check(
        "1..2",
        &[
            r#"Number 0..1 "1""#,
            r#"Punct 1..2 ".""#,
            r#"Punct 2..3 ".""#,
            r#"Number 3..4 "2""#,
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
    check("1e", &[r#"Number 0..2 "1e" TokenFlags(MALFORMED_NUMBER)"#]);
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
    check(
        "r\"a\r\nb",
        &[
            r#"RawString 0..3 "r\"a" TokenFlags(UNTERMINATED)"#,
            r#"Newline 3..5 "\r\n""#,
            r#"Ident 5..6 "b""#,
        ],
    );
}

/// The dump line of a source that is one multi-line literal.
fn block(source: &str, raw: &str, flags: &str) -> String {
    format!("{raw} 0..{} {source:?}{flags}", source.len())
}

#[test]
fn block_string_shapes() {
    let source = "\"\"\"\n  a \"b\"\n  \"\"\"";
    check(source, &[&block(source, "BlockString", "")]);
    assert_eq!(lex(source).unwrap().errors(), &[]);

    // An escaped quote keeps the literal open.
    let source = "\"\"\"\n  \\\"\"\"\n  \"\"\"";
    check(
        source,
        &[&block(source, "BlockString", " TokenFlags(HAS_ESCAPE)")],
    );

    let source = "\"\"\"\n\"\"\"";
    check(source, &[&block(source, "BlockString", "")]);

    // The first `"""` closes, wherever it sits; layout is judged after.
    check(
        "\"\"\"a\"\"\"b",
        &[r#"BlockString 0..7 "\"\"\"a\"\"\"""#, r#"Ident 7..8 "b""#],
    );
}

#[test]
fn unterminated_block_string_runs_to_the_end() {
    let source = "\"\"\"\nabc\n";
    check(
        source,
        &[&block(source, "BlockString", " TokenFlags(UNTERMINATED)")],
    );
    assert_eq!(
        lex(source).unwrap().errors(),
        &[error(0, 0, 3, LexErrorKind::UnterminatedBlockString)],
    );
}

#[test]
fn raw_block_string_shapes() {
    let source = "r\"\"\"\n  \\d \"q\"\n  \"\"\"";
    check(source, &[&block(source, "RawBlockString", "")]);
    assert_eq!(lex(source).unwrap().errors(), &[]);

    // A backslash escapes nothing, so the quotes after it close.
    let source = "r\"\"\"\n  \\\"\"\"";
    check(source, &[&block(source, "RawBlockString", "")]);

    let source = "r\"\"\"\nabc";
    check(
        source,
        &[&block(
            source,
            "RawBlockString",
            " TokenFlags(UNTERMINATED)",
        )],
    );
    assert_eq!(
        lex(source).unwrap().errors(),
        &[error(0, 0, 4, LexErrorKind::UnterminatedRawBlockString)],
    );

    // A fenced raw string that begins with quotes is not a multi-line one.
    check(r##"r#"""x""#"##, &[r##"RawString 0..9 "r#\"\"\"x\"\"#""##]);
}

#[test]
fn block_strings_keep_line_breaks_and_flag_lone_carriage_returns() {
    let source = "\"\"\"\r\n  a\r\n  \"\"\"";
    check(source, &[&block(source, "BlockString", "")]);
    assert_eq!(lex(source).unwrap().errors(), &[]);

    let source = "\"\"\"\r  a\r  \"\"\"";
    check(
        source,
        &[&block(source, "BlockString", " TokenFlags(LONE_CR)")],
    );
    assert_eq!(
        lex(source).unwrap().errors(),
        &[
            error(0, 3, 4, LexErrorKind::LoneCarriageReturn),
            error(0, 7, 8, LexErrorKind::LoneCarriageReturn),
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
fn char_shapes() {
    check("'a'", &[r#"Char 0..3 "'a'""#]);
    check(r"'\''", &[r#"Char 0..4 "'\\''" TokenFlags(HAS_ESCAPE)"#]);
}

#[test]
fn char_literals_end_at_newline() {
    check(
        "'a\n",
        &[
            r#"Char 0..2 "'a" TokenFlags(UNTERMINATED)"#,
            r#"Newline 2..3 "\n""#,
        ],
    );
    assert_eq!(
        lex("'a\n").unwrap().errors(),
        &[error(0, 0, 2, LexErrorKind::UnterminatedChar)],
    );
}

#[test]
fn raw_string_shapes() {
    check(r#"r"a""#, &[r#"RawString 0..4 "r\"a\"""#]);
    check(r##"r#"a"#"##, &[r##"RawString 0..6 "r#\"a\"#""##]);
}

#[test]
fn raw_string_needs_matching_hashes() {
    let source = "r##\"a\"#";
    check(
        source,
        &[r##"RawString 0..7 "r##\"a\"#" TokenFlags(UNTERMINATED)"##],
    );
    assert_eq!(
        lex(source).unwrap().errors(),
        &[error(0, 0, 7, LexErrorKind::UnterminatedRawString)],
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
    let source =
        "\u{feff}fn main() {\r\n\tlet s = r#\"raw\"#; // trailing\n\t'c' \"str\" 2.5e-3 0xFF\n}\n";
    dump(source);
}

#[test]
fn holes_split_a_string_into_parts() {
    check(
        r#""a {x} b""#,
        &[
            r#"String 0..3 "\"a ""#,
            r#"Punct 3..4 "{""#,
            r#"Ident 4..5 "x""#,
            r#"Punct 5..6 "}""#,
            r#"String 6..9 " b\"""#,
        ],
    );
    // Adjacent holes have no text between them, and an empty hole none
    // inside.
    check(
        r#""{a}{b}""#,
        &[
            r#"String 0..1 "\"""#,
            r#"Punct 1..2 "{""#,
            r#"Ident 2..3 "a""#,
            r#"Punct 3..4 "}""#,
            r#"Punct 4..5 "{""#,
            r#"Ident 5..6 "b""#,
            r#"Punct 6..7 "}""#,
            r#"String 7..8 "\"""#,
        ],
    );
    check(
        r#""{}""#,
        &[
            r#"String 0..1 "\"""#,
            r#"Punct 1..2 "{""#,
            r#"Punct 2..3 "}""#,
            r#"String 3..4 "\"""#,
        ],
    );
    // Braces in a hole's code are the code's, and a string inside it is a
    // string.
    check(
        r#""{a {b} c}""#,
        &[
            r#"String 0..1 "\"""#,
            r#"Punct 1..2 "{""#,
            r#"Ident 2..3 "a""#,
            r#"HorizontalSpace 3..4 " ""#,
            r#"Punct 4..5 "{""#,
            r#"Ident 5..6 "b""#,
            r#"Punct 6..7 "}""#,
            r#"HorizontalSpace 7..8 " ""#,
            r#"Ident 8..9 "c""#,
            r#"Punct 9..10 "}""#,
            r#"String 10..11 "\"""#,
        ],
    );
    check(
        r#""{ "x" }""#,
        &[
            r#"String 0..1 "\"""#,
            r#"Punct 1..2 "{""#,
            r#"HorizontalSpace 2..3 " ""#,
            r#"String 3..6 "\"x\"""#,
            r#"HorizontalSpace 6..7 " ""#,
            r#"Punct 7..8 "}""#,
            r#"String 8..9 "\"""#,
        ],
    );
    // An escaped brace and the braces of a `\u{…}` escape open nothing,
    // and a raw literal has no holes.
    check(
        r#""\{x\}""#,
        &[r#"String 0..7 "\"\\{x\\}\"" TokenFlags(HAS_ESCAPE)"#],
    );
    check(
        r#""\u{41}""#,
        &[r#"String 0..8 "\"\\u{41}\"" TokenFlags(HAS_ESCAPE)"#],
    );
    check(r#"r"{x}""#, &[r#"RawString 0..6 "r\"{x}\"""#]);
}

#[test]
fn a_hole_ends_with_its_line() {
    check(
        "\"a {b\nc",
        &[
            r#"String 0..3 "\"a ""#,
            r#"Punct 3..4 "{""#,
            r#"Ident 4..5 "b""#,
            r#"Newline 5..6 "\n""#,
            r#"Ident 6..7 "c""#,
        ],
    );
    assert_eq!(
        lex("\"a {b\nc").unwrap().errors(),
        &[error(1, 3, 4, LexErrorKind::UnclosedHole)],
    );
    // A quote inside the hole that its line never closes is the literal's
    // closer, and the rest of the line lexes outside it.
    check(
        "\"a {b\" + c",
        &[
            r#"String 0..3 "\"a ""#,
            r#"Punct 3..4 "{""#,
            r#"Ident 4..5 "b""#,
            r#"String 5..6 "\"""#,
            r#"HorizontalSpace 6..7 " ""#,
            r#"Punct 7..8 "+""#,
            r#"HorizontalSpace 8..9 " ""#,
            r#"Ident 9..10 "c""#,
        ],
    );
    assert_eq!(
        lex("\"a {b\" + c").unwrap().errors(),
        &[error(1, 3, 4, LexErrorKind::UnclosedHole)],
    );
    // A comment in a hole runs to the end of the line, the hole's end
    // included.
    check(
        "\"{a // c}\"\nb",
        &[
            r#"String 0..1 "\"""#,
            r#"Punct 1..2 "{""#,
            r#"Ident 2..3 "a""#,
            r#"HorizontalSpace 3..4 " ""#,
            r#"LineComment 4..10 "// c}\"""#,
            r#"Newline 10..11 "\n""#,
            r#"Ident 11..12 "b""#,
        ],
    );
    assert_eq!(
        lex("\"{a // c}\"\nb").unwrap().errors(),
        &[error(1, 1, 2, LexErrorKind::UnclosedHole)],
    );
    // The text after a hole may run out with the line, which leaves the
    // literal unterminated, reported at its start.
    check(
        "\"{a}\n",
        &[
            r#"String 0..1 "\"""#,
            r#"Punct 1..2 "{""#,
            r#"Ident 2..3 "a""#,
            r#"Punct 3..4 "}""#,
            r#"Newline 4..5 "\n""#,
        ],
    );
    assert_eq!(
        lex("\"{a}\n").unwrap().errors(),
        &[error(0, 0, 1, LexErrorKind::UnterminatedString)],
    );
}

#[test]
fn block_strings_take_holes() {
    check(
        "\"\"\"\n  {x}\n  \"\"\"",
        &[
            r#"BlockString 0..6 "\"\"\"\n  ""#,
            r#"Punct 6..7 "{""#,
            r#"Ident 7..8 "x""#,
            r#"Punct 8..9 "}""#,
            r#"BlockString 9..15 "\n  \"\"\"""#,
        ],
    );
    // The text goes on from the line break that leaves a hole open.
    check(
        "\"\"\"\n  {x\n  y\n  \"\"\"",
        &[
            r#"BlockString 0..6 "\"\"\"\n  ""#,
            r#"Punct 6..7 "{""#,
            r#"Ident 7..8 "x""#,
            r#"BlockString 8..18 "\n  y\n  \"\"\"""#,
        ],
    );
    assert_eq!(
        lex("\"\"\"\n  {x\n  y\n  \"\"\"").unwrap().errors(),
        &[error(1, 6, 7, LexErrorKind::UnclosedHole)],
    );
    // No hole holds a `"""` literal: one inside a hole closes the literal.
    check(
        "\"\"\"\n {x\"\"\"",
        &[
            r#"BlockString 0..5 "\"\"\"\n ""#,
            r#"Punct 5..6 "{""#,
            r#"Ident 6..7 "x""#,
            r#"BlockString 7..10 "\"\"\"""#,
        ],
    );
    assert_eq!(
        lex("\"\"\"\n {x\"\"\"").unwrap().errors(),
        &[
            error(1, 5, 6, LexErrorKind::UnclosedHole),
            error(3, 7, 10, LexErrorKind::BlockStringCloserContent),
        ],
    );
}

#[test]
fn a_string_in_a_hole_may_have_holes() {
    // The inner literal's quote, which its line never closes, closes the
    // inner literal and leaves its hole open; the outer hole then closes,
    // and the outer literal runs out with the line.
    check(
        "\"{ \"{a\" }\n",
        &[
            r#"String 0..1 "\"""#,
            r#"Punct 1..2 "{""#,
            r#"HorizontalSpace 2..3 " ""#,
            r#"String 3..4 "\"""#,
            r#"Punct 4..5 "{""#,
            r#"Ident 5..6 "a""#,
            r#"String 6..7 "\"""#,
            r#"HorizontalSpace 7..8 " ""#,
            r#"Punct 8..9 "}""#,
            r#"Newline 9..10 "\n""#,
        ],
    );
    assert_eq!(
        lex("\"{ \"{a\" }\n").unwrap().errors(),
        &[
            error(0, 0, 1, LexErrorKind::UnterminatedString),
            error(4, 4, 5, LexErrorKind::UnclosedHole),
        ],
    );
}

#[test]
fn a_string_in_a_hole_never_closes_on_the_first_quote_of_a_block_delimiter() {
    // No hole holds a `"""` literal, so the quote that would close a
    // literal inside the hole on the first quote of one is the outer
    // literal's closer instead, and the `"""` opens a literal outside it.
    check(
        "\"a {b\" + \"\"\"\n  c\n  \"\"\"",
        &[
            r#"String 0..3 "\"a ""#,
            r#"Punct 3..4 "{""#,
            r#"Ident 4..5 "b""#,
            r#"String 5..6 "\"""#,
            r#"HorizontalSpace 6..7 " ""#,
            r#"Punct 7..8 "+""#,
            r#"HorizontalSpace 8..9 " ""#,
            r#"BlockString 9..22 "\"\"\"\n  c\n  \"\"\"""#,
        ],
    );
    assert_eq!(
        lex("\"a {b\" + \"\"\"\n  c\n  \"\"\"").unwrap().errors(),
        &[error(1, 3, 4, LexErrorKind::UnclosedHole)],
    );
}
