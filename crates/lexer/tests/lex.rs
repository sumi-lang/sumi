use jolt_lexer::{LexError, LexErrorKind, lex};

/// Lex `source`, assert the partition invariants every lex must uphold, and
/// render one line per token: `Kind start..end "text"` plus any flags.
fn dump(source: &str) -> Vec<String> {
    let file = lex(source).expect("test sources fit in u32");

    let mut concatenated = String::new();
    for index in 0..file.len() {
        let range = file.range(index);
        assert!(range.start() < range.end(), "token {index} is empty");
        assert!(source.is_char_boundary(range.start().to_usize()));
        assert!(source.is_char_boundary(range.end().to_usize()));

        if index == 0 {
            assert_eq!(range.start().to_u32(), 0, "first token must start at 0");
        } else {
            assert_eq!(
                range.start(),
                file.range(index - 1).end(),
                "token {index} is not contiguous"
            );
        }

        concatenated.push_str(file.text(source, index));
    }
    assert_eq!(concatenated, source, "tokens must reproduce the source");

    if let Some(last) = file.len().checked_sub(1) {
        assert_eq!(file.range(last).end(), file.source_len());
    }
    for error in file.errors() {
        assert!((error.token as usize) < file.len());
    }

    (0..file.len())
        .map(|index| {
            let range = file.range(index);
            let flags = file.flags(index);
            let mut line = format!(
                "{:?} {}..{} {:?}",
                file.kind(index),
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
}

#[test]
fn control_chars_are_unknown() {
    check("\u{1}", &[r#"Unknown 0..1 "\u{1}""#]);
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
        &[LexError {
            token: 1,
            kind: LexErrorKind::MisplacedBom
        }],
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
        &[LexError {
            token: 0,
            kind: LexErrorKind::LoneCarriageReturn
        }],
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
    // Jolt has line comments only; there is no block-comment syntax.
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
    // Boundaries must not depend on marker case; the cooker rejects `E`.
    check("1E-5", &[r#"Number 0..4 "1E-5""#]);
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
    check("1u32", &[r#"Number 0..4 "1u32""#]);
    check("1e", &[r#"Number 0..2 "1e""#]);
    // With no base prefixes in the language, `x1F` is just a suffix.
    check("0x1F", &[r#"Number 0..4 "0x1F""#]);
    assert_eq!(lex("0x1F").unwrap().errors(), &[]);
}

#[test]
fn string_shapes() {
    check(r#""abc""#, &[r#"String 0..5 "\"abc\"""#]);
    check("\"a\nb\"", &[r#"String 0..5 "\"a\nb\"""#]);
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
        &[LexError {
            token: 0,
            kind: LexErrorKind::UnterminatedString
        }],
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
        &[LexError {
            token: 0,
            kind: LexErrorKind::UnterminatedChar
        }],
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
        &[LexError {
            token: 0,
            kind: LexErrorKind::UnterminatedRawString
        }],
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
    let source = "fn main() {\n    x >>= 2;\n}\n";
    assert_eq!(lex(source).unwrap().errors(), &[]);
}

#[test]
fn partition_smoke() {
    let source =
        "\u{feff}fn main() {\r\n\tlet s = r#\"raw\"#; // trailing\n\t'c' \"str\" 2.5e-3 0xFF\n}\n";
    dump(source);
}
