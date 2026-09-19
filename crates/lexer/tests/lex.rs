use sumi_lexer::{LexError, LexErrorKind, RawIdx, lex};
use sumi_text::{TextRange, TextSize};

fn error(token: u32, start: u32, end: u32, kind: LexErrorKind) -> LexError {
    LexError {
        token: RawIdx::new(token),
        range: TextRange::new(TextSize::new(start), TextSize::new(end)),
        kind,
    }
}

fn dump(source: &str) -> Vec<String> {
    let file = lex(source).expect("test sources fit in u32");
    file.indices()
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
fn keywords_classify() {
    check(
        "fn map",
        &[
            r#"FnKw 0..2 "fn""#,
            r#"Whitespace 2..3 " ""#,
            r#"Ident 3..6 "map""#,
        ],
    );
}

#[test]
fn every_v0_keyword_classifies() {
    let source = "else false fn if let mut return true";
    let lexed = lex(source).unwrap();

    let keyword_kinds: Vec<String> = lexed
        .indices()
        .map(|index| format!("{:?}", lexed.kind(index)))
        .filter(|kind| kind.ends_with("Kw"))
        .collect();
    assert_eq!(
        keyword_kinds,
        [
            "ElseKw", "FalseKw", "FnKw", "IfKw", "LetKw", "MutKw", "ReturnKw", "TrueKw",
        ],
    );
}

#[test]
fn near_misses_stay_idents() {
    check(
        "fnx Fn lets _if",
        &[
            r#"Ident 0..3 "fnx""#,
            r#"Whitespace 3..4 " ""#,
            r#"Ident 4..6 "Fn""#,
            r#"Whitespace 6..7 " ""#,
            r#"Ident 7..11 "lets""#,
            r#"Whitespace 11..12 " ""#,
            r#"Ident 12..15 "_if""#,
        ],
    );
}

#[test]
fn keywords_inside_strings_and_comments_stay_put() {
    check(
        "\"fn\" // let\n",
        &[
            r#"StringLiteral 0..4 "\"fn\"""#,
            r#"Whitespace 4..5 " ""#,
            r#"LineComment 5..11 "// let""#,
            r#"Newline 11..12 "\n""#,
        ],
    );
}

#[test]
fn a_lone_underscore_is_its_own_kind() {
    check(
        "_ _x",
        &[
            r#"Underscore 0..1 "_""#,
            r#"Whitespace 1..2 " ""#,
            r#"Ident 2..4 "_x""#,
        ],
    );
}

#[test]
fn punct_stays_split_until_the_parser_glues() {
    check(
        "x >>= 2",
        &[
            r#"Ident 0..1 "x""#,
            r#"Whitespace 1..2 " ""#,
            r#"Gt 2..3 ">""#,
            r#"Gt 3..4 ">""#,
            r#"Eq 4..5 "=""#,
            r#"Whitespace 5..6 " ""#,
            r#"IntLiteral 6..7 "2""#,
        ],
    );
}

#[test]
fn punctuation_classifies_per_character() {
    let source = "( ) { } , : . = < > ! + - * / % & |";
    let lexed = lex(source).unwrap();

    let kinds: Vec<String> = lexed
        .indices()
        .map(|index| format!("{:?}", lexed.kind(index)))
        .filter(|kind| kind != "Whitespace")
        .collect();
    assert_eq!(
        kinds,
        [
            "LParen", "RParen", "LBrace", "RBrace", "Comma", "Colon", "Dot", "Eq", "Lt", "Gt",
            "Bang", "Plus", "Minus", "Star", "Slash", "Percent", "Amp", "Pipe",
        ],
    );
}

#[test]
fn unused_punctuation_is_an_error_token() {
    check(
        "(;)",
        &[
            r#"LParen 0..1 "(""#,
            r#"Error 1..2 ";""#,
            r#"RParen 2..3 ")""#,
        ],
    );
    check("[", &[r#"Error 0..1 "[""#]);
    assert_eq!(
        lex("(;)").unwrap().errors(),
        &[error(1, 1, 2, LexErrorKind::UnknownPunctuation)],
    );
}

#[test]
fn slash_star_is_just_punctuation() {
    check(
        "/* x",
        &[
            r#"Slash 0..1 "/""#,
            r#"Star 1..2 "*""#,
            r#"Whitespace 2..3 " ""#,
            r#"Ident 3..4 "x""#,
        ],
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
            r##"Error 1..2 "#""##,
            r#"Ident 2..3 "x""#,
        ],
    );
}

#[test]
fn horizontal_space_lexes_as_one_run() {
    check(
        "  \t x",
        &[r#"Whitespace 0..4 "  \t ""#, r#"Ident 4..5 "x""#],
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
    check("\r", &[r#"Newline 0..1 "\r""#]);
    assert_eq!(
        lex("\r").unwrap().errors(),
        &[error(0, 0, 1, LexErrorKind::LoneCarriageReturn)],
    );
}

#[test]
fn line_comments_end_at_newline() {
    check(
        "a // c\nb",
        &[
            r#"Ident 0..1 "a""#,
            r#"Whitespace 1..2 " ""#,
            r#"LineComment 2..6 "// c""#,
            r#"Newline 6..7 "\n""#,
            r#"Ident 7..8 "b""#,
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
fn identifiers_are_ascii() {
    check(
        "Δx aé",
        &[
            r#"Error 0..2 "Δ""#,
            r#"Ident 2..3 "x""#,
            r#"Whitespace 3..4 " ""#,
            r#"Ident 4..5 "a""#,
            r#"Error 5..7 "é""#,
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
fn control_chars_are_unknown() {
    check("\u{1}", &[r#"Error 0..1 "\u{1}""#]);
    assert_eq!(
        lex("\u{1}").unwrap().errors(),
        &[error(0, 0, 1, LexErrorKind::UnknownCharacter)],
    );
}

#[test]
fn a_byte_order_mark_is_an_unknown_character() {
    let source = "\u{feff}x";
    check(source, &[r#"Error 0..3 "\u{feff}""#, r#"Ident 3..4 "x""#]);
    assert_eq!(
        lex(source).unwrap().errors(),
        &[error(0, 0, 3, LexErrorKind::UnknownCharacter)],
    );
}

#[test]
fn literal_kinds() {
    check(
        r#"0 123 "s""#,
        &[
            r#"IntLiteral 0..1 "0""#,
            r#"Whitespace 1..2 " ""#,
            r#"IntLiteral 2..5 "123""#,
            r#"Whitespace 5..6 " ""#,
            r#"StringLiteral 6..9 "\"s\"""#,
        ],
    );
}

#[test]
fn a_dot_never_continues_a_number() {
    check(
        "1.5",
        &[
            r#"IntLiteral 0..1 "1""#,
            r#"Dot 1..2 ".""#,
            r#"IntLiteral 2..3 "5""#,
        ],
    );
    check(
        "1.foo",
        &[
            r#"IntLiteral 0..1 "1""#,
            r#"Dot 1..2 ".""#,
            r#"Ident 2..5 "foo""#,
        ],
    );
    check("1.", &[r#"IntLiteral 0..1 "1""#, r#"Dot 1..2 ".""#]);
}

#[test]
fn number_suffixes_attach() {
    check(
        "1u32",
        &[r#"IntLiteral 0..4 "1u32" TokenFlags(MALFORMED_NUMBER)"#],
    );
    check(
        "1_000",
        &[r#"IntLiteral 0..5 "1_000" TokenFlags(MALFORMED_NUMBER)"#],
    );
    check(
        "1e-5",
        &[
            r#"IntLiteral 0..2 "1e" TokenFlags(MALFORMED_NUMBER)"#,
            r#"Minus 2..3 "-""#,
            r#"IntLiteral 3..4 "5""#,
        ],
    );
    check(
        "0x1F",
        &[r#"IntLiteral 0..4 "0x1F" TokenFlags(MALFORMED_NUMBER)"#],
    );
    assert_eq!(
        lex("0x1F").unwrap().errors(),
        &[error(0, 1, 4, LexErrorKind::UnknownSuffix)],
    );
}

#[test]
fn an_escaped_quote_never_closes() {
    check(r#""a\"b""#, &[r#"StringLiteral 0..6 "\"a\\\"b\"""#]);
}

#[test]
fn unterminated_string() {
    check(
        "\"ab",
        &[r#"StringLiteral 0..3 "\"ab" TokenFlags(UNTERMINATED)"#],
    );
    assert_eq!(
        lex("\"ab").unwrap().errors(),
        &[error(0, 0, 3, LexErrorKind::UnterminatedString)],
    );
}

#[test]
fn line_literals_end_at_the_line() {
    check(
        "\"a\nb\"",
        &[
            r#"StringLiteral 0..2 "\"a" TokenFlags(UNTERMINATED)"#,
            r#"Newline 2..3 "\n""#,
            r#"Ident 3..4 "b""#,
            r#"StringLiteral 4..5 "\"" TokenFlags(UNTERMINATED)"#,
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
            r#"StringLiteral 0..3 "\"a\\" TokenFlags(UNTERMINATED)"#,
            r#"Newline 3..4 "\n""#,
            r#"Ident 4..5 "b""#,
        ],
    );
}
