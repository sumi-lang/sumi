//! Language-level classification, assigned during the scan: keywords,
//! punctuation roles, literal kinds, and trivia.

use sumi_lexer::lex;

/// Lex `source` and render one line per token: `SyntaxKind start..end
/// "text"` plus any flags.
fn dump(source: &str) -> Vec<String> {
    let lexed = lex(source).expect("test sources fit in u32");

    lexed
        .indices()
        .map(|index| {
            let range = lexed.range(index);
            let flags = lexed.flags(index);
            let mut line = format!(
                "{:?} {}..{} {:?}",
                lexed.kind(index),
                range.start().to_u32(),
                range.end().to_u32(),
                lexed.text(source, index),
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
fn unused_punctuation_classifies_to_error() {
    // Collection reports these, so every later phase can treat an `Error`
    // token as already diagnosed.
    check(";", &[r#"Error 0..1 ";""#]);
    check("[", &[r#"Error 0..1 "[""#]);
}

#[test]
fn a_lone_underscore_is_its_own_kind() {
    check("_", &[r#"Underscore 0..1 "_""#]);
    check("_x", &[r#"Ident 0..2 "_x""#]);
}

#[test]
fn trivia_classification() {
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
fn literal_kinds() {
    check(
        r#"15 "s""#,
        &[
            r#"IntLiteral 0..2 "15""#,
            r#"Whitespace 2..3 " ""#,
            r#"StringLiteral 3..6 "\"s\"""#,
        ],
    );
}

#[test]
fn malformed_literals_keep_their_kind() {
    check(
        "\"open",
        &[r#"StringLiteral 0..5 "\"open" TokenFlags(UNTERMINATED)"#],
    );
}

#[test]
fn broken_numbers_keep_their_kind() {
    check(
        "1u32",
        &[r#"IntLiteral 0..4 "1u32" TokenFlags(MALFORMED_NUMBER)"#],
    );
    // A separator or an exponent is a suffix: there are no floats.
    check(
        "1_000",
        &[r#"IntLiteral 0..5 "1_000" TokenFlags(MALFORMED_NUMBER)"#],
    );
    check(
        "1e5",
        &[r#"IntLiteral 0..3 "1e5" TokenFlags(MALFORMED_NUMBER)"#],
    );
}

#[test]
fn unknown_classifies_to_error() {
    check(
        "a€b",
        &[
            r#"Ident 0..1 "a""#,
            r#"Error 1..4 "€""#,
            r#"Ident 4..5 "b""#,
        ],
    );
}
