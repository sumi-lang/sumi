use jolt_lexer::lex;
use jolt_syntax::cook;

/// Lex and cook `source`, assert the 1:1 invariant, and render one line per
/// token: `SyntaxKind start..end "text"`.
fn dump(source: &str) -> Vec<String> {
    let lexed = lex(source).expect("test sources fit in u32");
    let cooked = cook(source, &lexed);
    assert_eq!(cooked.len(), lexed.len(), "cooking must stay 1:1");

    (0..cooked.len())
        .map(|index| {
            let range = lexed.range(index);
            format!(
                "{:?} {}..{} {:?}",
                cooked.kind(index),
                range.start().to_u32(),
                range.end().to_u32(),
                lexed.text(source, index),
            )
        })
        .collect()
}

#[track_caller]
fn check(source: &str, expected: &[&str]) {
    assert_eq!(dump(source), expected, "for source {source:?}");
}

#[test]
fn empty_source_cooks_to_nothing() {
    check("", &[]);
    assert!(cook("", &lex("").unwrap()).is_empty());
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
    let cooked = cook(source, &lexed);

    let keyword_kinds: Vec<String> = (0..cooked.len())
        .map(|index| format!("{:?}", cooked.kind(index)))
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
            r#"Punct 2..3 ">""#,
            r#"Punct 3..4 ">""#,
            r#"Punct 4..5 "=""#,
            r#"Whitespace 5..6 " ""#,
            r#"NumberLiteral 6..7 "2""#,
        ],
    );
}

#[test]
fn trivia_classification() {
    check(
        "\u{feff}a // c\nb",
        &[
            r#"Whitespace 0..3 "\u{feff}""#,
            r#"Ident 3..4 "a""#,
            r#"Whitespace 4..5 " ""#,
            r#"LineComment 5..9 "// c""#,
            r#"Newline 9..10 "\n""#,
            r#"Ident 10..11 "b""#,
        ],
    );
}

#[test]
fn literal_kinds() {
    check(
        r#"1.5 "s" r"r" 'c'"#,
        &[
            r#"NumberLiteral 0..3 "1.5""#,
            r#"Whitespace 3..4 " ""#,
            r#"StringLiteral 4..7 "\"s\"""#,
            r#"Whitespace 7..8 " ""#,
            r#"RawStringLiteral 8..12 "r\"r\"""#,
            r#"Whitespace 12..13 " ""#,
            r#"CharLiteral 13..16 "'c'""#,
        ],
    );
}

#[test]
fn malformed_literals_keep_their_kind() {
    check("\"open", &[r#"StringLiteral 0..5 "\"open""#]);
}

#[test]
fn unknown_cooks_to_error() {
    check(
        "a€b",
        &[
            r#"Ident 0..1 "a""#,
            r#"Error 1..4 "€""#,
            r#"Ident 4..5 "b""#,
        ],
    );
}

#[test]
fn misplaced_bom_cooks_to_error() {
    check(
        "x\u{feff}",
        &[r#"Ident 0..1 "x""#, r#"Error 1..4 "\u{feff}""#],
    );
}
