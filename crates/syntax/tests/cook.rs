use sumi_lexer::lex;
use sumi_syntax::{SyntaxErrorKind, cook};

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

#[track_caller]
fn check_errors(source: &str, expected: &[(u32, SyntaxErrorKind)]) {
    let lexed = lex(source).expect("test sources fit in u32");
    let cooked = cook(source, &lexed);
    let actual: Vec<(u32, SyntaxErrorKind)> = cooked
        .errors()
        .iter()
        .map(|error| (error.token, error.kind))
        .collect();
    assert_eq!(actual, expected, "for source {source:?}");
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
    let cooked = cook(source, &lexed);

    let kinds: Vec<String> = (0..cooked.len())
        .map(|index| format!("{:?}", cooked.kind(index)))
        .filter(|kind| kind != "Whitespace")
        .collect();
    assert_eq!(
        kinds,
        [
            "LParen", "RParen", "LBrace", "RBrace", "Comma", "Colon", "Dot", "Eq", "Lt", "Gt",
            "Bang", "Plus", "Minus", "Star", "Slash", "Percent", "Amp", "Pipe",
        ],
    );
    check_errors(source, &[]);
}

#[test]
fn unused_punctuation_cooks_to_error() {
    // The parser reports these with the text in hand; no cook error.
    check(";", &[r#"Error 0..1 ";""#]);
    check("[", &[r#"Error 0..1 "[""#]);
    check_errors(";", &[]);
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
            r#"FloatLiteral 0..3 "1.5""#,
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
fn int_and_float_split() {
    let source = "0 123 1_000 1.5 1e5 2.5e-3";
    let lexed = lex(source).unwrap();
    let cooked = cook(source, &lexed);

    let number_kinds: Vec<String> = (0..cooked.len())
        .map(|index| format!("{:?}", cooked.kind(index)))
        .filter(|kind| kind.ends_with("Literal"))
        .collect();
    assert_eq!(
        number_kinds,
        [
            "IntLiteral",
            "IntLiteral",
            "IntLiteral",
            "FloatLiteral",
            "FloatLiteral",
            "FloatLiteral",
        ],
    );
    check_errors(source, &[]);
}

#[test]
fn exponent_plus_and_padding_are_rejected() {
    check("1e+5", &[r#"FloatLiteral 0..4 "1e+5""#]);
    check_errors("1e+5", &[(0, SyntaxErrorKind::ExponentPlusSign)]);
    check_errors("1e-5", &[]);
    check_errors("1e05", &[(0, SyntaxErrorKind::ExponentLeadingZero)]);
    check_errors("1e-05", &[(0, SyntaxErrorKind::ExponentLeadingZero)]);
    check_errors("1e0", &[]);
}

#[test]
fn multiple_number_errors_report_in_source_order() {
    check("1E+05", &[r#"FloatLiteral 0..5 "1E+05""#]);
    check_errors(
        "1E+05",
        &[
            (0, SyntaxErrorKind::UppercaseExponent),
            (0, SyntaxErrorKind::ExponentPlusSign),
            (0, SyntaxErrorKind::ExponentLeadingZero),
        ],
    );
}

#[test]
fn leading_zeros_are_rejected() {
    check_errors("0123", &[(0, SyntaxErrorKind::LeadingZero)]);
    // The digit count ignores separators: `0_0` is padded, `0_` is not.
    check_errors("0_0", &[(0, SyntaxErrorKind::LeadingZero)]);
    check_errors("0_", &[(0, SyntaxErrorKind::MisplacedUnderscore)]);
    check_errors("0", &[]);
    check_errors("0.5", &[]);
    check_errors("0e5", &[]);
    check_errors("1.05", &[]);
}

#[test]
fn misplaced_underscores_are_rejected() {
    check_errors("1_000 1_000_000", &[]);
    check_errors("1_", &[(0, SyntaxErrorKind::MisplacedUnderscore)]);
    check_errors("1__0", &[(0, SyntaxErrorKind::MisplacedUnderscore)]);
    check_errors("1_.5", &[(0, SyntaxErrorKind::MisplacedUnderscore)]);
    check_errors("1e5_", &[(0, SyntaxErrorKind::MisplacedUnderscore)]);
}

#[test]
fn suffixes_are_rejected() {
    check_errors("1u32", &[(0, SyntaxErrorKind::UnknownSuffix)]);
    check_errors("x 1_5f", &[(2, SyntaxErrorKind::UnknownSuffix)]);
    // Base prefixes are not part of the language; `x…` is just a suffix.
    check_errors("0x1F", &[(0, SyntaxErrorKind::UnknownSuffix)]);
    check_errors("0b10", &[(0, SyntaxErrorKind::UnknownSuffix)]);
    check_errors("0x", &[(0, SyntaxErrorKind::UnknownSuffix)]);
}

#[test]
fn exponent_markers_are_lowercase_only() {
    check_errors("1e5", &[]);
    check("1E5", &[r#"FloatLiteral 0..3 "1E5""#]);
    check_errors("1E5", &[(0, SyntaxErrorKind::UppercaseExponent)]);
    // The raw shape still munches signed uppercase exponents as one token.
    check("1E-5", &[r#"FloatLiteral 0..4 "1E-5""#]);
    check_errors("1E-5", &[(0, SyntaxErrorKind::UppercaseExponent)]);
    // `1E` has both problems; the missing digits are the primary error.
    check_errors("1E", &[(0, SyntaxErrorKind::MissingExponent)]);
}

#[test]
fn broken_exponents_get_a_targeted_error() {
    // A broken exponent still classifies as the intended float.
    check("1e", &[r#"FloatLiteral 0..2 "1e""#]);
    check_errors("1e", &[(0, SyntaxErrorKind::MissingExponent)]);
    check_errors("2.5e", &[(0, SyntaxErrorKind::MissingExponent)]);
    // The raw token is just `1e`: the lexer declined `+x` as an exponent.
    check_errors("1e+x", &[(0, SyntaxErrorKind::MissingExponent)]);
    // After a real exponent, a trailing `e5` is an ordinary unknown suffix.
    check_errors("1e5e5", &[(0, SyntaxErrorKind::UnknownSuffix)]);
    check_errors("1.5e5f", &[(0, SyntaxErrorKind::UnknownSuffix)]);
}

#[test]
fn lexer_reported_tokens_get_no_cook_errors() {
    // Unterminated literals already carry a LexError.
    check_errors("\"a\\q", &[]);
    check_errors("'ab", &[]);
}

#[test]
fn valid_escapes_pass() {
    check_errors(r#""a\n\r\t\\\"\'\0b" '\n' '\u{1F600}'"#, &[]);
}

#[test]
fn unknown_escapes_are_reported() {
    check_errors(r#""a\qb""#, &[(0, SyntaxErrorKind::UnknownEscape)]);
    check_errors(
        r#""\q\q""#,
        &[
            (0, SyntaxErrorKind::UnknownEscape),
            (0, SyntaxErrorKind::UnknownEscape),
        ],
    );
}

#[test]
fn unicode_escape_validation() {
    check_errors(r#""\u{41}""#, &[]);
    check_errors(r#""\uX""#, &[(0, SyntaxErrorKind::MalformedUnicodeEscape)]);
    check_errors(r#""\u{}""#, &[(0, SyntaxErrorKind::MalformedUnicodeEscape)]);
    check_errors(
        r#""\u{1234567}""#,
        &[(0, SyntaxErrorKind::MalformedUnicodeEscape)],
    );
    check_errors(
        r#""\u{zz}""#,
        &[(0, SyntaxErrorKind::MalformedUnicodeEscape)],
    );
    check_errors(
        r#""\u{d800}""#,
        &[(0, SyntaxErrorKind::InvalidUnicodeScalar)],
    );
    check_errors(
        r#""\u{110000}""#,
        &[(0, SyntaxErrorKind::InvalidUnicodeScalar)],
    );
}

#[test]
fn char_content_validation() {
    check_errors("'a'", &[]);
    check_errors(r"'\''", &[]);
    check_errors("''", &[(0, SyntaxErrorKind::EmptyCharLiteral)]);
    check_errors("'ab'", &[(0, SyntaxErrorKind::MoreThanOneChar)]);
    check_errors(r"'\u{41}b'", &[(0, SyntaxErrorKind::MoreThanOneChar)]);
    // A bad escape is one piece: no cascading length error.
    check_errors(r"'\q'", &[(0, SyntaxErrorKind::UnknownEscape)]);
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
