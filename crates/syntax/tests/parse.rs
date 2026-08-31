mod common;

use sumi_lexer::{LexedFile, lex};
use sumi_syntax::{
    ParseAnchor, ParseEvidence, ParseExpected, ParseRecoveryKind, ParseViolationKind, ParserInput,
    cook, parse,
};

/// Parse `source`; assert the tree dump and the evidence, each rendered as
/// `Kind at byte`.
#[track_caller]
fn check(source: &str, tree: &[&str], evidence: &[&str]) {
    let lexed = lex(source).expect("test sources fit in u32");
    let cooked = cook(source, &lexed);
    let parse = parse(&ParserInput::new(&cooked));
    assert_eq!(
        common::dump(parse.tree(), &lexed, source),
        tree,
        "tree for {source:?}"
    );
    let actual: Vec<String> = parse
        .evidence()
        .iter()
        .map(|evidence| {
            format!(
                "{} at {}",
                evidence_name(evidence),
                common::start_byte(&lexed, evidence_token(evidence))
            )
        })
        .collect();
    assert_eq!(actual, evidence, "evidence for {source:?}");
}

fn evidence_name(evidence: &ParseEvidence) -> String {
    match evidence {
        ParseEvidence::Recovery(recovery) => match recovery.kind {
            ParseRecoveryKind::Expected(expected) => match expected {
                ParseExpected::Item => "ExpectedItem".into(),
                ParseExpected::Statement => "ExpectedStatement".into(),
                ParseExpected::Expression => "ExpectedExpression".into(),
                ParseExpected::Name => "ExpectedName".into(),
                ParseExpected::Type => "ExpectedType".into(),
                ParseExpected::Token(kind) => format!("Expected({kind:?})"),
                ParseExpected::Boundary => "ExpectedBoundary".into(),
            },
            kind => format!("{kind:?}"),
        },
        ParseEvidence::Violation(violation) => format!("{:?}", violation.kind),
    }
}

fn evidence_token(evidence: &ParseEvidence) -> u32 {
    match evidence {
        ParseEvidence::Recovery(recovery) => match recovery.anchor {
            ParseAnchor::Gap(gap) => gap.trivia_end(),
            ParseAnchor::Tokens(range) => range.start(),
        },
        ParseEvidence::Violation(violation) => violation.range.start(),
    }
}

fn raw_text<'a>(source: &'a str, lexed: &LexedFile, start: u32, end: u32) -> &'a str {
    let start = common::start_byte(lexed, start) as usize;
    let end = common::start_byte(lexed, end) as usize;
    &source[start..end]
}

#[test]
fn missing_syntax_anchors_the_raw_trivia_gap() {
    let source = "fn f() { x // tail";
    let lexed = lex(source).expect("test source fits in u32");
    let parse = parse(&ParserInput::new(&cook(source, &lexed)));
    let [ParseEvidence::Recovery(recovery)] = parse.evidence() else {
        panic!("the unclosed block has one recovery")
    };
    assert_eq!(
        recovery.kind,
        ParseRecoveryKind::Expected(ParseExpected::Token(sumi_syntax::SyntaxKind::RBrace))
    );
    let ParseAnchor::Gap(gap) = recovery.anchor else {
        panic!("missing syntax must anchor a gap")
    };
    assert_eq!(
        raw_text(source, &lexed, gap.trivia_start(), gap.trivia_end()),
        " // tail"
    );
    assert!(recovery.skipped.is_empty());
}

#[test]
fn present_syntax_anchors_nonempty_token_ranges() {
    let source = "fn f() { a==b }";
    let lexed = lex(source).expect("test source fits in u32");
    let parse = parse(&ParserInput::new(&cook(source, &lexed)));
    let [ParseEvidence::Violation(violation)] = parse.evidence() else {
        panic!("the unspaced operator has one violation")
    };
    assert_eq!(violation.kind, ParseViolationKind::UnspacedBinaryOperator);
    assert_eq!(
        raw_text(
            source,
            &lexed,
            violation.range.start(),
            violation.range.end()
        ),
        "=="
    );
}

#[test]
fn recovery_records_the_ranges_it_skips() {
    let source = ": (x)";
    let lexed = lex(source).expect("test source fits in u32");
    let parse = parse(&ParserInput::new(&cook(source, &lexed)));
    let [ParseEvidence::Recovery(recovery)] = parse.evidence() else {
        panic!("top-level garbage has one recovery")
    };
    assert_eq!(
        recovery.kind,
        ParseRecoveryKind::Expected(ParseExpected::Item)
    );
    let ParseAnchor::Tokens(anchor) = recovery.anchor else {
        panic!("rejected syntax must anchor tokens")
    };
    assert_eq!(raw_text(source, &lexed, anchor.start(), anchor.end()), ":");
    let [skipped] = &*recovery.skipped else {
        panic!("the recovery has one skipped range")
    };
    assert_eq!(
        raw_text(source, &lexed, skipped.start(), skipped.end()),
        source
    );
}

#[test]
fn empty_file() {
    check("", &[r#"SourceFile 0..0 """#], &[]);
    check("// nothing\n", &[r#"SourceFile 0..11 "// nothing\n""#], &[]);
}

#[test]
fn function_items() {
    check(
        "fn main() {}",
        &[
            "SourceFile 0..12",
            "  FnItem 0..12",
            r#"    ParamList 7..9 "()""#,
            r#"    Block 10..12 "{}""#,
        ],
        &[],
    );
    check(
        "fn add(a: int, b: int) -> int { a + b }",
        &[
            "SourceFile 0..39",
            "  FnItem 0..39",
            "    ParamList 6..22",
            r#"      Param 7..13 "a: int""#,
            r#"      Param 15..21 "b: int""#,
            "    Block 30..39",
            "      BinaryExpr 32..37",
            r#"        NameExpr 32..33 "a""#,
            r#"        NameExpr 36..37 "b""#,
        ],
        &[],
    );
    check(
        "fn f(a: int,) {}",
        &[
            "SourceFile 0..16",
            "  FnItem 0..16",
            "    ParamList 4..13",
            r#"      Param 5..11 "a: int""#,
            r#"    Block 14..16 "{}""#,
        ],
        &[],
    );
}

#[test]
fn a_malformed_signature_keeps_its_body() {
    // Garbage before the name.
    check(
        "fn } f() { x }",
        &[
            "SourceFile 0..14",
            "  FnItem 0..14",
            r#"    Error 3..4 "}""#,
            r#"    ParamList 6..8 "()""#,
            "    Block 9..14",
            r#"      NameExpr 11..12 "x""#,
        ],
        &["ExpectedName at 3"],
    );
    // A missing name, with the rest intact.
    check(
        "fn () {}",
        &[
            "SourceFile 0..8",
            "  FnItem 0..8",
            r#"    ParamList 3..5 "()""#,
            r#"    Block 6..8 "{}""#,
        ],
        &["ExpectedName at 3"],
    );
    // A duplicated name.
    check(
        "fn b b() {}",
        &[
            "SourceFile 0..11",
            "  FnItem 0..11",
            r#"    Error 5..6 "b""#,
            r#"    ParamList 6..8 "()""#,
            r#"    Block 9..11 "{}""#,
        ],
        &["Expected(LParen) at 5"],
    );
    // A missing `(`: the parameters are gone, the body is not.
    check(
        "fn a) { a }",
        &[
            "SourceFile 0..11",
            "  FnItem 0..11",
            r#"    Error 4..5 ")""#,
            "    Block 6..11",
            r#"      NameExpr 8..9 "a""#,
        ],
        &["Expected(LParen) at 4"],
    );
    // An unclosed `{` where the parameters belong is garbage, not the body:
    // the body is the `{` the stream pairs with a `}`.
    check(
        "fn a{ () {}",
        &[
            "SourceFile 0..11",
            "  FnItem 0..11",
            r#"    Error 4..5 "{""#,
            r#"    ParamList 6..8 "()""#,
            r#"    Block 9..11 "{}""#,
        ],
        &["Expected(LParen) at 4"],
    );
    // Garbage between the parameters and the body, and after the return
    // type.
    check(
        "fn f() ( { x }",
        &[
            "SourceFile 0..14",
            "  FnItem 0..14",
            r#"    ParamList 4..6 "()""#,
            r#"    Error 7..8 "(""#,
            "    Block 9..14",
            r#"      NameExpr 11..12 "x""#,
        ],
        &["Expected(LBrace) at 7"],
    );
    check(
        "fn f() -> int x { y }",
        &[
            "SourceFile 0..21",
            "  FnItem 0..21",
            r#"    ParamList 4..6 "()""#,
            r#"    Error 14..15 "x""#,
            "    Block 16..21",
            r#"      NameExpr 18..19 "y""#,
        ],
        &["Expected(LBrace) at 14"],
    );
    // A closer in the garbage is garbage: nothing encloses a signature.
    check(
        "fn foo() -) > int { b }",
        &[
            "SourceFile 0..23",
            "  FnItem 0..23",
            r#"    ParamList 6..8 "()""#,
            r#"    Error 9..17 "-) > int""#,
            "    Block 18..23",
            r#"      NameExpr 20..21 "b""#,
        ],
        &["Expected(LBrace) at 9"],
    );
    // A signature missing its `fn` is still an item; a misplaced call,
    // with nothing after its list, is not.
    check(
        "a() { x }",
        &[
            "SourceFile 0..9",
            "  FnItem 0..9",
            r#"    ParamList 1..3 "()""#,
            "    Block 4..9",
            r#"      NameExpr 6..7 "x""#,
        ],
        &["Expected(FnKw) at 0"],
    );
    check(
        "foo(2)\nfn f() {}",
        &[
            "SourceFile 0..16",
            r#"  Error 0..6 "foo(2)""#,
            "  FnItem 7..16",
            r#"    ParamList 11..13 "()""#,
            r#"    Block 14..16 "{}""#,
        ],
        &["ExpectedItem at 0"],
    );
    // An unpaired `{` in the parameter list is garbage in the list, not
    // the body.
    check(
        "fn a({ ) { x }",
        &[
            "SourceFile 0..14",
            "  FnItem 0..14",
            "    ParamList 4..8",
            r#"      Error 5..6 "{""#,
            "    Block 9..14",
            r#"      NameExpr 11..12 "x""#,
        ],
        &["ExpectedName at 5"],
    );
    // Nothing is searched for past the end of the line — the physical
    // line, whatever the newline rule says about the tokens around it. Each
    // part found missing there remains a distinct parser fact.
    check(
        "fn f() x\nfn g() {}",
        &[
            "SourceFile 0..18",
            "  FnItem 0..8",
            r#"    ParamList 4..6 "()""#,
            r#"    Error 7..8 "x""#,
            "  FnItem 9..18",
            r#"    ParamList 13..15 "()""#,
            r#"    Block 16..18 "{}""#,
        ],
        &["Expected(LBrace) at 7"],
    );
    check(
        "fn f +\n() { x }",
        &[
            "SourceFile 0..15",
            "  FnItem 0..6",
            r#"    Error 5..6 "+""#,
            r#"  Error 7..15 "() { x }""#,
        ],
        &[
            "Expected(LParen) at 5",
            "Expected(LBrace) at 7",
            "ExpectedItem at 7",
        ],
    );
    // A body or return type on the next line does not make a headless
    // signature an item.
    check(
        "a()\n-> int {}",
        &["SourceFile 0..13", r#"  Error 0..13 "a()\n-> int {}""#],
        &["ExpectedItem at 0"],
    );
}

#[test]
fn orphan_closers_at_the_top_level_are_one_episode() {
    // Nothing encloses the top level, so a closer there is garbage like
    // anything else: one report, however many runs it takes.
    check(
        "fn f() {}\n) }\nfn g() {}",
        &[
            "SourceFile 0..23",
            "  FnItem 0..9",
            r#"    ParamList 4..6 "()""#,
            r#"    Block 7..9 "{}""#,
            r#"  Error 10..13 ") }""#,
            "  FnItem 14..23",
            r#"    ParamList 18..20 "()""#,
            r#"    Block 21..23 "{}""#,
        ],
        &["ExpectedItem at 10"],
    );
}

#[test]
fn let_statements() {
    check(
        "fn f() {\n  let x = 1\n  let mut y: int = x\n}",
        &[
            "SourceFile 0..43",
            "  FnItem 0..43",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..43",
            "      LetStmt 11..20",
            r#"        LiteralExpr 19..20 "1""#,
            "      LetStmt 23..41",
            r#"        NameExpr 40..41 "x""#,
        ],
        &[],
    );
}

#[test]
fn discard_and_return_statements() {
    check(
        "fn f() {\n  _ = g(1)\n  return\n}",
        &[
            "SourceFile 0..30",
            "  FnItem 0..30",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..30",
            "      DiscardStmt 11..19",
            "        CallExpr 15..19",
            r#"          NameExpr 15..16 "g""#,
            "          ArgList 16..19",
            r#"            LiteralExpr 17..18 "1""#,
            r#"      ReturnStmt 22..28 "return""#,
        ],
        &[],
    );
}

#[test]
fn return_takes_a_value_only_on_its_own_line() {
    check(
        "fn f() {\n  return x\n  return\n  x\n}",
        &[
            "SourceFile 0..34",
            "  FnItem 0..34",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..34",
            "      ReturnStmt 11..19",
            r#"        NameExpr 18..19 "x""#,
            r#"      ReturnStmt 22..28 "return""#,
            r#"      NameExpr 31..32 "x""#,
        ],
        &[],
    );
}

#[test]
fn precedence_climbs() {
    check(
        "fn f() { a || b && c == d + e * -f(g) }",
        &[
            "SourceFile 0..39",
            "  FnItem 0..39",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..39",
            "      BinaryExpr 9..37",
            r#"        NameExpr 9..10 "a""#,
            "        BinaryExpr 14..37",
            r#"          NameExpr 14..15 "b""#,
            "          BinaryExpr 19..37",
            r#"            NameExpr 19..20 "c""#,
            "            BinaryExpr 24..37",
            r#"              NameExpr 24..25 "d""#,
            "              BinaryExpr 28..37",
            r#"                NameExpr 28..29 "e""#,
            "                PrefixExpr 32..37",
            "                  CallExpr 33..37",
            r#"                    NameExpr 33..34 "f""#,
            "                    ArgList 34..37",
            r#"                      NameExpr 35..36 "g""#,
        ],
        &[],
    );
}

#[test]
fn binary_operators_associate_left() {
    check(
        "fn f() { a - b - c }",
        &[
            "SourceFile 0..20",
            "  FnItem 0..20",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..20",
            "      BinaryExpr 9..18",
            "        BinaryExpr 9..14",
            r#"          NameExpr 9..10 "a""#,
            r#"          NameExpr 13..14 "b""#,
            r#"        NameExpr 17..18 "c""#,
        ],
        &[],
    );
}

#[test]
fn prefix_binds_tighter_than_binary_and_looser_than_call() {
    check(
        "fn f() { -a * b }",
        &[
            "SourceFile 0..17",
            "  FnItem 0..17",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..17",
            "      BinaryExpr 9..15",
            "        PrefixExpr 9..11",
            r#"          NameExpr 10..11 "a""#,
            r#"        NameExpr 14..15 "b""#,
        ],
        &[],
    );
}

#[test]
fn if_expressions_chain() {
    check(
        "fn f() { if a { 1 } else if b { 2 } else { 3 } }",
        &[
            "SourceFile 0..48",
            "  FnItem 0..48",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..48",
            "      IfExpr 9..46",
            r#"        NameExpr 12..13 "a""#,
            "        Block 14..19",
            r#"          LiteralExpr 16..17 "1""#,
            "        IfExpr 25..46",
            r#"          NameExpr 28..29 "b""#,
            "          Block 30..35",
            r#"            LiteralExpr 32..33 "2""#,
            "          Block 41..46",
            r#"            LiteralExpr 43..44 "3""#,
        ],
        &[],
    );
    // `else` continues the line before it.
    check(
        "fn f() {\n  if a { 1 }\n  else { 2 }\n}",
        &[
            "SourceFile 0..36",
            "  FnItem 0..36",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..36",
            "      IfExpr 11..34",
            r#"        NameExpr 14..15 "a""#,
            "        Block 16..21",
            r#"          LiteralExpr 18..19 "1""#,
            "        Block 29..34",
            r#"          LiteralExpr 31..32 "2""#,
        ],
        &[],
    );
}

#[test]
fn a_malformed_if_condition_still_keeps_its_body() {
    check(
        "fn f() { if {} }",
        &[
            "SourceFile 0..16",
            "  FnItem 0..16",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..16",
            "      IfExpr 9..14",
            r#"        Block 12..14 "{}""#,
        ],
        &["ExpectedExpression at 12"],
    );
    check(
        "fn f() { if 1 1 {} }",
        &[
            "SourceFile 0..20",
            "  FnItem 0..20",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..20",
            "      IfExpr 9..18",
            r#"        LiteralExpr 12..13 "1""#,
            r#"        Error 14..15 "1""#,
            r#"        Block 16..18 "{}""#,
        ],
        &["Expected(LBrace) at 14"],
    );
}

#[test]
fn blocks_and_parentheses_are_expressions() {
    check(
        "fn f() { let x = { (1) } }",
        &[
            "SourceFile 0..26",
            "  FnItem 0..26",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..26",
            "      LetStmt 9..24",
            "        Block 17..24",
            "          ParenExpr 19..22",
            r#"            LiteralExpr 20..21 "1""#,
        ],
        &[],
    );
}

#[test]
fn calls_take_argument_lists() {
    check(
        "fn f() { g()(a, b,) }",
        &[
            "SourceFile 0..21",
            "  FnItem 0..21",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..21",
            "      CallExpr 9..19",
            "        CallExpr 9..12",
            r#"          NameExpr 9..10 "g""#,
            r#"          ArgList 10..12 "()""#,
            "        ArgList 12..19",
            r#"          NameExpr 13..14 "a""#,
            r#"          NameExpr 16..17 "b""#,
        ],
        &[],
    );
    // Newlines inside parentheses never end a statement.
    check(
        "fn f() {\n  g(\n    a,\n    b\n  )\n}",
        &[
            "SourceFile 0..32",
            "  FnItem 0..32",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..32",
            "      CallExpr 11..30",
            r#"        NameExpr 11..12 "g""#,
            "        ArgList 12..30",
            r#"          NameExpr 18..19 "a""#,
            r#"          NameExpr 25..26 "b""#,
        ],
        &[],
    );
}

#[test]
fn leading_operators_continue_the_line_before() {
    check(
        "fn f() {\n  a\n  + b\n  && c\n}",
        &[
            "SourceFile 0..27",
            "  FnItem 0..27",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..27",
            "      BinaryExpr 11..25",
            "        BinaryExpr 11..18",
            r#"          NameExpr 11..12 "a""#,
            r#"          NameExpr 17..18 "b""#,
            r#"        NameExpr 24..25 "c""#,
        ],
        &[],
    );
}

#[test]
fn a_glued_minus_starts_a_statement_and_a_spaced_one_continues() {
    check(
        "fn f() {\n  a\n  -b\n  - c\n}",
        &[
            "SourceFile 0..25",
            "  FnItem 0..25",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..25",
            r#"      NameExpr 11..12 "a""#,
            "      BinaryExpr 15..23",
            "        PrefixExpr 15..17",
            r#"          NameExpr 16..17 "b""#,
            r#"        NameExpr 22..23 "c""#,
        ],
        &[],
    );
}

#[test]
fn unspaced_binary_operators_are_errors_recovered_as_binary() {
    check(
        "fn f() { a-b }",
        &[
            "SourceFile 0..14",
            "  FnItem 0..14",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..14",
            "      BinaryExpr 9..12",
            r#"        NameExpr 9..10 "a""#,
            r#"        NameExpr 11..12 "b""#,
        ],
        &["UnspacedBinaryOperator at 10"],
    );
    check(
        "fn f() { a +b }",
        &[
            "SourceFile 0..15",
            "  FnItem 0..15",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..15",
            "      BinaryExpr 9..13",
            r#"        NameExpr 9..10 "a""#,
            r#"        NameExpr 12..13 "b""#,
        ],
        &["UnspacedBinaryOperator at 11"],
    );
}

#[test]
fn a_trailing_operator_is_an_error_recovered_as_binary() {
    check(
        "fn f() {\n  a +\n  b\n}",
        &[
            "SourceFile 0..20",
            "  FnItem 0..20",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..20",
            "      BinaryExpr 11..18",
            r#"        NameExpr 11..12 "a""#,
            r#"        NameExpr 17..18 "b""#,
        ],
        &["TrailingOperator at 13"],
    );
}

#[test]
fn a_spaced_prefix_operator_is_an_error_recovered_as_prefix() {
    check(
        "fn f() { - a }",
        &[
            "SourceFile 0..14",
            "  FnItem 0..14",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..14",
            "      PrefixExpr 9..12",
            r#"        NameExpr 11..12 "a""#,
        ],
        &["SpacedPrefixOperator at 9"],
    );
}

#[test]
fn a_prefix_without_an_operand_reports_only_the_missing_operand() {
    check(
        "fn f() { - }",
        &[
            "SourceFile 0..12",
            "  FnItem 0..12",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..12",
            r#"      PrefixExpr 9..10 "-""#,
        ],
        &["ExpectedExpression at 11"],
    );
}

#[test]
fn comparisons_do_not_chain() {
    check(
        "fn f() { a < b < c }",
        &[
            "SourceFile 0..20",
            "  FnItem 0..20",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..20",
            "      Error 9..18",
            "        BinaryExpr 9..14",
            r#"          NameExpr 9..10 "a""#,
            r#"          NameExpr 13..14 "b""#,
            r#"        NameExpr 17..18 "c""#,
        ],
        &["ChainedComparison at 15"],
    );
    check(
        "fn f() { (a < b) < c }",
        &[
            "SourceFile 0..22",
            "  FnItem 0..22",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..22",
            "      BinaryExpr 9..20",
            "        ParenExpr 9..16",
            "          BinaryExpr 10..15",
            r#"            NameExpr 10..11 "a""#,
            r#"            NameExpr 14..15 "b""#,
            r#"        NameExpr 19..20 "c""#,
        ],
        &[],
    );
}

#[test]
fn missing_pieces_are_absent() {
    check(
        "fn f() {\n  let x =\n}",
        &[
            "SourceFile 0..20",
            "  FnItem 0..20",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..20",
            r#"      LetStmt 11..18 "let x =""#,
        ],
        &["ExpectedExpression at 19"],
    );
    check(
        "fn (a: int) {}",
        &[
            "SourceFile 0..14",
            "  FnItem 0..14",
            "    ParamList 3..11",
            r#"      Param 4..10 "a: int""#,
            r#"    Block 12..14 "{}""#,
        ],
        &["ExpectedName at 3"],
    );
    check(
        "fn f(a) {}",
        &[
            "SourceFile 0..10",
            "  FnItem 0..10",
            "    ParamList 4..7",
            r#"      Param 5..6 "a""#,
            r#"    Block 8..10 "{}""#,
        ],
        &["Expected(Colon) at 6"],
    );
    check(
        "fn f(a: int",
        &[
            "SourceFile 0..11",
            "  FnItem 0..11",
            "    ParamList 4..11",
            r#"      Param 5..11 "a: int""#,
        ],
        &["Expected(RParen) at 11", "Expected(LBrace) at 11"],
    );
}

#[test]
fn two_statements_on_one_line_are_an_error() {
    check(
        "fn f() { a b }",
        &[
            "SourceFile 0..14",
            "  FnItem 0..14",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..14",
            r#"      NameExpr 9..10 "a""#,
            r#"      NameExpr 11..12 "b""#,
        ],
        &["ExpectedBoundary at 11"],
    );
}

#[test]
fn garbage_at_the_top_level_resynchronizes_at_fn() {
    check(
        "x = 1\nfn f() {}",
        &[
            "SourceFile 0..15",
            r#"  Error 0..5 "x = 1""#,
            "  FnItem 6..15",
            r#"    ParamList 10..12 "()""#,
            r#"    Block 13..15 "{}""#,
        ],
        &["ExpectedItem at 0"],
    );
}

#[test]
fn a_nested_fn_is_skipped_whole() {
    check(
        "fn f() {\n  fn g() {}\n}",
        &[
            "SourceFile 0..22",
            "  FnItem 0..22",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..22",
            r#"      Error 11..20 "fn g() {}""#,
        ],
        &["ExpectedStatement at 11"],
    );
}

#[test]
fn an_unclosed_block_ends_at_the_next_item() {
    // The stream never closes the body's `{`, so the `fn` that follows is
    // where the `}` was meant to be, not a statement to skip; the item
    // after it is intact.
    check(
        "fn foo() -> int { { b }\n\nfn a() {}",
        &[
            "SourceFile 0..34",
            "  FnItem 0..23",
            r#"    ParamList 6..8 "()""#,
            "    Block 16..23",
            "      Block 18..23",
            r#"        NameExpr 20..21 "b""#,
            "  FnItem 25..34",
            r#"    ParamList 29..31 "()""#,
            r#"    Block 32..34 "{}""#,
        ],
        &["Expected(RBrace) at 25"],
    );
    // Every unclosed block ends there, for one report.
    check(
        "fn f() { if c {\n x\nfn g() {}",
        &[
            "SourceFile 0..28",
            "  FnItem 0..18",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..18",
            "      IfExpr 9..18",
            r#"        NameExpr 12..13 "c""#,
            "        Block 14..18",
            r#"          NameExpr 17..18 "x""#,
            "  FnItem 19..28",
            r#"    ParamList 23..25 "()""#,
            r#"    Block 26..28 "{}""#,
        ],
        &["Expected(RBrace) at 19", "Expected(RBrace) at 19"],
    );
    // On the line of the last statement too.
    check(
        "fn f() { x fn g() {}",
        &[
            "SourceFile 0..20",
            "  FnItem 0..10",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..10",
            r#"      NameExpr 9..10 "x""#,
            "  FnItem 11..20",
            r#"    ParamList 15..17 "()""#,
            r#"    Block 18..20 "{}""#,
        ],
        &["Expected(RBrace) at 11"],
    );
    // Statement recovery stops there too: the run beginning at `:` is
    // inside the unclosed block, and the item is not its to take.
    check(
        "fn f() { : fn g() {}",
        &[
            "SourceFile 0..20",
            "  FnItem 0..10",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..10",
            r#"      Error 9..10 ":""#,
            "  FnItem 11..20",
            r#"    ParamList 15..17 "()""#,
            r#"    Block 18..20 "{}""#,
        ],
        &["ExpectedStatement at 9", "Expected(RBrace) at 11"],
    );
    // A block the stream closes owns the `fn` like anything else in it.
    check(
        "fn f() { : fn g() {} }",
        &[
            "SourceFile 0..22",
            "  FnItem 0..22",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..22",
            r#"      Error 9..20 ": fn g() {}""#,
        ],
        &["ExpectedStatement at 9"],
    );
}

#[test]
fn a_closed_list_owns_everything_up_to_its_closer() {
    // The stream pairs the `(` with the `)`, so a `{` before it is garbage
    // in the list — not the body, whatever the list would otherwise yield
    // to — and the body is where it was.
    check(
        "fn f(a: { int) { x }",
        &[
            "SourceFile 0..20",
            "  FnItem 0..20",
            "    ParamList 4..14",
            r#"      Param 5..7 "a:""#,
            r#"      Error 8..13 "{ int""#,
            "    Block 15..20",
            r#"      NameExpr 17..18 "x""#,
        ],
        &["ExpectedType at 8", "ExpectedName at 8"],
    );
    check(
        "fn x1(b: int, foo: int{ ) {}",
        &[
            "SourceFile 0..28",
            "  FnItem 0..28",
            "    ParamList 5..25",
            r#"      Param 6..12 "b: int""#,
            r#"      Param 14..22 "foo: int""#,
            r#"      Error 22..23 "{""#,
            r#"    Block 26..28 "{}""#,
        ],
        &["ExpectedName at 22"],
    );
    // The same for an argument list and a misplaced `fn`.
    check(
        "fn f() { g(fn, b) }",
        &[
            "SourceFile 0..19",
            "  FnItem 0..19",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..19",
            "      CallExpr 9..17",
            r#"        NameExpr 9..10 "g""#,
            "        ArgList 10..17",
            r#"          Error 11..13 "fn""#,
            r#"          NameExpr 15..16 "b""#,
        ],
        &["ExpectedExpression at 11"],
    );
}

#[test]
fn prior_phase_tokens_are_recorded_as_recovery() {
    let source = "fn f() {\n  a ;\n  b\n}";
    check(
        source,
        &[
            "SourceFile 0..20",
            "  FnItem 0..20",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..20",
            r#"      NameExpr 11..12 "a""#,
            r#"      Error 13..14 ";""#,
            r#"      NameExpr 17..18 "b""#,
        ],
        &["ExpectedBoundary at 13", "PriorPhaseError at 13"],
    );

    let lexed = lex(source).expect("test source fits in u32");
    let parsed = parse(&ParserInput::new(&cook(source, &lexed)));
    let ParseEvidence::Recovery(recovery) = &parsed.evidence()[1] else {
        panic!("the prior-phase token starts a recovery")
    };
    assert_eq!(recovery.kind, ParseRecoveryKind::PriorPhaseError);
    let ParseAnchor::Tokens(anchor) = recovery.anchor else {
        panic!("prior-phase syntax must anchor its tokens")
    };
    assert_eq!(raw_text(source, &lexed, anchor.start(), anchor.end()), ";");
    assert_eq!(recovery.skipped.as_ref(), &[anchor]);

    // Adjacent tokens diagnosed by earlier phases form one recovery run.
    let source = "fn f() { ; € }";
    let lexed = lex(source).expect("test source fits in u32");
    let parsed = parse(&ParserInput::new(&cook(source, &lexed)));
    let [ParseEvidence::Recovery(recovery)] = parsed.evidence() else {
        panic!("adjacent prior-phase tokens form one recovery")
    };
    assert_eq!(recovery.kind, ParseRecoveryKind::PriorPhaseError);
    let ParseAnchor::Tokens(anchor) = recovery.anchor else {
        panic!("prior-phase syntax must anchor its tokens")
    };
    assert_eq!(
        raw_text(source, &lexed, anchor.start(), anchor.end()),
        "; €"
    );
    assert_eq!(recovery.skipped.as_ref(), &[anchor]);
}

#[test]
fn blocks_open_on_the_line_of_their_owner() {
    check(
        "fn f()\n{\n}",
        &[
            "SourceFile 0..10",
            "  FnItem 0..10",
            r#"    ParamList 4..6 "()""#,
            r#"    Block 7..10 "{\n}""#,
        ],
        &["BlockOnNewLine at 7"],
    );
    check(
        "fn f() { if a\n{ } }",
        &[
            "SourceFile 0..19",
            "  FnItem 0..19",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..19",
            "      IfExpr 9..13",
            r#"        NameExpr 12..13 "a""#,
            r#"      Block 14..17 "{ }""#,
        ],
        &["Expected(LBrace) at 14"],
    );
}

#[test]
fn unclosed_delimiters() {
    check(
        "fn f() { (a }",
        &[
            "SourceFile 0..13",
            "  FnItem 0..13",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..13",
            "      ParenExpr 9..11",
            r#"        NameExpr 10..11 "a""#,
        ],
        &["Expected(RParen) at 12"],
    );
    check(
        "fn f() { g(a",
        &[
            "SourceFile 0..12",
            "  FnItem 0..12",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..12",
            "      CallExpr 9..12",
            r#"        NameExpr 9..10 "g""#,
            "        ArgList 10..12",
            r#"          NameExpr 11..12 "a""#,
        ],
        &["Expected(RParen) at 12", "Expected(RBrace) at 12"],
    );
}

#[test]
fn malformed_literals_are_structurally_ordinary() {
    // `1e` carries a cook error; misplacing it is a second, independent
    // problem, so the parser still reports it.
    check(
        "1e",
        &["SourceFile 0..2", r#"  Error 0..2 "1e""#],
        &["ExpectedItem at 0"],
    );
}

#[test]
fn list_recovery_leaves_enclosing_syntax_alone() {
    // The block's `}` is not the argument list's to take.
    check(
        "fn f() { g( }",
        &[
            "SourceFile 0..13",
            "  FnItem 0..13",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..13",
            "      CallExpr 9..11",
            r#"        NameExpr 9..10 "g""#,
            r#"        ArgList 10..11 "(""#,
        ],
        &["Expected(RParen) at 12"],
    );
    // Nor is the next item's body the parameter list's, or the function's.
    check(
        "fn f(\nfn g() {}",
        &[
            "SourceFile 0..15",
            "  FnItem 0..5",
            r#"    ParamList 4..5 "(""#,
            "  FnItem 6..15",
            r#"    ParamList 10..12 "()""#,
            r#"    Block 13..15 "{}""#,
        ],
        &["Expected(RParen) at 6", "Expected(LBrace) at 6"],
    );
    // An unpaired block opener immediately before the list's `)` is local
    // garbage; it does not turn the rest of the enclosing expression into
    // an unclosed block.
    check(
        "fn f() { g(a, { ) x }",
        &[
            "SourceFile 0..21",
            "  FnItem 0..21",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..21",
            "      CallExpr 9..17",
            r#"        NameExpr 9..10 "g""#,
            "        ArgList 10..17",
            r#"          NameExpr 11..12 "a""#,
            r#"          Error 14..15 "{""#,
            r#"      Error 18..19 "x""#,
        ],
        &["ExpectedExpression at 14"],
    );
}

#[test]
fn recovery_matches_brackets_inside_the_skipped_run() {
    // The run takes the block whole, as the stream pairs it: the boundary
    // inside it is never consulted.
    check(
        "fn f() { x = { a\nb } }",
        &[
            "SourceFile 0..22",
            "  FnItem 0..22",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..22",
            r#"      NameExpr 9..10 "x""#,
            r#"      Error 11..20 "= { a\nb }""#,
        ],
        &["ExpectedStatement at 11"],
    );
}

#[test]
fn garbage_before_an_argument_ends_where_the_argument_begins() {
    // The `:` displaced the argument, which is still there to parse.
    check(
        "fn f() { g(:(x), y) }",
        &[
            "SourceFile 0..21",
            "  FnItem 0..21",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..21",
            "      CallExpr 9..19",
            r#"        NameExpr 9..10 "g""#,
            "        ArgList 10..19",
            r#"          Error 11..12 ":""#,
            "          ParenExpr 12..15",
            r#"            NameExpr 13..14 "x""#,
            r#"          NameExpr 17..18 "y""#,
        ],
        &["ExpectedExpression at 11"],
    );
}

#[test]
fn recovery_never_takes_an_enclosing_closer() {
    // The unmatched `{` must not let the run swallow the argument list's `)`.
    check(
        "fn f() { g(:{) }",
        &[
            "SourceFile 0..16",
            "  FnItem 0..16",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..16",
            "      CallExpr 9..14",
            r#"        NameExpr 9..10 "g""#,
            "        ArgList 10..14",
            r#"          Error 11..13 ":{""#,
        ],
        &["ExpectedExpression at 11"],
    );
}

#[test]
fn recovery_ownership_regressions() {
    // A matched group inside malformed statement syntax remains local even
    // when its enclosing block is unclosed. Its `fn` is not reparented into
    // a top-level item.
    check(
        "fn f() { : { fn g() {} }",
        &[
            "SourceFile 0..24",
            "  FnItem 0..24",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..24",
            r#"      Error 9..24 ": { fn g() {} }""#,
        ],
        &["ExpectedStatement at 9", "Expected(RBrace) at 24"],
    );
    // The same remains true in an unclosed block nested under a known outer
    // closer: recovery may take the local group, but not that outer `)`.
    check(
        "fn f() { ({ : { fn g() {} } ) }",
        &[
            "SourceFile 0..31",
            "  FnItem 0..31",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..31",
            "      ParenExpr 9..29",
            "        Block 10..27",
            r#"          Error 12..27 ": { fn g() {} }""#,
        ],
        &["ExpectedStatement at 12", "Expected(RBrace) at 28"],
    );
    // The inner unclosed list yields the `)` mechanically paired with the
    // enclosing paren instead of stealing it as a recovery closer.
    check(
        "fn f() { ({ g(a } x ) }",
        &[
            "SourceFile 0..23",
            "  FnItem 0..23",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..23",
            "      ParenExpr 9..21",
            "        Block 10..19",
            "          CallExpr 12..19",
            r#"            NameExpr 12..13 "g""#,
            "            ArgList 13..19",
            r#"              NameExpr 14..15 "a""#,
            r#"              Error 16..17 "}""#,
            r#"              NameExpr 18..19 "x""#,
        ],
        &[
            "ExpectedExpression at 16",
            "Expected(RParen) at 20",
            "Expected(RBrace) at 20",
        ],
    );
    // A plain parenthesized expression follows the same ownership rule.
    check(
        "fn f() { ({ (} x ) }",
        &[
            "SourceFile 0..20",
            "  FnItem 0..20",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..20",
            "      ParenExpr 9..18",
            "        Block 10..16",
            "          ParenExpr 12..16",
            r#"            Error 13..14 "}""#,
            r#"            NameExpr 15..16 "x""#,
        ],
        &[
            "ExpectedExpression at 13",
            "Expected(RParen) at 17",
            "Expected(RBrace) at 17",
        ],
    );
}

/// Parse `source` and return its evidence kinds, asserting the tree is well
/// formed.
fn evidence_kinds(source: &str) -> Vec<String> {
    let lexed = lex(source).expect("test sources fit in u32");
    let parse = parse(&ParserInput::new(&cook(source, &lexed)));
    let _ = common::dump(parse.tree(), &lexed, source);
    parse.evidence().iter().map(evidence_name).collect()
}

/// How many `fn` items `source` parses into.
fn items(source: &str) -> usize {
    let lexed = lex(source).expect("test sources fit in u32");
    let parse = parse(&ParserInput::new(&cook(source, &lexed)));
    let tree = parse.tree();
    (0..tree.len())
        .filter(|&node| tree.kind(node) == sumi_syntax::NodeKind::FnItem)
        .count()
}

#[test]
fn a_block_yields_to_the_paren_that_encloses_it() {
    // A `{` is valid expression syntax, but the block cannot take the `)`
    // owned by the enclosing paren during recovery.
    check(
        "fn f() { ({ ) }",
        &[
            "SourceFile 0..15",
            "  FnItem 0..15",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..15",
            "      ParenExpr 9..13",
            r#"        Block 10..11 "{""#,
        ],
        &["Expected(RBrace) at 12"],
    );
    // A `)` with nothing to close is garbage inside the expression.
    check(
        "fn f() { g(a)) }",
        &[
            "SourceFile 0..16",
            "  FnItem 0..16",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..16",
            "      CallExpr 9..13",
            r#"        NameExpr 9..10 "g""#,
            "        ArgList 10..13",
            r#"          NameExpr 11..12 "a""#,
            r#"      Error 13..14 ")""#,
        ],
        &["Unexpected at 13"],
    );
}

#[test]
fn a_block_does_not_yield_to_a_paren_opened_inside_it() {
    // `(a` recovers before `b`; the remainder of that malformed statement
    // stays one local error rather than becoming a plausible new statement.
    check(
        "fn f() { (a b) }",
        &[
            "SourceFile 0..16",
            "  FnItem 0..16",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..16",
            "      ParenExpr 9..11",
            r#"        NameExpr 10..11 "a""#,
            r#"      Error 12..14 "b)""#,
        ],
        &["Expected(RParen) at 12"],
    );
    // The same with a brace in between: statement recovery owns the
    // malformed suffix, then the nearest `}` closes the body.
    check(
        "fn f() { (a { b) } }",
        &[
            "SourceFile 0..20",
            "  FnItem 0..18",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..18",
            "      ParenExpr 9..11",
            r#"        NameExpr 10..11 "a""#,
            r#"      Error 12..16 "{ b)""#,
            r#"  Error 19..20 "}""#,
        ],
        &["Expected(RParen) at 12", "ExpectedItem at 19"],
    );
}

#[test]
fn a_block_yields_only_to_a_paren_the_parser_still_has_open() {
    // The block-local recovery does not let a malformed inner statement
    // steal syntax from constructs which enclose the block.
    check(
        "fn f() { ({ (a { b) } }) }",
        &[
            "SourceFile 0..26",
            "  FnItem 0..23",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..23",
            "      ParenExpr 9..21",
            "        Block 10..21",
            "          ParenExpr 12..14",
            r#"            NameExpr 13..14 "a""#,
            r#"          Error 15..19 "{ b)""#,
            r#"  Error 23..26 ") }""#,
        ],
        &[
            "Expected(RParen) at 15",
            "Expected(RParen) at 22",
            "ExpectedItem at 23",
        ],
    );
}

#[test]
fn an_opener_nothing_closes_does_not_extend_a_skipped_run() {
    // The `}` mechanically discards the unmatched `(`, so the run does not
    // nest at it: the `,` ends the run, and `b` is an argument after all.
    check(
        "fn f() { g(:(, b }",
        &[
            "SourceFile 0..18",
            "  FnItem 0..18",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..18",
            "      CallExpr 9..16",
            r#"        NameExpr 9..10 "g""#,
            "        ArgList 10..16",
            r#"          Error 11..13 ":(""#,
            r#"          NameExpr 15..16 "b""#,
        ],
        &["ExpectedExpression at 11", "Expected(RParen) at 17"],
    );
}

#[test]
fn declarations_end_at_line_breaks() {
    // `=`, `:`, and `->` never continue a line, so a declaration cannot
    // pick them up from the next one.
    check(
        "fn f() {\n  let x\n  = 1\n}",
        &[
            "SourceFile 0..24",
            "  FnItem 0..24",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..24",
            r#"      LetStmt 11..16 "let x""#,
            r#"      Error 19..22 "= 1""#,
        ],
        &["Expected(Eq) at 19", "ExpectedStatement at 19"],
    );
    check(
        "fn f() {\n  let x\n  : int = 1\n}",
        &[
            "SourceFile 0..30",
            "  FnItem 0..30",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..30",
            r#"      LetStmt 11..16 "let x""#,
            r#"      Error 19..28 ": int = 1""#,
        ],
        &["Expected(Eq) at 19", "ExpectedStatement at 19"],
    );
    check(
        "fn f() {\n  _\n  = v\n}",
        &[
            "SourceFile 0..20",
            "  FnItem 0..20",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..20",
            r#"      DiscardStmt 11..12 "_""#,
            r#"      Error 15..18 "= v""#,
        ],
        &["Expected(Eq) at 15", "ExpectedStatement at 15"],
    );
    check(
        "fn f()\n-> int {}",
        &[
            "SourceFile 0..16",
            "  FnItem 0..6",
            r#"    ParamList 4..6 "()""#,
            r#"  Error 7..16 "-> int {}""#,
        ],
        &["Expected(LBrace) at 7", "ExpectedItem at 7"],
    );
    check(
        "fn f\n() {}",
        &[
            "SourceFile 0..10",
            r#"  FnItem 0..4 "fn f""#,
            r#"  Error 5..10 "() {}""#,
        ],
        &[
            "Expected(LParen) at 5",
            "Expected(LBrace) at 5",
            "ExpectedItem at 5",
        ],
    );
}

#[test]
fn arguments_stay_on_the_callee_line_even_inside_parens() {
    // Boundaries are suspended inside `(`, so the line break alone must
    // keep `()` from attaching to `g`.
    check(
        "fn f() { (g\n()) }",
        &[
            "SourceFile 0..17",
            "  FnItem 0..17",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..17",
            "      ParenExpr 9..11",
            r#"        NameExpr 10..11 "g""#,
            r#"      Error 12..15 "())""#,
        ],
        &["Expected(RParen) at 12"],
    );
}

#[test]
fn a_paren_takes_its_closer_across_a_boundary_a_block_restored() {
    // The block inside the parens restores boundaries, so one precedes the
    // `)`; the block yields to it, and the paren still owns it.
    check(
        "fn f() { ({ a\n) }",
        &[
            "SourceFile 0..17",
            "  FnItem 0..17",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..17",
            "      ParenExpr 9..15",
            "        Block 10..13",
            r#"          NameExpr 12..13 "a""#,
        ],
        &["Expected(RBrace) at 14"],
    );
}

#[test]
fn recovery_over_many_brackets_is_linear() {
    let n = 50_000;
    let source = format!(":{}{}{}", "{".repeat(n), "(".repeat(n), ")".repeat(n));
    assert_eq!(evidence_kinds(&source), ["ExpectedItem"]);
}

#[test]
fn a_group_spanning_a_boundary_stays_open_in_an_unclosed_body() {
    // With no parser-owned closer ahead, recovery takes a matched group
    // whole only when no statement boundary lies inside it: the statement
    // after the break is kept, not swallowed with the garbage.
    check(
        "fn f() {\n: { { x\ny } }\n",
        &[
            "SourceFile 0..23",
            "  FnItem 0..20",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..20",
            r#"      Error 9..16 ": { { x""#,
            r#"      NameExpr 17..18 "y""#,
            r#"  Error 21..22 "}""#,
        ],
        &["ExpectedStatement at 9", "ExpectedItem at 21"],
    );
}

#[test]
fn recovery_over_nested_groups_spanning_a_boundary_is_linear() {
    // Every group of the ladder spans the central boundary inside an
    // unclosed body, so each is rejected and entered one token at a time;
    // rejecting one must not rescan its interior.
    let n = 50_000;
    let source = format!("fn f() {{\n: {}x\ny {}\n", "{ ".repeat(n), "} ".repeat(n));
    assert_eq!(
        evidence_kinds(&source),
        ["ExpectedStatement", "ExpectedItem"]
    );
    assert_eq!(items(&source), 1);
}

#[test]
fn nesting_is_bounded() {
    use sumi_syntax::MAX_DEPTH;
    let deep = |n: usize| format!("fn f() {{ {}x{} }}", "(".repeat(n), ")".repeat(n));
    assert_eq!(
        evidence_kinds(&deep(MAX_DEPTH as usize / 2)),
        Vec::<String>::new()
    );
    // At the limit with nothing left, or with a closer: no recovery run to
    // take a token that is not an expression's. Every open construct retains
    // its own missing-closer fact at EOF.
    let opens = |n: u32| format!("fn f() {{ {}", "(".repeat(n as usize));
    let assert_unclosed = |evidence: &[String], first: &str| {
        assert!(evidence.len() >= 2);
        assert_eq!(evidence.first().map(String::as_str), Some(first));
        assert_eq!(
            evidence.last().map(String::as_str),
            Some("Expected(RBrace)")
        );
        assert!(
            evidence[1..evidence.len() - 1]
                .iter()
                .all(|kind| kind == "Expected(RParen)")
        );
    };
    assert_unclosed(&evidence_kinds(&opens(MAX_DEPTH - 2)), "ExpectedExpression");
    // The `)` closes the innermost paren; the rest stay open to the end.
    assert_unclosed(
        &evidence_kinds(&format!("{})", opens(MAX_DEPTH - 2))),
        "ExpectedExpression",
    );
    assert_unclosed(&evidence_kinds(&opens(MAX_DEPTH + 40)), "NestingTooDeep");
    // The skip past the limit stops at the next item like any recovery:
    // the parens are unclosed, so the `fn` is not theirs to take.
    let next_item = format!("{}x fn g() {{}}", opens(MAX_DEPTH + 40));
    assert_unclosed(&evidence_kinds(&next_item), "NestingTooDeep");
    assert_eq!(items(&next_item), 2);
    // Far past the limit: one error, no crash, and the file still closes.
    assert_eq!(evidence_kinds(&deep(100_000)), ["NestingTooDeep"]);
    assert_eq!(
        evidence_kinds(&format!("fn f() {{ {}x }}", "!".repeat(100_000))),
        ["NestingTooDeep"]
    );
    assert_eq!(
        evidence_kinds(&format!(
            "fn f() {{ {}if a {{}} }}",
            "if a {} else ".repeat(100_000)
        )),
        ["NestingTooDeep"]
    );
}

#[test]
fn underscore_is_not_a_name() {
    check(
        "fn f() { let _ = 1 }",
        &[
            "SourceFile 0..20",
            "  FnItem 0..20",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..20",
            "      LetStmt 9..18",
            r#"        LiteralExpr 17..18 "1""#,
        ],
        &["ExpectedName at 13"],
    );
}

#[test]
fn a_malformed_suffix_belongs_to_the_latest_statement_recovery() {
    let source = "fn f() { let _ x }";
    check(
        source,
        &[
            "SourceFile 0..18",
            "  FnItem 0..18",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..18",
            r#"      LetStmt 9..14 "let _""#,
            r#"      Error 15..16 "x""#,
        ],
        &["ExpectedName at 13", "Expected(Eq) at 15"],
    );

    let lexed = lex(source).expect("test source fits in u32");
    let parse = parse(&ParserInput::new(&cook(source, &lexed)));
    let [ParseEvidence::Recovery(name), ParseEvidence::Recovery(eq)] = parse.evidence() else {
        panic!("the malformed statement has two recovery causes")
    };
    assert_eq!(name.kind, ParseRecoveryKind::Expected(ParseExpected::Name));
    assert!(name.skipped.is_empty());
    assert_eq!(
        eq.kind,
        ParseRecoveryKind::Expected(ParseExpected::Token(sumi_syntax::SyntaxKind::Eq))
    );
    let [skipped] = &*eq.skipped else {
        panic!("the latest recovery owns the malformed suffix")
    };
    assert_eq!(
        raw_text(source, &lexed, skipped.start(), skipped.end()),
        "x"
    );
}

#[test]
fn a_malformed_suffix_after_a_statement_is_reported_as_one() {
    // Neither `=` nor `else` can start a statement, so a boundary before
    // them would not help; each malformed suffix is one error run.
    check(
        "fn f() { x = 1 }",
        &[
            "SourceFile 0..16",
            "  FnItem 0..16",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..16",
            r#"      NameExpr 9..10 "x""#,
            r#"      Error 11..14 "= 1""#,
        ],
        &["ExpectedStatement at 11"],
    );
    check(
        "fn f() { x else }",
        &[
            "SourceFile 0..17",
            "  FnItem 0..17",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..17",
            r#"      NameExpr 9..10 "x""#,
            r#"      Error 11..15 "else""#,
        ],
        &["ExpectedStatement at 11"],
    );
}

#[test]
fn a_body_closes_at_the_nearest_matching_brace() {
    // Mechanical pairing is stable under suffix edits: the first `}` closes
    // the body and the malformed suffix stays at the top level.
    check(
        "fn f() {\n  a\n  } + b\n  c\n}\n\nfn g() {}",
        &[
            "SourceFile 0..37",
            "  FnItem 0..16",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..16",
            r#"      NameExpr 11..12 "a""#,
            r#"  Error 17..26 "+ b\n  c\n}""#,
            "  FnItem 28..37",
            r#"    ParamList 32..34 "()""#,
            r#"    Block 35..37 "{}""#,
        ],
        &["ExpectedItem at 17"],
    );
    // A doubled closer follows the same rule.
    check(
        "fn f() { a } }",
        &[
            "SourceFile 0..14",
            "  FnItem 0..12",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..12",
            r#"      NameExpr 9..10 "a""#,
            r#"  Error 13..14 "}""#,
        ],
        &["ExpectedItem at 13"],
    );
}

#[test]
fn an_orphan_closer_does_not_reparent_earlier_items() {
    check(
        "fn f() { a }\ng() {}\n}",
        &[
            "SourceFile 0..21",
            "  FnItem 0..12",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..12",
            r#"      NameExpr 9..10 "a""#,
            "  FnItem 13..19",
            r#"    ParamList 14..16 "()""#,
            r#"    Block 17..19 "{}""#,
            r#"  Error 20..21 "}""#,
        ],
        &["Expected(FnKw) at 13", "ExpectedItem at 20"],
    );
}

#[test]
fn an_unclosed_list_ends_where_its_line_does() {
    // The stream never closes the `(`, so it suspends no boundaries: the
    // line ends the list with one report, and `b` is the statement it is
    // rather than a second argument or part of the garbage.
    check(
        "fn f() { g(a\n  b\n}",
        &[
            "SourceFile 0..18",
            "  FnItem 0..18",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..18",
            "      CallExpr 9..12",
            r#"        NameExpr 9..10 "g""#,
            "        ArgList 10..12",
            r#"          NameExpr 11..12 "a""#,
            r#"      NameExpr 15..16 "b""#,
        ],
        &["Expected(RParen) at 15"],
    );
    check(
        "fn f() { g(* a\n  b\n}",
        &[
            "SourceFile 0..20",
            "  FnItem 0..20",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..20",
            "      CallExpr 9..14",
            r#"        NameExpr 9..10 "g""#,
            "        ArgList 10..14",
            r#"          Error 11..12 "*""#,
            r#"          NameExpr 13..14 "a""#,
            r#"      NameExpr 17..18 "b""#,
        ],
        &["ExpectedExpression at 11", "Expected(RParen) at 17"],
    );
    // A parameter list likewise: the next line is not a parameter.
    check(
        "fn f(a: int\n  x\nfn g() {}",
        &[
            "SourceFile 0..25",
            "  FnItem 0..11",
            "    ParamList 4..11",
            r#"      Param 5..11 "a: int""#,
            r#"  Error 14..15 "x""#,
            "  FnItem 16..25",
            r#"    ParamList 20..22 "()""#,
            r#"    Block 23..25 "{}""#,
        ],
        &[
            "Expected(RParen) at 14",
            "Expected(LBrace) at 14",
            "ExpectedItem at 14",
        ],
    );
}

#[test]
fn a_closed_list_owns_a_boundary_an_unclosed_brace_restores() {
    // The `)` pairs with the `(`, discarding the `{` in between; the `{`
    // restores boundaries all the same, so one sits before `b` inside the
    // closed list. The list owns everything through its `)` regardless.
    check(
        "fn f() { g(:{ a\nb) }",
        &[
            "SourceFile 0..20",
            "  FnItem 0..20",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..20",
            "      CallExpr 9..18",
            r#"        NameExpr 9..10 "g""#,
            "        ArgList 10..18",
            r#"          Error 11..13 ":{""#,
            r#"          NameExpr 14..15 "a""#,
            r#"          NameExpr 16..17 "b""#,
        ],
        &["ExpectedExpression at 11", "Expected(Comma) at 16"],
    );
    check(
        "fn f(a: { x\nb: int) {}",
        &[
            "SourceFile 0..22",
            "  FnItem 0..22",
            "    ParamList 4..19",
            r#"      Param 5..7 "a:""#,
            r#"      Error 8..18 "{ x\nb: int""#,
            r#"    Block 20..22 "{}""#,
        ],
        &["ExpectedType at 8", "ExpectedName at 8"],
    );
}

#[test]
fn garbage_where_an_expression_is_required_is_taken_as_such() {
    // The `*` displaced the operand, which is still there to parse: one
    // report, and the expression it was in stays whole.
    check(
        "fn f() { a + * b }",
        &[
            "SourceFile 0..18",
            "  FnItem 0..18",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..18",
            "      BinaryExpr 9..16",
            r#"        NameExpr 9..10 "a""#,
            r#"        Error 13..14 "*""#,
            r#"        NameExpr 15..16 "b""#,
        ],
        &["ExpectedExpression at 13"],
    );
    // In condition grammar a `)` before the operand cannot close anything;
    // it is garbage in the condition and the operand remains parseable.
    check(
        "fn f() { if ) x { a } }",
        &[
            "SourceFile 0..23",
            "  FnItem 0..23",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..23",
            "      IfExpr 9..21",
            r#"        Error 12..13 ")""#,
            r#"        NameExpr 14..15 "x""#,
            "        Block 16..21",
            r#"          NameExpr 18..19 "a""#,
        ],
        &["ExpectedExpression at 12"],
    );
    check(
        "fn f() { if else c { a } }",
        &[
            "SourceFile 0..26",
            "  FnItem 0..26",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..26",
            "      IfExpr 9..24",
            r#"        Error 12..16 "else""#,
            r#"        NameExpr 17..18 "c""#,
            "        Block 19..24",
            r#"          NameExpr 21..22 "a""#,
        ],
        &["ExpectedExpression at 12"],
    );
}

#[test]
fn a_statement_keyword_where_an_expression_is_required_begins_a_statement() {
    // The initializer is missing and the next statement has begun — on the
    // same line or, as while typing, the next: `let` is not garbage to
    // take, and the statement it begins is not missing a boundary.
    check(
        "fn f() { let x = let y = 1 }",
        &[
            "SourceFile 0..28",
            "  FnItem 0..28",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..28",
            r#"      LetStmt 9..16 "let x =""#,
            "      LetStmt 17..26",
            r#"        LiteralExpr 25..26 "1""#,
        ],
        &["ExpectedExpression at 17"],
    );
    check(
        "fn f() {\n  let x =\n  let y = 1\n}",
        &[
            "SourceFile 0..32",
            "  FnItem 0..32",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..32",
            r#"      LetStmt 11..18 "let x =""#,
            "      LetStmt 21..30",
            r#"        LiteralExpr 29..30 "1""#,
        ],
        &["ExpectedExpression at 21"],
    );
}

#[test]
fn a_closer_where_an_expression_is_required_is_left_to_its_owner() {
    // The paren is waiting for its `)`: the operand is missing, not the
    // closer garbage.
    check(
        "fn f() { !() }",
        &[
            "SourceFile 0..14",
            "  FnItem 0..14",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..14",
            "      PrefixExpr 9..12",
            r#"        ParenExpr 10..12 "()""#,
        ],
        &["ExpectedExpression at 11"],
    );
    // A missing prefix operand does not consume the argument list's closer,
    // even when a binary operator follows that closer.
    check(
        "fn f() { g(- ) == x }",
        &[
            "SourceFile 0..21",
            "  FnItem 0..21",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..21",
            "      BinaryExpr 9..19",
            "        CallExpr 9..14",
            r#"          NameExpr 9..10 "g""#,
            "          ArgList 10..14",
            r#"            PrefixExpr 11..12 "-""#,
            r#"        NameExpr 18..19 "x""#,
        ],
        &["ExpectedExpression at 13"],
    );
}

#[test]
fn each_failed_statement_owns_the_rest_of_its_line() {
    // The `+` fails at the `let`, whose strong introducer starts a new
    // statement. That malformed declaration then owns its `= 2` suffix.
    check(
        "fn f() { a + let b = 1 = 2 }",
        &[
            "SourceFile 0..28",
            "  FnItem 0..28",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..28",
            "      BinaryExpr 9..12",
            r#"        NameExpr 9..10 "a""#,
            "      LetStmt 13..22",
            r#"        LiteralExpr 21..22 "1""#,
            r#"      Error 23..26 "= 2""#,
        ],
        &["ExpectedExpression at 13", "ExpectedStatement at 23"],
    );
}

#[test]
fn a_body_whose_closer_an_inner_block_took_ends_at_the_next_item() {
    // The malformed statement stays local. Its `{` does not consume the
    // enclosing body's closer, and `fn` still begins the next item.
    check(
        "fn f() { (a { b) }\nfn g() {}",
        &[
            "SourceFile 0..28",
            "  FnItem 0..18",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..18",
            "      ParenExpr 9..11",
            r#"        NameExpr 10..11 "a""#,
            r#"      Error 12..16 "{ b)""#,
            "  FnItem 19..28",
            r#"    ParamList 23..25 "()""#,
            r#"    Block 26..28 "{}""#,
        ],
        &["Expected(RParen) at 12"],
    );
}

#[test]
fn a_non_recovery_report_does_not_trigger_statement_recovery() {
    // The spaced `-` is complained about and taken; `- x` parses whole, so
    // the `y` after it is a second statement missing its boundary.
    check(
        "fn f() { - x y }",
        &[
            "SourceFile 0..16",
            "  FnItem 0..16",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..16",
            "      PrefixExpr 9..12",
            r#"        NameExpr 11..12 "x""#,
            r#"      NameExpr 13..14 "y""#,
        ],
        &["SpacedPrefixOperator at 9", "ExpectedBoundary at 13"],
    );
}

#[test]
fn lexer_errors_do_not_hide_statement_recovery() {
    // The lexer owns the primary diagnostic for `€`, while the parser retains
    // the independent fact that it was unexpected. The ambiguous `c` belongs
    // to the malformed statement rather than becoming a new statement.
    let source = "fn f() { a € + b c }";
    check(
        source,
        &[
            "SourceFile 0..22",
            "  FnItem 0..22",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..22",
            "      BinaryExpr 9..18",
            r#"        NameExpr 9..10 "a""#,
            r#"        Error 11..14 "€""#,
            r#"        NameExpr 17..18 "b""#,
            r#"      Error 19..20 "c""#,
        ],
        &["Unexpected at 11"],
    );

    let lexed = lex(source).expect("test source fits in u32");
    let parse = parse(&ParserInput::new(&cook(source, &lexed)));
    let [ParseEvidence::Recovery(recovery)] = parse.evidence() else {
        panic!("the malformed statement has one recovery cause")
    };
    let skipped: Vec<_> = recovery
        .skipped
        .iter()
        .map(|range| raw_text(source, &lexed, range.start(), range.end()))
        .collect();
    assert_eq!(skipped, ["€", "c"]);
}

#[test]
fn displaced_brackets_are_recovered_by_their_grammar_context() {
    // A `}` where an operand continues is garbage in the discard statement,
    // rather than the end of its enclosing block.
    check(
        "fn f() { _ = } r\"a\"\n  x\n}",
        &[
            "SourceFile 0..25",
            "  FnItem 0..25",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..25",
            "      DiscardStmt 9..19",
            r#"        Error 13..14 "}""#,
            r#"        LiteralExpr 15..19 "r\"a\"""#,
            r#"      NameExpr 22..23 "x""#,
        ],
        &["ExpectedExpression at 13"],
    );
    // A `{` inside a paren that an operator follows is no block: the
    // expression runs straight through it, with one report.
    check(
        "fn f() { (a { * b) }",
        &[
            "SourceFile 0..20",
            "  FnItem 0..20",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..20",
            "      ParenExpr 9..18",
            "        BinaryExpr 10..17",
            r#"          NameExpr 10..11 "a""#,
            r#"          Error 12..13 "{""#,
            r#"          NameExpr 16..17 "b""#,
        ],
        &["Unexpected at 12"],
    );
    // At an argument position `{` is valid block syntax. The missing comma
    // is reported and the malformed block owns its contents.
    check(
        "fn f() { g(a\n  { % b) }",
        &[
            "SourceFile 0..23",
            "  FnItem 0..23",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..23",
            "      CallExpr 9..21",
            r#"        NameExpr 9..10 "g""#,
            "        ArgList 10..21",
            r#"          NameExpr 11..12 "a""#,
            "          Block 15..20",
            r#"            Error 17..20 "% b""#,
        ],
        &[
            "Expected(Comma) at 15",
            "ExpectedStatement at 17",
            "Expected(RBrace) at 20",
        ],
    );
}

#[test]
fn a_matched_bracket_keeps_its_structural_role() {
    // The body's `}` is balanced by its `{`: it closes the body, and the
    // `= b` is garbage between items.
    check(
        "fn f() { a } = b",
        &[
            "SourceFile 0..16",
            "  FnItem 0..12",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..12",
            r#"      NameExpr 9..10 "a""#,
            r#"  Error 13..16 "= b""#,
        ],
        &["ExpectedItem at 13"],
    );
    // The `if`'s block is balanced by its `}`: it is the block, and the
    // `+ b` is garbage inside it.
    check(
        "fn f() { (if a { + b }) }",
        &[
            "SourceFile 0..25",
            "  FnItem 0..25",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..25",
            "      ParenExpr 9..23",
            "        IfExpr 10..22",
            r#"          NameExpr 13..14 "a""#,
            "          Block 15..22",
            r#"            Error 17..20 "+ b""#,
        ],
        &["ExpectedStatement at 17"],
    );
}

#[test]
fn an_unclosed_list_recovers_a_displaced_closer() {
    // The `}` stands where the argument continues, so list recovery owns it
    // and the line still ends the unclosed list.
    check(
        "fn f() { g(a } = b\nc\n}",
        &[
            "SourceFile 0..22",
            "  FnItem 0..22",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..22",
            "      CallExpr 9..18",
            r#"        NameExpr 9..10 "g""#,
            "        ArgList 10..18",
            r#"          NameExpr 11..12 "a""#,
            r#"          Error 13..16 "} =""#,
            r#"          NameExpr 17..18 "b""#,
            r#"      NameExpr 19..20 "c""#,
        ],
        &["ExpectedExpression at 13", "Expected(RParen) at 19"],
    );
}

#[test]
fn garbage_skipped_in_an_expression_leaves_the_operator_spaced() {
    // Without the `:`, `a + b` is spaced as it should be: the space before
    // the garbage counts for the operator.
    check(
        "fn f() { a :+ b }",
        &[
            "SourceFile 0..17",
            "  FnItem 0..17",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..17",
            "      BinaryExpr 9..15",
            r#"        NameExpr 9..10 "a""#,
            r#"        Error 11..12 ":""#,
            r#"        NameExpr 14..15 "b""#,
        ],
        &["Unexpected at 11"],
    );
}

#[test]
fn a_surplus_brace_where_no_block_is_written_is_garbage() {
    // The `{` split an `&&`: a lone `&` on either side is wrong on both, so
    // statement recovery owns the whole malformed run. The body keeps its
    // `}` and the statement after.
    check(
        "fn f() { a &{ & b\n  c\n}",
        &[
            "SourceFile 0..23",
            "  FnItem 0..23",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..23",
            r#"      NameExpr 9..10 "a""#,
            r#"      Error 11..17 "&{ & b""#,
            r#"      NameExpr 20..21 "c""#,
        ],
        &["ExpectedStatement at 11"],
    );
    // Inside a paren before its `)`: garbage between the operand and the
    // closer, skipped so that the paren closes.
    check(
        "fn f() { (foo{ ) }",
        &[
            "SourceFile 0..18",
            "  FnItem 0..18",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..18",
            "      ParenExpr 9..16",
            r#"        NameExpr 10..13 "foo""#,
            r#"        Error 13..14 "{""#,
        ],
        &["Unexpected at 13"],
    );
    // After a `let`, where no block is written.
    check(
        "fn f() { let { a = 1\n  b\n}",
        &[
            "SourceFile 0..26",
            "  FnItem 0..26",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..26",
            r#"      LetStmt 9..12 "let""#,
            r#"      Error 13..20 "{ a = 1""#,
            r#"      NameExpr 23..24 "b""#,
        ],
        &["ExpectedName at 13", "Expected(Eq) at 13"],
    );
}

#[test]
fn a_matched_block_is_never_blamed_for_another_surplus() {
    // Each source has one unmatched `{`. The mechanically matched blocks
    // keep their structural role; the final opener is top-level garbage.
    check(
        "fn f() { (if a { + b }) } {",
        &[
            "SourceFile 0..27",
            "  FnItem 0..25",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..25",
            "      ParenExpr 9..23",
            "        IfExpr 10..22",
            r#"          NameExpr 13..14 "a""#,
            "          Block 15..22",
            r#"            Error 17..20 "+ b""#,
            r#"  Error 26..27 "{""#,
        ],
        &["ExpectedStatement at 17", "ExpectedItem at 26"],
    );
    check(
        "fn f() { let x = { + b } } {",
        &[
            "SourceFile 0..28",
            "  FnItem 0..26",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..26",
            "      LetStmt 9..24",
            "        Block 17..24",
            r#"          Error 19..22 "+ b""#,
            r#"  Error 27..28 "{""#,
        ],
        &["ExpectedStatement at 19", "ExpectedItem at 27"],
    );
    // A `fn` inside a block is garbage the block owns, not an item that
    // starts the count of brackets afresh.
    check(
        "fn f() { ({ fn }) }",
        &[
            "SourceFile 0..19",
            "  FnItem 0..19",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..19",
            "      ParenExpr 9..17",
            "        Block 10..16",
            r#"          Error 12..14 "fn""#,
        ],
        &["ExpectedStatement at 12"],
    );
}
