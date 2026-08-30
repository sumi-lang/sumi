mod common;

use sumi_lexer::lex;
use sumi_syntax::{ParserInput, cook, parse};

/// Parse `source`; assert the tree dump and the errors, each rendered as
/// `Kind at byte`.
#[track_caller]
fn check(source: &str, tree: &[&str], errors: &[&str]) {
    let lexed = lex(source).expect("test sources fit in u32");
    let cooked = cook(source, &lexed);
    let parse = parse(&ParserInput::new(&cooked));
    assert_eq!(
        common::dump(parse.tree(), &lexed, source),
        tree,
        "tree for {source:?}"
    );
    let actual: Vec<String> = parse
        .errors()
        .iter()
        .map(|error| {
            format!(
                "{:?} at {}",
                error.kind,
                common::start_byte(&lexed, error.token)
            )
        })
        .collect();
    assert_eq!(actual, errors, "errors for {source:?}");
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
    // line, whatever the newline rule says about the tokens around it —
    // and the parts missing once it has ended are covered by one report.
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
        &["Expected(LParen) at 5", "ExpectedItem at 7"],
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
        &["Expected(RParen) at 11"],
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
        &["Expected(RBrace) at 19"],
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
        &["ExpectedType at 8"],
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
fn tokens_reported_earlier_are_absorbed_silently() {
    check(
        "fn f() {\n  a ;\n  b\n}",
        &[
            "SourceFile 0..20",
            "  FnItem 0..20",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..20",
            r#"      NameExpr 11..12 "a""#,
            r#"      Error 13..14 ";""#,
            r#"      NameExpr 17..18 "b""#,
        ],
        &[],
    );
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
            "      IfExpr 9..17",
            r#"        NameExpr 12..13 "a""#,
            r#"        Block 14..17 "{ }""#,
        ],
        &["BlockOnNewLine at 14"],
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
        &["Expected(RParen) at 12"],
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
        &["Expected(RParen) at 6"],
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
    // The stray `{` must not let the run swallow the argument list's `)`.
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

/// Parse `source` and return its error kinds, asserting the tree is well
/// formed.
fn error_kinds(source: &str) -> Vec<sumi_syntax::ParseErrorKind> {
    let lexed = lex(source).expect("test sources fit in u32");
    let parse = parse(&ParserInput::new(&cook(source, &lexed)));
    let _ = common::dump(parse.tree(), &lexed, source);
    parse.errors().iter().map(|error| error.kind).collect()
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
    // The `)` closes the `(` around the block: the block is unclosed, and
    // the `)` is not its to skip.
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
    // A `)` with nothing to close is garbage, skipped where it stands.
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
        &["ExpectedStatement at 13"],
    );
}

#[test]
fn a_block_does_not_yield_to_a_paren_opened_inside_it() {
    // `(a` recovered before `b`; the later `)` is garbage in the block, not
    // a closer the block must yield to.
    check(
        "fn f() { (a b) }",
        &[
            "SourceFile 0..16",
            "  FnItem 0..16",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..16",
            "      ParenExpr 9..11",
            r#"        NameExpr 10..11 "a""#,
            r#"      NameExpr 12..13 "b""#,
            r#"      Error 13..14 ")""#,
        ],
        &["Expected(RParen) at 12"],
    );
    // The same with a block in between: the parser's own state, not the
    // token stream's bracket matching, decides — so neither block yields.
    check(
        "fn f() { (a { b) } }",
        &[
            "SourceFile 0..20",
            "  FnItem 0..20",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..20",
            "      ParenExpr 9..11",
            r#"        NameExpr 10..11 "a""#,
            "      Block 12..18",
            r#"        NameExpr 14..15 "b""#,
            r#"        Error 15..16 ")""#,
        ],
        &["Expected(RParen) at 12", "ExpectedStatement at 15"],
    );
}

#[test]
fn a_block_yields_only_to_a_paren_the_parser_still_has_open() {
    // The stream pairs the `)` with the `(` of `(a`, which recovery closed
    // at the `{`: nothing is waiting for it. The inner block keeps it as
    // garbage rather than cutting itself short, and every closer after it
    // lands where it belongs.
    check(
        "fn f() { ({ (a { b) } }) }",
        &[
            "SourceFile 0..26",
            "  FnItem 0..26",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..26",
            "      ParenExpr 9..24",
            "        Block 10..23",
            "          ParenExpr 12..14",
            r#"            NameExpr 13..14 "a""#,
            "          Block 15..21",
            r#"            NameExpr 17..18 "b""#,
            r#"            Error 18..19 ")""#,
        ],
        &["Expected(RParen) at 15", "ExpectedStatement at 18"],
    );
}

#[test]
fn an_opener_nothing_closes_does_not_extend_a_skipped_run() {
    // The stream pairs the stray `(` with nothing — the `}` discards it —
    // so the run does not nest at it: the `,` ends the run, and `b` is an
    // argument after all.
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
        &["Expected(Eq) at 19"],
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
        &["Expected(Eq) at 19"],
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
        &["Expected(Eq) at 15"],
    );
    check(
        "fn f()\n-> int {}",
        &[
            "SourceFile 0..16",
            "  FnItem 0..6",
            r#"    ParamList 4..6 "()""#,
            r#"  Error 7..16 "-> int {}""#,
        ],
        &["Expected(LBrace) at 7"],
    );
    check(
        "fn f\n() {}",
        &[
            "SourceFile 0..10",
            r#"  FnItem 0..4 "fn f""#,
            r#"  Error 5..10 "() {}""#,
        ],
        &["Expected(LParen) at 5"],
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
            r#"      ParenExpr 12..14 "()""#,
            r#"      Error 14..15 ")""#,
        ],
        &["Expected(RParen) at 12", "ExpectedExpression at 13"],
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
    use sumi_syntax::ParseErrorKind::ExpectedItem;
    let n = 50_000;
    let source = format!(":{}{}{}", "{".repeat(n), "(".repeat(n), ")".repeat(n));
    assert_eq!(error_kinds(&source), [ExpectedItem]);
}

#[test]
fn nesting_is_bounded() {
    use sumi_syntax::ParseErrorKind::{Expected, ExpectedExpression, NestingTooDeep};
    use sumi_syntax::{MAX_DEPTH, SyntaxKind};
    let deep = |n: usize| format!("fn f() {{ {}x{} }}", "(".repeat(n), ")".repeat(n));
    assert_eq!(error_kinds(&deep(MAX_DEPTH as usize / 2)), []);
    // At the limit with nothing left, or with a closer: no recovery run to
    // take a token that is not an expression's.
    let opens = |n: u32| format!("fn f() {{ {}", "(".repeat(n as usize));
    assert_eq!(error_kinds(&opens(MAX_DEPTH - 2)), [ExpectedExpression]);
    // The `)` closes the innermost paren; the rest stay open to the end.
    assert_eq!(
        error_kinds(&format!("{})", opens(MAX_DEPTH - 2))),
        [ExpectedExpression, Expected(SyntaxKind::RParen)]
    );
    assert_eq!(
        error_kinds(&opens(MAX_DEPTH + 40)),
        [NestingTooDeep, Expected(SyntaxKind::RParen)]
    );
    // The skip past the limit stops at the next item like any recovery:
    // the parens are unclosed, so the `fn` is not theirs to take.
    let next_item = format!("{}x fn g() {{}}", opens(MAX_DEPTH + 40));
    assert_eq!(
        error_kinds(&next_item),
        [NestingTooDeep, Expected(SyntaxKind::RParen)]
    );
    assert_eq!(items(&next_item), 2);
    // Far past the limit: one error, no crash, and the file still closes.
    assert_eq!(error_kinds(&deep(100_000)), [NestingTooDeep]);
    assert_eq!(
        error_kinds(&format!("fn f() {{ {}x }}", "!".repeat(100_000))),
        [NestingTooDeep]
    );
    assert_eq!(
        error_kinds(&format!(
            "fn f() {{ {}if a {{}} }}",
            "if a {} else ".repeat(100_000)
        )),
        [NestingTooDeep]
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
fn a_stray_token_after_a_statement_is_reported_as_one() {
    // Neither `=` nor `else` can start a statement, so a boundary before
    // them would not help: they are the strays, and the report says so.
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
fn a_stray_brace_inside_a_body_is_a_stray_statement() {
    // The stream pairs the body's `{` with the last `}` before the next
    // item, so the `}` in the middle is a stray inside the body — reported
    // as one, with the statements after it still in the body — rather than
    // the body's end, with everything after it garbage between items.
    check(
        "fn f() {\n  a\n  } + b\n  c\n}\n\nfn g() {}",
        &[
            "SourceFile 0..37",
            "  FnItem 0..26",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..26",
            r#"      NameExpr 11..12 "a""#,
            r#"      Error 15..20 "} + b""#,
            r#"      NameExpr 23..24 "c""#,
            "  FnItem 28..37",
            r#"    ParamList 32..34 "()""#,
            r#"    Block 35..37 "{}""#,
        ],
        &["ExpectedStatement at 15"],
    );
    // A doubled closer is the other way round: nothing but the second `}`
    // follows the first, so the first is the body's end and the second is
    // garbage between items — where the error belongs.
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
        &["Expected(RParen) at 14"],
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
        &["ExpectedType at 8"],
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
}

#[test]
fn what_follows_a_failed_statement_on_its_line_is_its_fallout() {
    // The `if` fails at the `)`, which nothing owns. The rest of the line
    // is parsed without further comment: `x` is not missing a boundary and
    // the `)` is not a second failure.
    check(
        "fn f() { if ) x { a } }",
        &[
            "SourceFile 0..23",
            "  FnItem 0..23",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..23",
            r#"      IfExpr 9..11 "if""#,
            r#"      Error 12..13 ")""#,
            r#"      NameExpr 14..15 "x""#,
            "      Block 16..21",
            r#"        NameExpr 18..19 "a""#,
        ],
        &["ExpectedExpression at 12"],
    );
}

#[test]
fn a_body_whose_closer_an_inner_block_took_ends_at_the_next_item() {
    // The `)` discards the inner `{` in the stream, so the `}` is the
    // body's; the parser's unclosed inner block takes it anyway, there
    // being nothing better. The body's closer is then behind it, and the
    // `fn` begins the next item rather than garbage the body owns.
    check(
        "fn f() { (a { b) }\nfn g() {}",
        &[
            "SourceFile 0..28",
            "  FnItem 0..18",
            r#"    ParamList 4..6 "()""#,
            "    Block 7..18",
            "      ParenExpr 9..11",
            r#"        NameExpr 10..11 "a""#,
            "      Block 12..18",
            r#"        NameExpr 14..15 "b""#,
            r#"        Error 15..16 ")""#,
            "  FnItem 19..28",
            r#"    ParamList 23..25 "()""#,
            r#"    Block 26..28 "{}""#,
        ],
        &[
            "Expected(RParen) at 12",
            "ExpectedStatement at 15",
            "Expected(RBrace) at 19",
        ],
    );
}

#[test]
fn a_report_on_the_way_does_not_make_the_line_fallout() {
    // The spaced `-` is complained about and taken; `- x` parses whole, so
    // the `y` after it is a second statement missing its boundary, not
    // fallout to pass over in silence.
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
