use sumi_lexer::lex;
use sumi_syntax::{ParserInput, SyntaxKind, cook};

/// Lex, cook, and stream `source`, assert the stream invariants, and render
/// one line per significant token: `Kind "text"` plus `newline`, `boundary`,
/// `joint`, and `partner N` markers. `newline`/`boundary` describe the gap
/// before the token; `joint` glues it to the next one; `partner` names the
/// bracket matching it.
fn dump(source: &str) -> Vec<String> {
    let lexed = lex(source).expect("test sources fit in u32");
    let cooked = cook(source, &lexed);
    let input = ParserInput::new(&cooked);

    let mut previous = None;
    (0..input.len())
        .map(|index| {
            let kind = input.get(index).expect("indices below len are present");
            let token = input.token(index) as usize;

            assert!(
                !matches!(
                    kind,
                    SyntaxKind::Whitespace | SyntaxKind::Newline | SyntaxKind::LineComment
                ),
                "token {index} is trivia"
            );
            assert_eq!(kind, cooked.kind(token), "kinds must come from the cook");
            if let Some(previous) = previous {
                assert!(token > previous, "token indices must increase");
            }
            previous = Some(token);
            if input.boundary_before(index) {
                assert!(index > 0, "no boundary before the first token");
                assert!(input.newline_before(index), "boundaries need a newline");
            }

            let mut line = format!("{:?} {:?}", kind, lexed.text(source, token));
            if input.newline_before(index) {
                line.push_str(" newline");
            }
            if input.boundary_before(index) {
                line.push_str(" boundary");
            }
            if input.is_joint(index) {
                line.push_str(" joint");
            }
            if let Some(partner) = input.partner(index) {
                assert_eq!(
                    input.partner(partner),
                    Some(index),
                    "partners must be mutual"
                );
                let (opener, closer) = if index < partner {
                    (index, partner)
                } else {
                    (partner, index)
                };
                assert!(
                    matches!(
                        (input.get(opener), input.get(closer)),
                        (Some(SyntaxKind::LParen), Some(SyntaxKind::RParen))
                            | (Some(SyntaxKind::LBrace), Some(SyntaxKind::RBrace))
                    ),
                    "partners must be a matching pair"
                );
                line.push_str(&format!(" partner {partner}"));
            }
            line
        })
        .collect()
}

#[track_caller]
fn check(source: &str, expected: &[&str]) {
    assert_eq!(dump(source), expected, "for source {source:?}");
}

/// Whether any statement boundary occurs in `source`.
#[track_caller]
fn has_boundary(source: &str) -> bool {
    dump(source); // invariants
    let lexed = lex(source).expect("test sources fit in u32");
    let input = ParserInput::new(&cook(source, &lexed));
    (0..input.len()).any(|index| input.boundary_before(index))
}

#[test]
fn empty_and_trivia_only_sources_have_no_tokens() {
    check("", &[]);
    check("  // c\n\n", &[]);

    let input = ParserInput::new(&cook("", &lex("").unwrap()));
    assert!(input.is_empty());
    assert_eq!(input.get(0), None);
}

#[test]
fn trivia_is_stripped() {
    check(
        "let x = 1 // bind\n",
        &[
            r#"LetKw "let""#,
            r#"Ident "x""#,
            r#"Eq "=""#,
            r#"IntLiteral "1""#,
        ],
    );
}

#[test]
fn lookahead_past_the_end_is_none() {
    let input = ParserInput::new(&cook("x", &lex("x").unwrap()));
    assert_eq!(input.get(0), Some(SyntaxKind::Ident));
    assert_eq!(input.get(1), None);
    assert!(!input.is_joint(0));
}

#[test]
fn jointness_tracks_adjacency() {
    check(
        "x >>= 2",
        &[
            r#"Ident "x""#,
            r#"Gt ">" joint"#,
            r#"Gt ">" joint"#,
            r#"Eq "=""#,
            r#"IntLiteral "2""#,
        ],
    );
    check(
        "a+b",
        &[r#"Ident "a" joint"#, r#"Plus "+" joint"#, r#"Ident "b""#],
    );
    check("a + b", &[r#"Ident "a""#, r#"Plus "+""#, r#"Ident "b""#]);
}

#[test]
fn newlines_end_statements() {
    check(
        "let a = 1\nlet b = 2",
        &[
            r#"LetKw "let""#,
            r#"Ident "a""#,
            r#"Eq "=""#,
            r#"IntLiteral "1""#,
            r#"LetKw "let" newline boundary"#,
            r#"Ident "b""#,
            r#"Eq "=""#,
            r#"IntLiteral "2""#,
        ],
    );
}

#[test]
fn incomplete_lines_continue() {
    // The left look: a token that cannot end a statement keeps the line
    // open, whatever follows. (Trailing `&&` still parses; banning the
    // trailing style is the parser's error.)
    assert!(!has_boundary("let x =\n1"));
    assert!(!has_boundary("a &&\nb"));
    assert!(!has_boundary("let\nmut x = 1"));
}

#[test]
fn leading_operators_continue() {
    // The right look: tokens that can never start a statement continue the
    // previous line.
    assert!(!has_boundary("a\n+ b"));
    assert!(!has_boundary("a\n* b"));
    assert!(!has_boundary("a\n/ b"));
    assert!(!has_boundary("a\n% b"));
    assert!(!has_boundary("a\n< b"));
    assert!(!has_boundary("a\n> b"));
    assert!(!has_boundary("a\n<= b"));
    assert!(!has_boundary("a\n== b"));
    assert!(!has_boundary("a\n!= b"));
    assert!(!has_boundary("a\n&& b"));
    assert!(!has_boundary("a\n|| b"));

    // A lone `=`, `&`, `|`, or `!` is not a binary operator: fresh statement.
    assert!(has_boundary("a\n= b"));
    assert!(has_boundary("a\n& b"));
    assert!(has_boundary("a\n| b"));
    assert!(has_boundary("a\n!b"));
    // Nor is `.`, until member access exists.
    assert!(has_boundary("a\n.b()"));
}

#[test]
fn leading_minus_arity_is_jointness() {
    // Spaced: binary, the line continues. Glued: a negation starts fresh.
    assert!(!has_boundary("a\n- b"));
    assert!(has_boundary("a\n-b"));
    // A joint `->` is an arrow, never a continuation.
    assert!(has_boundary("f(x)\n-> int"));
}

#[test]
fn call_arguments_stay_on_the_callee_line() {
    // `(` never continues a line: the JavaScript `f\n(x)` hazard is two
    // statements here, loudly.
    assert!(has_boundary("f\n(x)"));
}

#[test]
fn leading_dots_do_not_continue_until_member_access_exists() {
    // The continuation set mirrors the grammar, which has no `.` yet; a
    // leading `.` joins it with member access, and this test flips then.
    check(
        "let value = base\n    .offset(dx)\n    .scale(2)\nlet other = 1",
        &[
            r#"LetKw "let""#,
            r#"Ident "value""#,
            r#"Eq "=""#,
            r#"Ident "base""#,
            r#"Dot "." newline boundary joint"#,
            r#"Ident "offset" joint"#,
            r#"LParen "(" joint partner 8"#,
            r#"Ident "dx" joint"#,
            r#"RParen ")" partner 6"#,
            r#"Dot "." newline boundary joint"#,
            r#"Ident "scale" joint"#,
            r#"LParen "(" joint partner 13"#,
            r#"IntLiteral "2" joint"#,
            r#"RParen ")" partner 11"#,
            r#"LetKw "let" newline boundary"#,
            r#"Ident "other""#,
            r#"Eq "=""#,
            r#"IntLiteral "1""#,
        ],
    );
}

#[test]
fn continuations_may_span_blank_lines_and_comments() {
    assert!(!has_boundary("a // trailing\n+ b"));
    assert!(!has_boundary("a\n\n+ b"));
}

#[test]
fn parens_suspend_termination() {
    assert!(!has_boundary("f(a\nb)"));
    check(
        "f(a,\nb)",
        &[
            r#"Ident "f" joint"#,
            r#"LParen "(" joint partner 5"#,
            r#"Ident "a" joint"#,
            r#"Comma ",""#,
            r#"Ident "b" newline joint"#,
            r#"RParen ")" partner 1"#,
        ],
    );
}

#[test]
fn braces_restore_termination() {
    check(
        "f({ a\nb })",
        &[
            r#"Ident "f" joint"#,
            r#"LParen "(" joint partner 6"#,
            r#"LBrace "{" partner 5"#,
            r#"Ident "a""#,
            r#"Ident "b" newline boundary"#,
            r#"RBrace "}" joint partner 2"#,
            r#"RParen ")" partner 1"#,
        ],
    );
}

#[test]
fn braces_do_not_continue() {
    // `{` can start a block statement, so it never continues a line: the
    // brace of an `if` or `fn` must open on the same line.
    assert!(has_boundary("if c\n{}"));
    assert!(has_boundary("{ a }\n{ b }"));
}

#[test]
fn else_continues_the_previous_line() {
    assert!(!has_boundary("if c {}\nelse {}"));
    assert!(has_boundary("if c {}\nx"));
}

#[test]
fn bare_return_can_end_a_statement() {
    assert!(has_boundary("return\nx"));
    assert!(!has_boundary("return a\n+ b"));
}

#[test]
fn embedded_newlines_are_not_boundaries() {
    // The break sits inside the string token, not in trivia.
    assert!(!has_boundary("let s = \"a\nb\""));
}

#[test]
fn error_tokens_end_statements() {
    // Recovery: garbage ends at the line break instead of swallowing the
    // next statement.
    assert!(has_boundary("€\nx"));
}

#[test]
fn brackets_pair_and_closers_synchronize() {
    check(
        "{(a)}",
        &[
            r#"LBrace "{" joint partner 4"#,
            r#"LParen "(" joint partner 3"#,
            r#"Ident "a" joint"#,
            r#"RParen ")" joint partner 1"#,
            r#"RBrace "}" partner 0"#,
        ],
    );
    // A closer pops openers until its match: the `(` a `}` discards on the
    // way to its `{` partners with nothing, and a `)` after that has
    // nothing left to close.
    check(
        "{(a})",
        &[
            r#"LBrace "{" joint partner 3"#,
            r#"LParen "(" joint"#,
            r#"Ident "a" joint"#,
            r#"RBrace "}" joint partner 0"#,
            r#"RParen ")""#,
        ],
    );
    // A closer with no match is an orphan. A `}` with no `{` open abandons
    // the `(`s left open; a `)` with no `(` open discards nothing, so the
    // `{` it sits inside still pairs.
    check(
        "(a}",
        &[r#"LParen "(" joint"#, r#"Ident "a" joint"#, r#"RBrace "}""#],
    );
    check(")(", &[r#"RParen ")" joint"#, r#"LParen "(""#]);
    check(
        "{a)b}",
        &[
            r#"LBrace "{" joint partner 4"#,
            r#"Ident "a" joint"#,
            r#"RParen ")" joint"#,
            r#"Ident "b" joint"#,
            r#"RBrace "}" partner 0"#,
        ],
    );
}

#[test]
fn a_body_closes_at_the_first_of_the_last_run_of_braces() {
    // The `{` at the bottom of the stack is an item's body. A `}` reaching
    // it with statements and a later `}` after it is a stray inside the
    // body, so the body pairs with the later one.
    check(
        "{a}b}",
        &[
            r#"LBrace "{" joint partner 4"#,
            r#"Ident "a" joint"#,
            r#"RBrace "}" joint"#,
            r#"Ident "b" joint"#,
            r#"RBrace "}" partner 0"#,
        ],
    );
    // One with nothing but closers after it is the body's end, and those
    // closers are the strays.
    check(
        "{a}}",
        &[
            r#"LBrace "{" joint partner 2"#,
            r#"Ident "a" joint"#,
            r#"RBrace "}" joint partner 0"#,
            r#"RBrace "}""#,
        ],
    );
    check(
        "{a})}",
        &[
            r#"LBrace "{" joint partner 2"#,
            r#"Ident "a" joint"#,
            r#"RBrace "}" joint partner 0"#,
            r#"RParen ")" joint"#,
            r#"RBrace "}""#,
        ],
    );
    // The only `}` to reach the body is its end whatever follows: garbage
    // between items is likelier than a stray with the real closer missing,
    // and costs one error where the other reading costs two.
    check(
        "{a}b",
        &[
            r#"LBrace "{" joint partner 2"#,
            r#"Ident "a" joint"#,
            r#"RBrace "}" joint partner 0"#,
            r#"Ident "b""#,
        ],
    );
    check(
        "{a}(b)",
        &[
            r#"LBrace "{" joint partner 2"#,
            r#"Ident "a" joint"#,
            r#"RBrace "}" joint partner 0"#,
            r#"LParen "(" joint partner 5"#,
            r#"Ident "b" joint"#,
            r#"RParen ")" partner 3"#,
        ],
    );
    check(
        "{a}b fn g(){}",
        &[
            r#"LBrace "{" joint partner 2"#,
            r#"Ident "a" joint"#,
            r#"RBrace "}" joint partner 0"#,
            r#"Ident "b""#,
            r#"FnKw "fn""#,
            r#"Ident "g" joint"#,
            r#"LParen "(" joint partner 7"#,
            r#"RParen ")" joint partner 6"#,
            r#"LBrace "{" joint partner 9"#,
            r#"RBrace "}" partner 8"#,
        ],
    );
    // A `fn` settles it: the pairing never reaches into the next item.
    check(
        "{a} fn {b}",
        &[
            r#"LBrace "{" joint partner 2"#,
            r#"Ident "a" joint"#,
            r#"RBrace "}" partner 0"#,
            r#"FnKw "fn""#,
            r#"LBrace "{" joint partner 6"#,
            r#"Ident "b" joint"#,
            r#"RBrace "}" partner 4"#,
        ],
    );
    // Inner braces pair as they come; only the bottom one waits.
    check(
        "{{a}}b}",
        &[
            r#"LBrace "{" joint partner 6"#,
            r#"LBrace "{" joint partner 3"#,
            r#"Ident "a" joint"#,
            r#"RBrace "}" joint partner 1"#,
            r#"RBrace "}" joint"#,
            r#"Ident "b" joint"#,
            r#"RBrace "}" partner 0"#,
        ],
    );
}

#[test]
fn unbalanced_closers_do_not_wedge_termination() {
    assert!(has_boundary(")\nx"));
    assert!(has_boundary("f(a))\nx"));
    assert!(has_boundary("{\nf(a\n}\nx"));
    assert!(has_boundary("(a }\nx"));
    assert!(has_boundary("{a )\nx"));
    assert!(has_boundary("({a )\nx"));
}

#[test]
fn large_opposite_delimiter_run_recovers() {
    let mut source = "(".repeat(4096);
    source.push('a');
    source.push_str(&"}".repeat(4096));
    source.push_str("\nx");
    assert!(has_boundary(&source));
}
