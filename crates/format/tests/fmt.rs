//! The formatter's policy, one witness per rule, and its contract on
//! sources the parser recovered in.

use sumi_format::{Formatted, format, rep};
use sumi_lexer::lex;
use sumi_syntax::{ParserInput, parse};

fn fmt(source: &str) -> Formatted {
    let lexed = lex(source).expect("test sources fit in u32");
    let parsed = parse(&ParserInput::new(&lexed));
    format(source, &lexed, &parsed).expect("no defect")
}

#[track_caller]
fn check(source: &str, expected: &str) {
    let formatted = fmt(source);
    assert_eq!(formatted.text, expected, "formatting {source:?}");
    assert_eq!(formatted.reverted, 0, "reverted items in {source:?}");
    let again = fmt(&formatted.text);
    assert_eq!(again.text, formatted.text, "not a fixed point: {source:?}");
    assert!(again.edits.is_empty(), "a fixed point has no edits");
    assert_eq!(
        sumi_text::apply(source, &formatted.edits),
        formatted.text,
        "the edits are the text"
    );
}

#[test]
fn spacing_is_canonical_and_indentation_is_four_spaces() {
    check(
        "fn f(a:int,b:int)->int{let x=a+b\nreturn x*2}",
        "fn f(a: int, b: int) -> int {\n    let x = a + b\n    return x * 2\n}\n",
    );
    check(
        "fn f() {\n  let mut x = -  1\n  x = ! y\n  _ = f (x)\n}",
        "fn f() {\n    let mut x = -1\n    x = !y\n    _ = f(x)\n}\n",
    );
}

#[test]
fn blocks_are_vertical_and_else_chains_stay_chains() {
    check(
        "fn f() { if a<b {\n a } else if c { b }else {\n c } }",
        "fn f() {\n    if a < b {\n        a\n    } else if c {\n        b\n    } else {\n        c\n    }\n}\n",
    );
    check("fn f() { }", "fn f() {}\n");
}

#[test]
fn items_are_separated_by_lines_and_blank_lines_are_retained_singly() {
    check(
        "// header\n\n\nfn f() {}\n\n\nfn g() = 1\n// tail\n",
        "// header\n\nfn f() {}\n\nfn g() = 1\n// tail\n",
    );
    check("fn f() {}fn g() {}", "fn f() {}\nfn g() {}\n");
    check(
        "\n\nfn f() {\n\n    a\n\n\n    b\n\n}\n\n",
        "fn f() {\n    a\n\n    b\n}\n",
    );
}

#[test]
fn lists_break_one_per_line_with_a_layout_comma() {
    check(
        "fn long(aaaaaaaaaaaaaaaa: int, bbbbbbbbbbbbbbbbbbbb: int, cccccccccccccccccccccc: int, dddddddddddddddddd: int) -> int = 1",
        "fn long(\n    aaaaaaaaaaaaaaaa: int,\n    bbbbbbbbbbbbbbbbbbbb: int,\n    cccccccccccccccccccccc: int,\n    dddddddddddddddddd: int,\n) -> int = 1\n",
    );
    check(
        "fn f() {\n    foo(a, b,)\n    foo(\n        a,\n        b,\n    )\n    foo(b , )\n}",
        "fn f() {\n    foo(a, b)\n    foo(a, b)\n    foo(b)\n}\n",
    );
    check(
        "fn f() {\n    let total = compute(aaaaaaaaaaaaaaaaaaaaaaaaa, bbbbbbbbbbbbbbbbbbbbbbbbbbbb, cccccccccccccccccccccccccccc, dddddddddddd)\n}",
        "fn f() {\n    let total = compute(\n        aaaaaaaaaaaaaaaaaaaaaaaaa,\n        bbbbbbbbbbbbbbbbbbbbbbbbbbbb,\n        cccccccccccccccccccccccccccc,\n        dddddddddddd,\n    )\n}\n",
    );
}

#[test]
fn chains_break_before_operators_and_values_move_after_eq() {
    // Ninety columns: past the width after `let x = `, within it one
    // level in.
    check(
        "fn f() {\n    let x = aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa + bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\n}",
        "fn f() {\n    let x =\n        aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa + bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\n}\n",
    );
    // Wider still: the chain breaks before each operator of its level.
    check(
        "fn f() {\n    let x = aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa + bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\n}",
        "fn f() {\n    let x =\n        aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n            + bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\n}\n",
    );
    check(
        "fn f() {\n    aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa + bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb * ccccccccccccccccccccc + ddddddddddddddd\n}",
        "fn f() {\n    aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n        + bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb * ccccccccccccccccccccc\n        + ddddddddddddddd\n}\n",
    );
}

#[test]
fn comments_stay_in_their_gaps_and_force_breaks() {
    check(
        "fn f() { a // why\n + b }",
        "fn f() {\n    a // why\n        + b\n}\n",
    );
    check(
        "fn f() {\n// lead\n  a   // trail\n   // own\n}",
        "fn f() {\n    // lead\n    a // trail\n    // own\n}\n",
    );
    check("fn f() { // inside\n}", "fn f() { // inside\n}\n");
    check(
        "fn f(a: int, // first\n b: int) {}",
        "fn f(\n    a: int, // first\n    b: int,\n) {}\n",
    );
}

#[test]
fn holes_never_break() {
    check(
        "fn g() { let s = \"x{ a + b }y{f( c )}\" }",
        "fn g() {\n    let s = \"x{a + b}y{f(c)}\"\n}\n",
    );
}

#[test]
fn closures_and_expression_bodies_keep_their_forms() {
    check(
        "fn f() = fn(x) = x * 2\nfn g() = fn(x: int) -> int {\n x\n}\nfn h() = {\n 1\n}",
        "fn f() = fn(x) = x * 2\nfn g() = fn(x: int) -> int {\n    x\n}\nfn h() = {\n    1\n}\n",
    );
    check(
        "fn f() {\n    let x = if c {\n a\n } else { b }\n}",
        "fn f() {\n    let x = if c {\n        a\n    } else {\n        b\n    }\n}\n",
    );
}

#[test]
fn empty_and_trivia_only_sources() {
    check("", "");
    check("  \n\n", "");
    check("  // only\n\n", "// only\n");
    check("// a\n\n\n// b", "// a\n\n// b\n");
}

#[test]
fn recovered_syntax_is_left_as_written_around_the_damage() {
    // The chained comparison is an `Error` node: frozen. The unclosed
    // paren anchors a recovery at the gap where `)` is missing: frozen.
    // Everything else, the sound item included, is formatted.
    check(
        "fn f() {\n    let x = a < b < c\n    let y = (\n}\nfn g() { ok(1) }",
        "fn f() {\n    let x = a < b < c\n    let y = (\n}\nfn g() {\n    ok(1)\n}\n",
    );
    // A frozen final gap keeps even the missing trailing newline.
    check("fn f( { ) }", "fn f( { ) }");
    check("fn 0() fn", "fn 0() fn");
    check(
        "fn f() { a==b }\n\u{20ac} ; [",
        "fn f() {\n    a == b\n}\n\u{20ac} ; [",
    );
}

#[test]
fn formatting_keeps_the_rep_and_only_changes_trivia() {
    for source in [
        "fn f(a:int,b:int)->int{let x=a+b\nreturn x*2}",
        "fn f() { a // why\n + b }\nfn g() { let s = \"x{ a + b }y\" }",
        "fn f() { a==b }\n\u{20ac} ; [",
        "fn f() {\n    let x = a < b < c\n    let y = (\n}\nfn g() { ok(1) }",
        "fn f(a, b,) {}",
        "\"open",
        "fn f() { ((((( }",
    ] {
        let lexed = lex(source).unwrap();
        let input = ParserInput::new(&lexed);
        let parsed = parse(&input);
        let before = rep(source, &lexed, &input, parsed.tree());
        let formatted = format(source, &lexed, &parsed).expect("no defect");
        let after_lexed = lex(&formatted.text).unwrap();
        let after_input = ParserInput::new(&after_lexed);
        let after = parse(&after_input);
        assert_eq!(
            rep(&formatted.text, &after_lexed, &after_input, after.tree()),
            before,
            "rep of {source:?} -> {:?}",
            formatted.text
        );
    }
}

#[test]
fn a_value_hugs_its_binding_line_when_its_head_fits() {
    // The call's head `let total = compute(` fits, so the arguments break
    // inside it; the whole moves to the next line only when even the head
    // does not fit, and then its inside is one level deeper.
    check(
        "fn f() {\n    let total = compute(aaaaaaaaaaaaaaaaaaaaaaaaa, bbbbbbbbbbbbbbbbbbbbbbbbbbbb, cccccccccccccccccccccccccccc, dddddddddddd)\n}",
        "fn f() {\n    let total = compute(\n        aaaaaaaaaaaaaaaaaaaaaaaaa,\n        bbbbbbbbbbbbbbbbbbbbbbbbbbbb,\n        cccccccccccccccccccccccccccc,\n        dddddddddddd,\n    )\n}\n",
    );
    check(
        "fn f() {\n    let a_rather_long_binding_name_for_the_result = a_callee_whose_name_is_longer_than_the_line_allows(aaaaaaaaaaaaaaaaaaaaa, bbbbbbbbbbbbbbb)\n}",
        "fn f() {\n    let a_rather_long_binding_name_for_the_result =\n        a_callee_whose_name_is_longer_than_the_line_allows(aaaaaaaaaaaaaaaaaaaaa, bbbbbbbbbbbbbbb)\n}\n",
    );
    check(
        "fn f() {\n    let a_rather_long_binding_name_for_the_result = a_callee_whose_name_is_longer_than_the_line_allows(aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, bbbbbbbbbbbbbbbbbbbbbbbbb)\n}",
        "fn f() {\n    let a_rather_long_binding_name_for_the_result =\n        a_callee_whose_name_is_longer_than_the_line_allows(\n            aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,\n            bbbbbbbbbbbbbbbbbbbbbbbbb,\n        )\n}\n",
    );
    check(
        "fn f() {\n    let x = aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n}",
        "fn f() {\n    let x =\n        aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n}\n",
    );
    check(
        "fn compute() -> int = combine(aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb, ccccccccccccc)",
        "fn compute() -> int = combine(\n    aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,\n    bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb,\n    ccccccccccccc,\n)\n",
    );
}

#[test]
fn a_block_bodied_closure_hugs_the_list_it_ends() {
    check(
        "fn f() {\n    each(items, fn(item) {\n        visit(item)\n    })\n}",
        "fn f() {\n    each(items, fn(item) {\n        visit(item)\n    })\n}\n",
    );
    // When the head does not fit, the list breaks and the closure moves
    // one level in with the other elements.
    check(
        "fn f() {\n    each(aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb, fn(item) {\n        visit(item)\n    })\n}",
        "fn f() {\n    each(\n        aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,\n        bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb,\n        fn(item) {\n            visit(item)\n        },\n    )\n}\n",
    );
    // A comment before the closure forces the list; one inside it does not.
    check(
        "fn f() {\n    each(items, // all\n fn(item) {\n        visit(item) // one\n    })\n}",
        "fn f() {\n    each(\n        items, // all\n        fn(item) {\n            visit(item) // one\n        },\n    )\n}\n",
    );
}
