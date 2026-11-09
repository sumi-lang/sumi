//! The syntax layer's invariants from `sumi_test::check`, sampled over generated sources.

use proptest::prelude::*;
use sumi_lexer::lex;
use sumi_syntax::{ParserInput, SigIdx, SyntaxKind, parse};
use sumi_test::{
    Edit, check, delimiter_edited_program, front, non_delimiter_edited_program, program,
};

const EXTRA_FRAGMENTS: &[&str] = &[
    "x", "foo", "0", "123", "1_000", "1.5", "1e", "0123", "1u32", "0x1F", ";", "[", " ", "\t",
    "\n", "\r\n", "\r", "// c", "/// d", "€",
];

fn fragments() -> Vec<&'static str> {
    SyntaxKind::ALL
        .iter()
        .filter_map(|kind| kind.text())
        .chain(EXTRA_FRAGMENTS.iter().copied())
        .collect()
}

/// No `)`, `}`, `{`, or unmatched `(`: each would close or unbalance the wrapping paren in
/// [`newlines_inside_parens_never_terminate`], or restore termination.
const PAREN_SAFE: &[&str] = &[
    "fn", "let", "if", "else", "return", "true", "x", "foo", "0", "1.5", "1e", "(x)", "(\nx\n)",
    ",", ":", ".", "=", "<", ">", "!", "+", "-", "*", "/", "%", "&", "|", " ", "\t", "\n", "\r\n",
    "// c\n",
];

fn fragment() -> impl Strategy<Value = String> {
    prop_oneof![
        9 => prop::sample::select(fragments()).prop_map(str::to_owned),
        1 => proptest::collection::vec(any::<char>(), 0..4)
            .prop_map(|chars| chars.into_iter().collect::<String>()),
    ]
}

fn soup() -> impl Strategy<Value = String> {
    proptest::collection::vec(fragment(), 0..64).prop_map(|fragments| fragments.concat())
}

proptest! {
    #![proptest_config(sumi_test::regressions!("prop.txt"))]
    #[test]
    fn arbitrary_source_invariants(source in soup()) {
        let lexed = lex(&source).expect("generated sources fit in u32");
        let input = ParserInput::new(&lexed);
        check::input(&lexed, &input);
        check::widening(&source, &lexed, &input);
        check::parse(&source, &lexed, &parse(input));
    }

    #[test]
    fn newlines_inside_parens_never_terminate(
        pieces in proptest::collection::vec(
            prop::sample::select(PAREN_SAFE).prop_map(str::to_owned),
            0..32,
        ),
    ) {
        let source = format!("f({})", pieces.concat());
        let lexed = lex(&source).expect("generated sources fit in u32");
        let input = ParserInput::new(&lexed);
        // Two `/` pieces make a `//` that comments out the closer, and an unclosed `(` suspends
        // nothing.
        prop_assume!(input.partner(SigIdx::new(1)) == Some(input.end() - 1));
        for index in input.indices() {
            prop_assert!(
                !input.has_boundary_before(index),
                "boundary before token {:?} in {:?}", index, source
            );
        }
    }

    #[test]
    fn well_formed_programs_produce_no_parse_evidence(source in program()) {
        let lexed = lex(&source).expect("generated sources fit in u32");
        prop_assert!(lexed.errors().is_empty(), "lexer errors in {:?}", source);
        let parse = parse(ParserInput::new(&lexed));
        check::parse(&source, &lexed, &parse);
        prop_assert!(
            parse.evidence().is_empty(),
            "parse evidence {:?} in {:?}", parse.evidence(), source
        );
    }

    #[test]
    fn a_single_non_delimiter_edit_disturbs_only_where_it_lands(
        (source, index, edit) in non_delimiter_edited_program()
    ) {
        check::recovery(&source, &front(&source), index, edit);
    }

    #[test]
    fn a_single_delimiter_edit_preserves_unaffected_items(
        (source, index, edit) in delimiter_edited_program()
    ) {
        check::recovery(&source, &front(&source), index, edit);
    }
}

#[test]
fn a_duplicated_if_may_take_the_next_lines_block() {
    let source = "fn o() {\n    (e) = if {} {}\n    {} && a / {}\n}\n";
    check::recovery(source, &front(source), 9, Edit::Duplicate);
}

#[test]
fn an_equals_before_a_union_member_keeps_the_body() {
    let source = "fn foo(b: P | Q) -> P | Q | int { foo }\n";
    for member in [13, 15] {
        check::recovery(source, &front(source), member, Edit::Insert("="));
    }
}

#[test]
fn a_duplicated_arrow_keeps_the_body_after_a_multiline_return_type() {
    for source in [
        "fn f()->\ni{{k}}",
        "fn f() ->\n i {\n    { k() }\ntue(x)=x\n   \n6}\n",
    ] {
        check::recovery(source, &front(source), 5, Edit::Duplicate);
    }
}

#[test]
fn a_range_without_its_operator_leaves_the_block_to_the_body() {
    let source = "fn f() {\n    _ = 0\n      / for x in a..b {}\n      <= c\n    {}\n      % d\n    e = f\n}\n";
    check::recovery(source, &front(source), 13, Edit::Delete);
}

#[test]
fn a_failed_statement_leaves_its_blocks_closer_before_an_equals() {
    let source = "fn f() {\n    _ = match a {\n        _ => {\n            if a { b } = 1\n        }\n    }\n    { c }\n}\n";
    check::recovery(source, &front(source), 17, Edit::Insert(","));
}

#[test]
fn a_match_without_its_scrutinee_keeps_its_arms() {
    let source = "fn f() {\n    _ = match a { P => b }\n      || c\n    { d }\n}\n";
    check::recovery(source, &front(source), 8, Edit::Delete);
}
