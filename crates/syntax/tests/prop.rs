//! The syntax layer's invariants from `sumi_test::check`, sampled over generated sources.

use proptest::prelude::*;
use sumi_lexer::lex;
use sumi_syntax::{ParserInput, SigIdx, SyntaxKind, parse};
use sumi_test::{
    Edit, INSERTS, check, delimiter_edited_program, front, non_delimiter_edited_program, program,
};

const EXTRA_FRAGMENTS: &[&str] = &[
    "x",
    "foo",
    "0",
    "123",
    "1_000",
    "1.5",
    "1e",
    "0123",
    "1u32",
    "0x1F",
    "\"abc\"",
    "\"a\\nb\"",
    "\"a\nb\"",
    "\"open",
    ";",
    "[",
    " ",
    "\t",
    "\n",
    "\r\n",
    "\r",
    "// c",
    "/// d",
    "€",
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
    "fn",
    "let",
    "if",
    "else",
    "return",
    "true",
    "x",
    "foo",
    "0",
    "1.5",
    "1e",
    "\"s\"",
    "(x)",
    "(\nx\n)",
    ",",
    ":",
    ".",
    "=",
    "<",
    ">",
    "!",
    "+",
    "-",
    "*",
    "/",
    "%",
    "&",
    "|",
    " ",
    "\t",
    "\n",
    "\r\n",
    "// c\n",
    "\"a {x} b\"",
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
                !input.boundary_before(index),
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

/// The program generator produces no exposed closures, so these are enumerated by hand.
#[test]
fn every_edit_around_an_exposed_closure_recovers_locally() {
    let edits = [Edit::Delete, Edit::Duplicate, Edit::Swap]
        .into_iter()
        .chain(INSERTS.iter().map(|&text| Edit::Insert(text)));
    for source in [
        "fn first() = 0\nfn outer() = fn() = fn(x) = x\nfn next() = 2\n",
        "fn first() = 0\nfn outer() =\n fn(x: int) { x }\nfn next() = 2\n",
        "fn first()\n= 0\nfn outer()\n= fn(x: int)\n-> int\n= x +\n1\nfn next()\n-> int\n= 2\n",
        "fn first()\n{}\nfn outer()\n{ if { true }\n{}\nelse\n{} }\nfn next()\n{}\n",
    ] {
        let original = front(source);
        for index in 0..original.input().len() {
            for edit in edits.clone() {
                check::recovery(source, &original, index, edit);
            }
        }
    }
}
