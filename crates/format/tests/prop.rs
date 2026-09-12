//! Formatting properties over generated token soup and well-formed programs.

use proptest::prelude::*;
use proptest::test_runner::FileFailurePersistence;
use sumi_format::{format, rep};
use sumi_lexer::{LexedFile, lex};
use sumi_syntax::{Parse, ParserInput, SyntaxKind, parse};

/// Source fragments beyond every keyword and punctuation text of the
/// language, valid and pathological, echoing the parser soup property;
/// concatenation composes the adjacencies goldens cannot enumerate.
const EXTRA_FRAGMENTS: &[&str] = &[
    "x", "foo", "x = y", "0", "123", "1.5", "1e", "0123", "1u32", "\"abc\"", "\"open", ";", "[",
    " ", "\t", "\n", "\r\n", "\r", "// c", "€", "\"{", "}\"", "\"{x}\"",
];

/// Token soup, half the time wrapped in a function body: violations are
/// recorded while parsing expressions, which live in blocks.
fn soup() -> impl Strategy<Value = String> {
    let fragments: Vec<&'static str> = SyntaxKind::ALL
        .iter()
        .filter_map(|kind| kind.text())
        .chain(EXTRA_FRAGMENTS.iter().copied())
        .collect();
    let fragments = proptest::collection::vec(prop::sample::select(fragments), 0..48)
        .prop_map(|fragments| fragments.concat());
    prop_oneof![
        1 => fragments.clone(),
        1 => fragments.prop_map(|soup| format!("fn f() {{ {soup} }}")),
    ]
}

struct Front {
    lexed: LexedFile,
    parse: Parse,
}

fn front(source: &str) -> Front {
    let lexed = lex(source).expect("generated sources fit in u32");
    let parse = parse(&ParserInput::new(&lexed));
    Front { lexed, parse }
}

/// Records every failing seed in the crate's tracked `proptest-regressions/`
/// file, which each later run replays before generating anything new, so a
/// failure found once stays found. Proptest's default location is found by
/// walking up from the test file to a `lib.rs`, which a test under `tests/`
/// never reaches; this path is fixed at compile time instead.
fn config() -> ProptestConfig {
    ProptestConfig {
        failure_persistence: Some(Box::new(FileFailurePersistence::Direct(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/proptest-regressions/prop.txt"
        )))),
        ..ProptestConfig::default()
    }
}

/// The layout-free content of `source`: what formatting must keep.
fn layout_free<'s>(source: &'s str, front: &Front) -> sumi_format::Rep<'s> {
    let input = ParserInput::new(&front.lexed);
    rep(source, &front.lexed, &input, front.parse.tree())
}

/// Format `source` and assert the contract: the rep is kept, the edits are
/// the text, and formatting the result changes nothing.
fn check_format(source: &str) -> sumi_format::Formatted {
    let before = front(source);
    let formatted = format(source, &before.lexed, &before.parse)
        .unwrap_or_else(|defect| panic!("defect on {source:?}: {}", defect.rejected));
    let after = front(&formatted.text);
    assert_eq!(
        layout_free(&formatted.text, &after),
        layout_free(source, &before),
        "format changed the rep of {source:?} -> {:?}",
        formatted.text
    );
    assert_eq!(
        sumi_text::apply(source, &formatted.edits),
        formatted.text,
        "the edits of {source:?} are not its text"
    );
    let again = format(&formatted.text, &after.lexed, &after.parse)
        .unwrap_or_else(|defect| panic!("defect on {:?}: {}", formatted.text, defect.rejected));
    assert_eq!(
        again.text, formatted.text,
        "format of {source:?} is not idempotent"
    );
    formatted
}

proptest! {
    #![proptest_config(config())]
    #[test]
    fn format_keeps_the_rep_and_settles(source in soup()) {
        check_format(&source);
    }

    #[test]
    fn well_formed_programs_format_without_reverting(source in sumi_test::program()) {
        let formatted = check_format(&source);
        prop_assert_eq!(formatted.reverted, 0, "reverted items in {:?}", source);
        let after = front(&formatted.text);
        prop_assert!(
            after.parse.evidence().is_empty(),
            "formatted {:?} -> {:?} has evidence {:?}",
            source,
            formatted.text,
            after.parse.evidence()
        );
    }
}
