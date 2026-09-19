use proptest::prelude::*;
use sumi_lexer::{SyntaxKind, lex};
use sumi_test::check;

/// Each entry lexes to one token on its own and absorbs no following space-separated fragment;
/// [`spaced_tokens_roundtrip`] relies on both.
const EXTRA_SINGLE_TOKENS: &[&str] = &[
    "x",
    "foo",
    "_a",
    "r",
    "raw",
    "0",
    "123",
    "1_000",
    "1e5",
    "0123",
    "1u32",
    "0x1F",
    "\"abc\"",
    "\"a\\\"b\"",
    ";",
    "[",
    "]",
    "@",
    "#",
    "\\",
    "€",
];

fn single_tokens() -> Vec<&'static str> {
    SyntaxKind::ALL
        .iter()
        .filter_map(|kind| kind.text())
        .chain(EXTRA_SINGLE_TOKENS.iter().copied())
        .collect()
}

const LOOSE_FRAGMENTS: &[&str] = &[
    " ",
    "\t",
    "\n",
    "\r\n",
    "\r",
    "// c",
    "//",
    "\"a b\"",
    "\"open",
    "\"a\\nb\"",
    "\"\\q\"",
    "\\",
    "'",
    "\u{1}",
];

fn fragment() -> impl Strategy<Value = String> {
    prop_oneof![
        6 => prop::sample::select(single_tokens()).prop_map(str::to_owned),
        3 => prop::sample::select(LOOSE_FRAGMENTS).prop_map(str::to_owned),
        1 => proptest::collection::vec(any::<char>(), 0..4)
            .prop_map(|chars| chars.into_iter().collect::<String>()),
    ]
}

fn soup() -> impl Strategy<Value = String> {
    proptest::collection::vec(fragment(), 0..64).prop_map(|fragments| fragments.concat())
}

/// Malformed number literals arise in [`soup`] only by chance; here they are dense.
fn number_soup() -> impl Strategy<Value = String> {
    const PIECES: &[&str] = &[
        "0", "1", "9", "123", "_", ".", "e", "-", "5", "u32", "x", " ",
    ];
    proptest::collection::vec(prop::sample::select(PIECES).prop_map(str::to_owned), 1..12)
        .prop_map(|pieces| pieces.concat())
}

proptest! {
    #![proptest_config(sumi_test::regressions!("prop.txt"))]
    #[test]
    fn lex_is_total_and_partitions(source in prop_oneof![soup(), number_soup()]) {
        check::lexed(&source, &lex(&source).expect("generated sources fit in u32"));
    }

    #[test]
    fn spaced_tokens_roundtrip(
        fragments in proptest::collection::vec(
            prop::sample::select(single_tokens()).prop_map(str::to_owned),
            0..32,
        ),
    ) {
        let source = fragments.join(" ");
        let file = lex(&source).expect("generated sources fit in u32");

        let tokens: Vec<&str> = file.indices()
            .filter(|&index| file.kind(index) != SyntaxKind::Whitespace)
            .map(|index| file.text(&source, index))
            .collect();
        let expected: Vec<&str> = fragments.iter().map(String::as_str).collect();
        prop_assert_eq!(tokens, expected);
    }
}
