//! Property tests: the partition invariants of `lex`, over generated sources
//! instead of the hand-written cases in `lex.rs`.

use proptest::prelude::*;
use sumi_lexer::{SyntaxKind, lex};
use sumi_test::check;

/// Fragments beyond every keyword and punctuation text of the language that
/// each lex to exactly one token on their own, stay terminated, and do not
/// absorb a following space-separated fragment. [`spaced_tokens_roundtrip`]
/// depends on all three; keep new entries within them.
const EXTRA_SINGLE_TOKENS: &[&str] = &[
    // Identifiers.
    "x",
    "foo",
    "_a",
    "r",
    "raw",
    // Numbers, valid and pathological: suffixes and padding.
    "0",
    "123",
    "1_000",
    "1e5",
    "0123",
    "1u32",
    "0x1F",
    // Terminated string literals.
    "\"abc\"",
    "\"a\\\"b\"",
    // Punctuation outside the language.
    ";",
    "[",
    "]",
    "@",
    "#",
    "\\",
    // A character with no token to belong to.
    "€",
];

/// Every keyword and punctuation text of the language, then
/// [`EXTRA_SINGLE_TOKENS`].
fn single_tokens() -> Vec<&'static str> {
    SyntaxKind::ALL
        .iter()
        .filter_map(|kind| kind.text())
        .chain(EXTRA_SINGLE_TOKENS.iter().copied())
        .collect()
}

/// Fragments that are only safe in free concatenation: trivia, comments,
/// strings terminated and not, escapes known and unknown, and characters
/// with no meaning.
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

/// Concatenated fragments: the boundaries between them are what exercises
/// maximal munch.
fn soup() -> impl Strategy<Value = String> {
    proptest::collection::vec(fragment(), 0..64).prop_map(|fragments| fragments.concat())
}

/// Number-shaped sources: digits, the separator, the point, an exponent,
/// a sign, a suffix, and a hex digit, concatenated in every order, so the
/// pathological literals the malformed flag is held to are sampled densely
/// rather than by chance in [`soup`].
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
