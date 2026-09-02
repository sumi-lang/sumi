//! Property tests: the partition invariants of `lex`, over generated sources
//! instead of the hand-written corpus in `lex.rs`.

use proptest::prelude::*;
use proptest::test_runner::FileFailurePersistence;
use sumi_lexer::{RawIdx, RawKind, SyntaxKind, TokenFlags, lex};

/// Fragments beyond every keyword and punctuation text of the language that
/// each lex to exactly one token on their own, stay terminated, and do not
/// absorb a following space-separated fragment. [`spaced_tokens_roundtrip`]
/// depends on all three; keep new entries within them.
const EXTRA_SINGLE_TOKENS: &[&str] = &[
    // Identifiers.
    "x",
    "foo",
    "_a",
    "Δx",
    "μ2",
    "r",
    "raw",
    // Numbers, valid and pathological: suffixes, broken exponents, padding.
    "0",
    "123",
    "1_000",
    "1.5",
    "2.5e-3",
    "1e5",
    "1E-5",
    "1e",
    "1e+05",
    "0123",
    "1__0",
    "0_",
    "1u32",
    "0x1F",
    // Terminated string, char, and raw-string literals.
    "\"abc\"",
    "\"a\\\"b\"",
    "'a'",
    "'\\''",
    "'ab'",
    "''",
    "r\"a\"",
    "r#\"q\"#",
    // Terminated multi-line literals.
    "\"\"\"\n\"\"\"",
    "\"\"\"\n  a \\\"\n  \"\"\"",
    "r\"\"\"\n  \\d\n  \"\"\"",
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
/// unterminated literals, and a misplaced byte-order mark.
const LOOSE_FRAGMENTS: &[&str] = &[
    " ",
    "\t",
    "\n",
    "\r\n",
    "\r",
    "// c",
    "/// d",
    "//! e",
    "//",
    "\"open",
    "'x",
    "r##\"a\"#",
    "\"\"\"\n",
    "r\"\"\"",
    "\u{feff}",
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

fn number_soup() -> impl Strategy<Value = String> {
    const PIECES: &[&str] = &[
        "0", "1", "9", "123", "_", "__", ".", "..", "e", "E", "+", "-", "5", "u32", "f", "x", " ",
    ];
    proptest::collection::vec(prop::sample::select(PIECES).prop_map(str::to_owned), 1..12)
        .prop_map(|fragments| fragments.concat())
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

proptest! {
    #![proptest_config(config())]
    #[test]
    fn lex_is_total_and_partitions(source in soup()) {
        let file = lex(&source).expect("generated sources fit in u32");
        prop_assert_eq!(file.source_len().to_usize(), source.len());

        let mut concatenated = String::new();
        for index in file.indices() {
            let range = file.range(index);
            prop_assert!(range.start() < range.end(), "token {:?} is empty", index);
            prop_assert!(source.is_char_boundary(range.start().to_usize()));
            prop_assert!(source.is_char_boundary(range.end().to_usize()));
            if index == RawIdx::new(0) {
                prop_assert_eq!(range.start().to_u32(), 0, "first token must start at 0");
            } else {
                prop_assert_eq!(
                    range.start(),
                    file.range(index - 1).end(),
                    "token {:?} is not contiguous", index
                );
            }
            concatenated.push_str(file.text(&source, index));
        }
        prop_assert_eq!(&concatenated, &source, "tokens must reproduce the source");

        if let Some(last) = file.end().checked_sub(1) {
            prop_assert_eq!(file.range(last).end(), file.source_len());
        }
        for error in file.errors() {
            prop_assert!(error.token < file.end());
            let token = file.range(error.token);
            prop_assert!(token.start() <= error.range.start());
            prop_assert!(error.range.end() <= token.end());
            prop_assert!(source.is_char_boundary(error.range.start().to_usize()));
            prop_assert!(source.is_char_boundary(error.range.end().to_usize()));
        }

        for index in file.indices() {
            if file.kind(index) == SyntaxKind::Error {
                prop_assert!(
                    file.errors().iter().any(|error| error.token == index),
                    "error token {:?} has no lexical error", index
                );
            }
            // Only a line break and a multi-line literal span lines.
            if file.text(&source, index).contains(['\n', '\r']) {
                prop_assert!(
                    matches!(
                        file.raw_kind(index),
                        RawKind::Newline | RawKind::BlockString | RawKind::RawBlockString
                    ),
                    "token {:?} crosses a line break", index
                );
            }
        }
    }

    #[test]
    fn the_number_scan_and_validation_agree(source in number_soup()) {
        let file = lex(&source).expect("generated sources fit in u32");
        for index in file.indices() {
            if file.raw_kind(index) != RawKind::Number {
                continue;
            }
            let flagged = file.flags(index).contains(TokenFlags::MALFORMED_NUMBER);
            let has_error = file.errors().iter().any(|error| error.token == index);
            prop_assert_eq!(
                flagged, has_error,
                "number {:?} flagged={} but has-error={}",
                file.text(&source, index), flagged, has_error
            );
        }
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
            .filter(|&index| file.raw_kind(index) != RawKind::HorizontalSpace)
            .map(|index| file.text(&source, index))
            .collect();
        let expected: Vec<&str> = fragments.iter().map(String::as_str).collect();
        prop_assert_eq!(tokens, expected);
    }
}
