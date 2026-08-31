//! Property tests: the partition invariants of `lex`, over generated sources
//! instead of the hand-written corpus in `lex.rs`.

use proptest::prelude::*;
use sumi_lexer::{RawKind, SyntaxKind, TokenFlags, lex};

/// Fragments that each lex to exactly one token on their own, stay
/// terminated, and do not absorb a following space-separated fragment.
/// [`spaced_tokens_roundtrip`] depends on all three; keep new entries within
/// them.
const SINGLE_TOKENS: &[&str] = &[
    // Keywords and identifiers.
    "fn",
    "let",
    "if",
    "else",
    "return",
    "true",
    "false",
    "mut",
    "x",
    "foo",
    "_",
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
    "\"a\nb\"",
    "'a'",
    "'\\''",
    "'ab'",
    "''",
    "r\"a\"",
    "r#\"q\"#",
    // Punctuation, in and out of the language.
    "(",
    ")",
    "{",
    "}",
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
    ";",
    "[",
    "]",
    "@",
    "#",
    "\\",
    // A character with no token to belong to.
    "€",
];

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
    "\u{feff}",
    "\u{1}",
];

fn fragment() -> impl Strategy<Value = String> {
    prop_oneof![
        6 => prop::sample::select(SINGLE_TOKENS).prop_map(str::to_owned),
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

proptest! {
    #[test]
    fn lex_is_total_and_partitions(source in soup()) {
        let file = lex(&source).expect("generated sources fit in u32");
        prop_assert_eq!(file.source_len().to_usize(), source.len());

        let mut concatenated = String::new();
        for index in 0..file.len() {
            let range = file.range(index);
            prop_assert!(range.start() < range.end(), "token {} is empty", index);
            prop_assert!(source.is_char_boundary(range.start().to_usize()));
            prop_assert!(source.is_char_boundary(range.end().to_usize()));
            if index == 0 {
                prop_assert_eq!(range.start().to_u32(), 0, "first token must start at 0");
            } else {
                prop_assert_eq!(
                    range.start(),
                    file.range(index - 1).end(),
                    "token {} is not contiguous", index
                );
            }
            concatenated.push_str(file.text(&source, index));
        }
        prop_assert_eq!(&concatenated, &source, "tokens must reproduce the source");

        if let Some(last) = file.len().checked_sub(1) {
            prop_assert_eq!(file.range(last).end(), file.source_len());
        }
        for error in file.errors() {
            prop_assert!((error.token as usize) < file.len());
            let token = file.range(error.token as usize);
            prop_assert!(token.start() <= error.range.start());
            prop_assert!(error.range.end() <= token.end());
            prop_assert!(source.is_char_boundary(error.range.start().to_usize()));
            prop_assert!(source.is_char_boundary(error.range.end().to_usize()));
        }

        for index in 0..file.len() {
            if file.kind(index) == SyntaxKind::Error {
                prop_assert!(
                    file.errors().iter().any(|error| error.token == index as u32),
                    "error token {} has no lexical error", index
                );
            }
        }
    }

    #[test]
    fn the_number_scan_and_validation_agree(source in number_soup()) {
        let file = lex(&source).expect("generated sources fit in u32");
        for index in 0..file.len() {
            if file.raw_kind(index) != RawKind::Number {
                continue;
            }
            let flagged = file.flags(index).contains(TokenFlags::MALFORMED_NUMBER);
            let has_error = file.errors().iter().any(|error| error.token == index as u32);
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
            prop::sample::select(SINGLE_TOKENS).prop_map(str::to_owned),
            0..32,
        ),
    ) {
        let source = fragments.join(" ");
        let file = lex(&source).expect("generated sources fit in u32");

        let tokens: Vec<&str> = (0..file.len())
            .filter(|&index| file.raw_kind(index) != RawKind::HorizontalSpace)
            .map(|index| file.text(&source, index))
            .collect();
        let expected: Vec<&str> = fragments.iter().map(String::as_str).collect();
        prop_assert_eq!(tokens, expected);
    }
}
