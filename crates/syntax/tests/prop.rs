//! Property tests: cook and ParserInput invariants over generated sources
//! instead of the hand-written corpus in `cook.rs` and `input.rs`.

use jolt_lexer::{RawKind, lex};
use jolt_syntax::{ParserInput, SyntaxKind, cook};
use proptest::prelude::*;

/// Source fragments, valid and pathological; concatenation composes the
/// adjacencies goldens cannot enumerate.
const FRAGMENTS: &[&str] = &[
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
    "Δx",
    "0",
    "123",
    "1_000",
    "1.5",
    "2.5e-3",
    "1e",
    "1e+05",
    "0123",
    "1u32",
    "0x1F",
    "\"abc\"",
    "\"a\\nb\"",
    "\"a\nb\"",
    "\"open",
    "'a'",
    "'ab'",
    "r\"a\"",
    "r##\"a\"#",
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
    " ",
    "\t",
    "\n",
    "\r\n",
    "\r",
    "// c",
    "/// d",
    "\u{feff}",
    "€",
];

/// Fragments free of `)` and `}` (each would close the wrapping paren) and
/// of `{` (it would restore termination), for
/// [`newlines_inside_parens_never_terminate`].
const PAREN_SAFE: &[&str] = &[
    "fn", "let", "if", "else", "return", "true", "x", "foo", "0", "1.5", "2.5e-3", "1e", "\"s\"",
    "'a'", "r\"a\"", "(", ",", ":", ".", "=", "<", ">", "!", "+", "-", "*", "/", "%", "&", "|",
    " ", "\t", "\n", "\r\n", "// c",
];

fn fragment() -> impl Strategy<Value = String> {
    prop_oneof![
        9 => prop::sample::select(FRAGMENTS).prop_map(str::to_owned),
        1 => proptest::collection::vec(any::<char>(), 0..4)
            .prop_map(|chars| chars.into_iter().collect::<String>()),
    ]
}

fn soup() -> impl Strategy<Value = String> {
    proptest::collection::vec(fragment(), 0..64).prop_map(|fragments| fragments.concat())
}

fn is_trivia(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::Whitespace | SyntaxKind::Newline | SyntaxKind::LineComment
    )
}

proptest! {
    #[test]
    fn cook_is_total_and_one_to_one(source in soup()) {
        let lexed = lex(&source).expect("generated sources fit in u32");
        let cooked = cook(&source, &lexed);
        prop_assert_eq!(cooked.len(), lexed.len(), "cooking must stay 1:1");

        for error in cooked.errors() {
            prop_assert!((error.token as usize) < cooked.len());
            // Diagnostic ownership does not overlap: a token the lexer
            // reported gets no further errors from the cook.
            prop_assert!(
                !lexed.errors().iter().any(|lex_error| lex_error.token == error.token),
                "token {} has both a lex and a cook error", error.token
            );
        }
    }

    #[test]
    fn parser_input_invariants(source in soup()) {
        let lexed = lex(&source).expect("generated sources fit in u32");
        let cooked = cook(&source, &lexed);
        let input = ParserInput::new(&cooked);

        prop_assert!(input.len() <= cooked.len());
        prop_assert_eq!(input.get(input.len()), None);

        let mut previous: Option<usize> = None;
        for index in 0..input.len() {
            let token = input.token(index) as usize;
            let kind = input.get(index).expect("indices below len are present");
            if let Some(previous) = previous {
                prop_assert!(previous < token, "token mappings must strictly increase");
            }
            prop_assert_eq!(kind, cooked.kind(token), "kinds must come from the cook");
            prop_assert!(!is_trivia(kind), "token {} is trivia", index);

            // Everything skipped between kept tokens must be trivia, and the
            // newline fact must match what was skipped.
            let skipped = previous.map_or(0, |previous| previous + 1)..token;
            let newline = skipped.clone().any(|j| cooked.kind(j) == SyntaxKind::Newline);
            for j in skipped {
                prop_assert!(is_trivia(cooked.kind(j)), "token {} was dropped", j);
            }
            prop_assert_eq!(input.newline_before(index), newline);

            // Jointness is adjacency, checked through ranges rather than
            // token indices.
            if index + 1 < input.len() {
                let next = input.token(index + 1) as usize;
                let adjacent = lexed.range(token).end() == lexed.range(next).start();
                prop_assert_eq!(input.is_joint(index), adjacent);
            } else {
                prop_assert!(!input.is_joint(index));
            }

            if input.boundary_before(index) {
                prop_assert!(index > 0, "no boundary before the first token");
                prop_assert!(input.newline_before(index), "boundaries need a newline");
            }
            previous = Some(token);
        }

        // Nothing significant may be dropped after the last kept token.
        for j in previous.map_or(0, |previous| previous + 1)..cooked.len() {
            prop_assert!(is_trivia(cooked.kind(j)), "token {} was dropped", j);
        }
    }

    #[test]
    fn widening_space_runs_changes_nothing(source in soup()) {
        let lexed = lex(&source).expect("generated sources fit in u32");
        let mut widened = String::new();
        for index in 0..lexed.len() {
            widened.push_str(lexed.text(&source, index));
            if lexed.kind(index) == RawKind::HorizontalSpace {
                widened.push(' ');
            }
        }

        // Widening an existing space run merges back into the same token, so
        // everything but the ranges is untouched: kinds, jointness, newline
        // facts, and boundaries.
        let widened_lexed = lex(&widened).expect("widened sources fit in u32");
        prop_assert_eq!(widened_lexed.len(), lexed.len());

        let cooked = cook(&source, &lexed);
        let widened_cooked = cook(&widened, &widened_lexed);
        for index in 0..cooked.len() {
            prop_assert_eq!(cooked.kind(index), widened_cooked.kind(index));
        }

        let input = ParserInput::new(&cooked);
        let widened_input = ParserInput::new(&widened_cooked);
        prop_assert_eq!(input.len(), widened_input.len());
        for index in 0..input.len() {
            prop_assert_eq!(input.token(index), widened_input.token(index));
            prop_assert_eq!(input.is_joint(index), widened_input.is_joint(index));
            prop_assert_eq!(input.newline_before(index), widened_input.newline_before(index));
            prop_assert_eq!(input.boundary_before(index), widened_input.boundary_before(index));
        }
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
        let input = ParserInput::new(&cook(&source, &lexed));
        for index in 0..input.len() {
            prop_assert!(
                !input.boundary_before(index),
                "boundary before token {} in {:?}", index, source
            );
        }
    }
}
