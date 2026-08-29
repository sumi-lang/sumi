//! Property tests: cook and ParserInput invariants over generated sources
//! instead of the hand-written corpus in `cook.rs` and `input.rs`.

use proptest::prelude::*;
use sumi_lexer::{RawKind, lex};
use sumi_syntax::{NodeKind, ParserInput, SyntaxKind, SyntaxTree, cook, parse};

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
        let mut open: Vec<usize> = Vec::new();
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

            // Partners are mutual, of matching kinds, and nest: an opener
            // whose partner lies ahead is pushed, and a closer must close
            // the innermost open pair.
            if let Some(partner) = input.partner(index) {
                prop_assert!(partner < input.len());
                prop_assert_eq!(input.partner(partner), Some(index), "partners must be mutual");
                let (opener, closer) = if index < partner { (index, partner) } else { (partner, index) };
                prop_assert!(
                    matches!(
                        (input.get(opener), input.get(closer)),
                        (Some(SyntaxKind::LParen), Some(SyntaxKind::RParen))
                            | (Some(SyntaxKind::LBrace), Some(SyntaxKind::RBrace))
                    ),
                    "tokens {} and {} are partners but not a matching pair", opener, closer
                );
                if partner > index {
                    open.push(index);
                } else {
                    prop_assert_eq!(open.pop(), Some(partner), "pairs must nest");
                }
            }
            previous = Some(token);
        }
        prop_assert!(open.is_empty(), "every pushed opener must have been closed");

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

/// Walk `tree` and check every structural invariant: extents partition the
/// nodes; children are ordered, disjoint, and inside their parent; every
/// node but the root covers at least one token and starts and ends on a
/// significant one; the root covers the whole buffer.
fn check_tree(tree: &SyntaxTree, cooked: &sumi_syntax::CookedFile) -> Result<(), TestCaseError> {
    let raw_len = cooked.len() as u32;
    prop_assert_eq!(tree.kind(0), NodeKind::SourceFile);
    prop_assert_eq!((tree.first_token(0), tree.end_token(0)), (0, raw_len));

    let mut visited = 0usize;
    let mut pending = vec![0usize];
    while let Some(node) = pending.pop() {
        visited += 1;
        let (first, end) = (tree.first_token(node), tree.end_token(node));
        if node != 0 {
            prop_assert!(first < end, "node {} is empty", node);
            prop_assert!(
                !is_trivia(cooked.kind(first as usize)),
                "node {} starts on trivia",
                node
            );
            prop_assert!(
                !is_trivia(cooked.kind(end as usize - 1)),
                "node {} ends on trivia",
                node
            );
        }
        let mut previous_end = first;
        for child in tree.children(node) {
            prop_assert!(
                tree.first_token(child) >= previous_end,
                "children of {} overlap",
                node
            );
            prop_assert!(
                tree.end_token(child) <= end,
                "child {} escapes {}",
                child,
                node
            );
            previous_end = tree.end_token(child);
            pending.push(child);
        }
    }
    prop_assert_eq!(visited, tree.len(), "extents must partition the tree");
    Ok(())
}

proptest! {
    #[test]
    fn parse_is_total_and_trees_are_well_formed(source in soup()) {
        let lexed = lex(&source).expect("generated sources fit in u32");
        let cooked = cook(&source, &lexed);
        let input = ParserInput::new(&cooked);
        let parse = parse(&input);
        let tree = parse.tree();
        check_tree(tree, &cooked)?;

        // The parser attaches no token to the root itself: every significant
        // token lies in some item or top-level error node.
        let mut children = tree.children(0).peekable();
        for index in 0..input.len() {
            let token = input.token(index);
            while children.peek().is_some_and(|&child| tree.end_token(child) <= token) {
                children.next();
            }
            prop_assert!(
                children.peek().is_some_and(|&child| tree.first_token(child) <= token),
                "token {} is attached to the root", token
            );
        }

        // Errors sit in range, in source order, at most one per position,
        // and never on a token with no meaning, whose report the lexer or
        // cook owns. (A malformed literal keeps its kind and may carry both a
        // cook error and a structural one: independent problems.)
        let mut previous: Option<u32> = None;
        for error in parse.errors() {
            prop_assert!(error.token <= cooked.len() as u32);
            if let Some(previous) = previous {
                prop_assert!(previous < error.token, "errors must strictly advance");
            }
            if (error.token as usize) < cooked.len() {
                prop_assert_ne!(cooked.kind(error.token as usize), SyntaxKind::Error);
            }
            previous = Some(error.token);
        }
    }

    #[test]
    fn well_formed_programs_parse_without_errors(source in program()) {
        let lexed = lex(&source).expect("generated sources fit in u32");
        prop_assert!(lexed.errors().is_empty(), "lexer errors in {:?}", source);
        let cooked = cook(&source, &lexed);
        prop_assert!(cooked.errors().is_empty(), "cook errors in {:?}", source);
        let parse = parse(&ParserInput::new(&cooked));
        check_tree(parse.tree(), &cooked)?;
        prop_assert!(
            parse.errors().is_empty(),
            "parse errors {:?} in {:?}", parse.errors(), source
        );
    }
}

// A generator for well-formed programs: grammar-directed, with the spacing
// and line-break rules built in, so the parser must accept every output.

fn name() -> BoxedStrategy<String> {
    prop::sample::select(&["a", "b", "foo", "x1", "Δ"][..])
        .prop_map(str::to_owned)
        .boxed()
}

fn literal() -> BoxedStrategy<String> {
    prop::sample::select(
        &[
            "0", "42", "1_000", "1.5", "2.5e-3", "\"s\"", "'c'", "r\"a\"", "true", "false",
        ][..],
    )
    .prop_map(str::to_owned)
    .boxed()
}

/// A binary operator applied left to right over `operands`, spaced, with
/// each operator either on the line or leading the next one.
fn chain(
    operand: BoxedStrategy<String>,
    ops: &'static [&'static str],
    max: usize,
) -> BoxedStrategy<String> {
    (
        operand.clone(),
        prop::collection::vec((prop::sample::select(ops), any::<bool>(), operand), 0..max),
    )
        .prop_map(|(first, rest)| {
            let mut text = first;
            for (op, leading, operand) in rest {
                text.push_str(if leading { "\n  " } else { " " });
                text.push_str(op);
                text.push(' ');
                text.push_str(&operand);
            }
            text
        })
        .boxed()
}

fn expr() -> BoxedStrategy<String> {
    let leaf = prop_oneof![name(), literal()];
    leaf.prop_recursive(3, 24, 3, |expr| {
        let atom = prop_oneof![
            4 => name(),
            4 => literal(),
            1 => expr.clone().prop_map(|e| format!("({e})")),
            1 => (name(), prop::collection::vec(expr.clone(), 0..3), any::<bool>(), any::<bool>())
                .prop_map(|(callee, args, trailing, multiline)| {
                    let comma = if trailing && !args.is_empty() { "," } else { "" };
                    if multiline && !args.is_empty() {
                        format!("{callee}(\n  {}{comma}\n)", args.join(",\n  "))
                    } else {
                        format!("{callee}({}{comma})", args.join(", "))
                    }
                }),
            1 => (expr.clone(), block(expr.clone()), prop::option::of(block(expr.clone())))
                .prop_map(|(condition, then, otherwise)| match otherwise {
                    Some(otherwise) => format!("if {condition} {then} else {otherwise}"),
                    None => format!("if {condition} {then}"),
                }),
            1 => block(expr.clone()),
        ]
        .boxed();
        // Prefix operators are glued to their operand.
        let unary = prop_oneof![
            6 => atom.clone(),
            1 => (prop::sample::select(&["-", "!"][..]), atom).prop_map(|(op, e)| format!("{op}{e}")),
        ]
        .boxed();
        // At most one operator per tier: five tiers already compound, and
        // program size is what generation time and shrinking scale with —
        // three operands per tier made the average program 6 KB.
        let product = chain(unary, &["*", "/", "%"], 2);
        let sum = chain(product, &["+", "-"], 2);
        // Comparisons never chain.
        let comparison = chain(sum, &["==", "!=", "<", "<=", ">", ">="], 2);
        let conjunction = chain(comparison, &["&&"], 2);
        chain(conjunction, &["||"], 2)
    })
    .boxed()
}

fn statement(expr: BoxedStrategy<String>) -> BoxedStrategy<String> {
    prop_oneof![
        3 => expr.clone(),
        2 => (any::<bool>(), name(), any::<bool>(), expr.clone()).prop_map(|(mutable, name, typed, init)| {
            let mutable = if mutable { "mut " } else { "" };
            let ty = if typed { ": int" } else { "" };
            format!("let {mutable}{name}{ty} = {init}")
        }),
        1 => expr.clone().prop_map(|e| format!("_ = {e}")),
        1 => prop::option::of(expr).prop_map(|value| match value {
            Some(value) => format!("return {value}"),
            None => "return".to_owned(),
        }),
    ]
    .boxed()
}

/// A block: one statement per line, or a single expression on the braces'
/// line, or nothing.
fn block(expr: BoxedStrategy<String>) -> BoxedStrategy<String> {
    prop_oneof![
        1 => Just("{}".to_owned()),
        2 => expr.clone().prop_map(|e| format!("{{ {e} }}")),
        3 => prop::collection::vec((statement(expr), any::<bool>()), 1..4).prop_map(|statements| {
            let lines: Vec<String> = statements
                .into_iter()
                .map(|(statement, comment)| if comment { format!("{statement} // c") } else { statement })
                .collect();
            format!("{{\n{}\n}}", lines.join("\n"))
        }),
    ]
    .boxed()
}

fn program() -> BoxedStrategy<String> {
    let item = (
        name(),
        prop::collection::vec(name(), 0..3),
        any::<bool>(),
        any::<bool>(),
        block(expr()),
    )
        .prop_map(|(name, params, trailing, returns, body)| {
            let params: Vec<String> = params.into_iter().map(|p| format!("{p}: int")).collect();
            let comma = if trailing && !params.is_empty() {
                ","
            } else {
                ""
            };
            let returns = if returns { " -> int" } else { "" };
            format!("fn {name}({}{comma}){returns} {body}", params.join(", "))
        });
    (any::<bool>(), prop::collection::vec(item, 0..3))
        .prop_map(|(comment, items)| {
            let mut text = if comment {
                "// file\n".to_owned()
            } else {
                String::new()
            };
            text.push_str(&items.join("\n\n"));
            text.push('\n');
            text
        })
        .boxed()
}
