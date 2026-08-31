//! Property tests: cook and ParserInput invariants over generated sources
//! instead of the hand-written corpus in `cook.rs` and `input.rs`.
//!
//! The well-formed program generator and the single-edit machinery live in
//! `sumi-test`, shared with any harness that measures recovery quality.

use std::collections::HashSet;

use proptest::prelude::*;
use sumi_lexer::{RawKind, lex};
use sumi_syntax::{
    NodeKind, ParseAnchor, ParseEvidence, ParserInput, SyntaxKind, SyntaxTree, cook, parse,
};
use sumi_test::{apply, delimiter_edited_program, front, non_delimiter_edited_program, program};

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

/// Fragments free of `)` and `}` (each would close the wrapping paren), of
/// `{` (it would restore termination), and of a lone `(` (it would take
/// the wrapping paren's closer, leaving the wrapper unclosed and suspending
/// nothing) — nested parens come closed — for
/// [`newlines_inside_parens_never_terminate`].
const PAREN_SAFE: &[&str] = &[
    "fn", "let", "if", "else", "return", "true", "x", "foo", "0", "1.5", "2.5e-3", "1e", "\"s\"",
    "'a'", "r\"a\"", "(x)", "(\nx\n)", ",", ":", ".", "=", "<", ">", "!", "+", "-", "*", "/", "%",
    "&", "|", " ", "\t", "\n", "\r\n", "// c\n",
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
            let token = lexed.range(error.token as usize);
            prop_assert!(token.start() <= error.range.start());
            prop_assert!(error.range.end() <= token.end());
            prop_assert!(source.is_char_boundary(error.range.start().to_usize()));
            prop_assert!(source.is_char_boundary(error.range.end().to_usize()));
            // Diagnostic ownership does not overlap: a token the lexer
            // reported gets no further errors from the cook.
            prop_assert!(
                !lexed.errors().iter().any(|lex_error| lex_error.token == error.token),
                "token {} has both a lex and a cook error", error.token
            );
        }

        // An earlier phase owns diagnostics for `Error` tokens, so every one
        // must have evidence from the lexer or cooker.
        for index in 0..cooked.len() {
            if cooked.kind(index) == SyntaxKind::Error {
                let token = index as u32;
                prop_assert!(
                    lexed.errors().iter().any(|error| error.token == token)
                        || cooked.errors().iter().any(|error| error.token == token),
                    "error token {} has no lex or cook error", token
                );
            }
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
        // Pieces can form a `//` that hides the wrapping paren's closer;
        // only a `(` the stream closes suspends termination.
        prop_assume!(input.partner(1) == Some(input.len() - 1));
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
    let root = tree.root();
    prop_assert_eq!(tree.kind(root), NodeKind::SourceFile);
    prop_assert_eq!((tree.first_token(root), tree.end_token(root)), (0, raw_len));

    let mut visited = 0usize;
    let mut pending = vec![root];
    while let Some(node) = pending.pop() {
        visited += 1;
        let (first, end) = (tree.first_token(node), tree.end_token(node));
        if node != root {
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
        // Children come last first, so ordering is checked back to front.
        let mut next_start = end;
        for child in tree.children(node) {
            prop_assert!(
                tree.end_token(child) <= next_start,
                "children of {} overlap",
                node
            );
            prop_assert!(
                tree.first_token(child) >= first,
                "child {} escapes {}",
                child,
                node
            );
            next_start = tree.first_token(child);
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

        // The tree is lossless: walking its elements reprints the source.
        prop_assert_eq!(&sumi_format::reprint(tree, &lexed, &source), &source);

        // The parser attaches no token to the root itself: every significant
        // token lies in some item or top-level error node.
        let mut items: Vec<usize> = tree.children(tree.root()).collect();
        items.reverse();
        let mut children = items.into_iter().peekable();
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

        // Present syntax gets nonempty in-bounds raw ranges. Missing syntax
        // gets the exact, possibly empty trivia interval between significant
        // tokens. Recovery effects are nonempty in-bounds ranges too.
        let raw_len = cooked.len() as u32;
        for evidence in parse.evidence() {
            let anchor = match evidence {
                ParseEvidence::Recovery(recovery) => {
                    let mut previous_end = None;
                    for skipped in &recovery.skipped {
                        prop_assert!(skipped.start() < skipped.end());
                        prop_assert!(skipped.end() <= raw_len);
                        if let Some(previous_end) = previous_end {
                            prop_assert!(previous_end <= skipped.start());
                        }
                        previous_end = Some(skipped.end());
                    }
                    recovery.anchor
                }
                ParseEvidence::Violation(violation) => ParseAnchor::Tokens(violation.range),
            };
            match anchor {
                ParseAnchor::Tokens(range) => {
                    prop_assert!(range.start() < range.end());
                    prop_assert!(range.end() <= raw_len);
                }
                ParseAnchor::Gap(gap) => {
                    prop_assert!(gap.trivia_start() <= gap.trivia_end());
                    prop_assert!(gap.trivia_end() <= raw_len);
                    if gap.trivia_start() > 0 {
                        prop_assert!(!is_trivia(cooked.kind(gap.trivia_start() as usize - 1)));
                    }
                    for token in gap.trivia_start()..gap.trivia_end() {
                        prop_assert!(is_trivia(cooked.kind(token as usize)));
                    }
                    if gap.trivia_end() < raw_len {
                        prop_assert!(!is_trivia(cooked.kind(gap.trivia_end() as usize)));
                    }
                }
            }
        }
    }

    #[test]
    fn well_formed_programs_produce_no_parse_evidence(source in program()) {
        let lexed = lex(&source).expect("generated sources fit in u32");
        prop_assert!(lexed.errors().is_empty(), "lexer errors in {:?}", source);
        let cooked = cook(&source, &lexed);
        prop_assert!(cooked.errors().is_empty(), "cook errors in {:?}", source);
        let parse = parse(&ParserInput::new(&cooked));
        check_tree(parse.tree(), &cooked)?;
        prop_assert!(
            parse.evidence().is_empty(),
            "parse evidence {:?} in {:?}", parse.evidence(), source
        );
    }
}

// Recovery quality, measured. The tests above prove the parser is total and
// accepts every well-formed program. These require recovery after one edit to
// remain local: at statement level for non-delimiters, and at item level for
// delimiters, which can legitimately reparent nearby syntax.

proptest! {
    #[test]
    fn a_single_non_delimiter_edit_disturbs_only_where_it_lands(
        (source, index, edit) in non_delimiter_edited_program()
    ) {
        let original = front(&source);
        let (edited, touched, moved, impact) = apply(&source, &original.spans(), index, edit);
        let touched: Vec<u32> = touched.iter().map(|&index| original.input.token(index)).collect();
        let moved: Vec<u32> = moved.iter().map(|&index| original.input.token(index)).collect();
        let after = front(&edited);
        let survivors: HashSet<_> = (0..after.parse.tree().len())
            .map(|node| (after.node_span(node), after.shape(&edited, node)))
            .collect();
        for node in original.guarded(&touched, &moved) {
            let shape = original.shape(&source, node);
            let span = impact.map(original.node_span(node));
            prop_assert!(
                survivors.contains(&(span, shape.clone())),
                "{:?} at token {} ({:?}) disturbs the {:?} {:?}\n--- original ---\n{}\n--- edited ---\n{}\nevidence: {:?}",
                edit, index, original.input.get(index), original.parse.tree().kind(node), shape.0,
                source, edited, after.parse.evidence()
            );
        }
    }

    #[test]
    fn a_single_delimiter_edit_preserves_unaffected_items(
        (source, index, edit) in delimiter_edited_program()
    ) {
        let original = front(&source);
        let (edited, touched, _, impact) = apply(&source, &original.spans(), index, edit);
        let touched: Vec<u32> = touched.iter().map(|&index| original.input.token(index)).collect();
        let after = front(&edited);
        let tree = after.parse.tree();
        let survivors: HashSet<_> = tree
            .children(tree.root())
            .filter(|&node| tree.kind(node) == NodeKind::FnItem)
            .map(|node| (after.node_span(node), after.shape(&edited, node)))
            .collect();

        let tree = original.parse.tree();
        for item in tree.children(tree.root()).filter(|&node| {
            tree.kind(node) == NodeKind::FnItem
                && !touched.iter().any(|&token| {
                    tree.first_token(node) <= token && token < tree.end_token(node)
                })
        }) {
            let shape = original.shape(&source, item);
            let span = impact.map(original.node_span(item));
            prop_assert!(
                survivors.contains(&(span, shape.clone())),
                "{:?} at token {} ({:?}) disturbs the item {:?}\n--- original ---\n{}\n--- edited ---\n{}\nevidence: {:?}",
                edit, index, original.input.get(index), shape.0, source, edited,
                after.parse.evidence()
            );
        }
    }
}
