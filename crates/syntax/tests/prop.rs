//! Property tests: ParserInput invariants over generated sources instead of
//! the hand-written corpus in `input.rs`.
//!
//! The well-formed program generator and the single-edit machinery live in
//! `sumi-test`, shared with any harness that measures recovery quality.

use std::collections::HashSet;

use proptest::prelude::*;
use sumi_lexer::{LexedFile, RawKind, lex};
use sumi_syntax::{
    NodeIdx, NodeKind, ParseAnchor, ParseEvidence, ParserInput, RawIdx, SigIdx, SyntaxKind,
    SyntaxTree, parse,
};
use sumi_test::{apply, delimiter_edited_program, front, non_delimiter_edited_program, program};

/// Source fragments beyond every keyword and punctuation text of the
/// language, valid and pathological; concatenation composes the adjacencies
/// goldens cannot enumerate.
const EXTRA_FRAGMENTS: &[&str] = &[
    "x",
    "foo",
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

/// Every fixed token text of the language, then [`EXTRA_FRAGMENTS`].
fn fragments() -> Vec<&'static str> {
    SyntaxKind::ALL
        .iter()
        .filter_map(|kind| kind.text())
        .chain(EXTRA_FRAGMENTS.iter().copied())
        .collect()
}

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
        9 => prop::sample::select(fragments()).prop_map(str::to_owned),
        1 => proptest::collection::vec(any::<char>(), 0..4)
            .prop_map(|chars| chars.into_iter().collect::<String>()),
    ]
}

fn soup() -> impl Strategy<Value = String> {
    proptest::collection::vec(fragment(), 0..64).prop_map(|fragments| fragments.concat())
}

/// The significant index of position `index` in a program's spans.
fn sig(index: usize) -> SigIdx {
    SigIdx::new(u32::try_from(index).expect("significant positions fit in u32"))
}

fn is_trivia(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::Whitespace | SyntaxKind::Newline | SyntaxKind::LineComment
    )
}

proptest! {
    #[test]
    fn parser_input_invariants(source in soup()) {
        let lexed = lex(&source).expect("generated sources fit in u32");
        let input = ParserInput::new(&lexed);

        prop_assert!(input.len() <= lexed.len());
        prop_assert_eq!(input.get(input.end()), None);

        let mut previous: Option<RawIdx> = None;
        let mut open: Vec<SigIdx> = Vec::new();
        for index in input.indices() {
            let token = input.token(index);
            let kind = input.get(index).expect("indices below len are present");
            if let Some(previous) = previous {
                prop_assert!(previous < token, "token mappings must strictly increase");
            }
            prop_assert_eq!(kind, lexed.kind(token), "kinds must come from the scan");
            prop_assert!(!is_trivia(kind), "token {:?} is trivia", index);

            // Everything skipped between kept tokens must be trivia, and the
            // newline fact must match what was skipped.
            let skipped = previous.map_or(RawIdx::new(0), |previous| previous + 1).until(token);
            let newline = skipped.clone().any(|j| lexed.kind(j) == SyntaxKind::Newline);
            for j in skipped {
                prop_assert!(is_trivia(lexed.kind(j)), "token {:?} was dropped", j);
            }
            prop_assert_eq!(input.newline_before(index), newline);

            // Jointness is adjacency, checked through ranges rather than
            // token indices.
            if index + 1 < input.end() {
                let next = input.token(index + 1);
                let adjacent = lexed.range(token).end() == lexed.range(next).start();
                prop_assert_eq!(input.is_joint(index), adjacent);
            } else {
                prop_assert!(!input.is_joint(index));
            }

            if input.boundary_before(index) {
                prop_assert!(index > SigIdx::new(0), "no boundary before the first token");
                prop_assert!(input.newline_before(index), "boundaries need a newline");
            }

            // Partners are mutual, of matching kinds, and nest: an opener
            // whose partner lies ahead is pushed, and a closer must close
            // the innermost open pair.
            if let Some(partner) = input.partner(index) {
                prop_assert!(partner < input.end());
                prop_assert_eq!(input.partner(partner), Some(index), "partners must be mutual");
                let (opener, closer) = if index < partner { (index, partner) } else { (partner, index) };
                prop_assert!(
                    matches!(
                        (input.get(opener), input.get(closer)),
                        (Some(SyntaxKind::LParen), Some(SyntaxKind::RParen))
                            | (Some(SyntaxKind::LBrace), Some(SyntaxKind::RBrace))
                    ),
                    "tokens {:?} and {:?} are partners but not a matching pair", opener, closer
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
        for j in previous.map_or(RawIdx::new(0), |previous| previous + 1).until(lexed.end()) {
            prop_assert!(is_trivia(lexed.kind(j)), "token {:?} was dropped", j);
        }
    }

    #[test]
    fn widening_space_runs_changes_nothing(source in soup()) {
        let lexed = lex(&source).expect("generated sources fit in u32");
        let mut widened = String::new();
        for index in lexed.indices() {
            widened.push_str(lexed.text(&source, index));
            if lexed.raw_kind(index) == RawKind::HorizontalSpace {
                widened.push(' ');
            }
        }

        // Widening an existing space run merges back into the same token, so
        // everything but the ranges is untouched: kinds, jointness, newline
        // facts, and boundaries.
        let widened_lexed = lex(&widened).expect("widened sources fit in u32");
        prop_assert_eq!(widened_lexed.len(), lexed.len());

        for index in lexed.indices() {
            prop_assert_eq!(lexed.kind(index), widened_lexed.kind(index));
        }

        let input = ParserInput::new(&lexed);
        let widened_input = ParserInput::new(&widened_lexed);
        prop_assert_eq!(input.len(), widened_input.len());
        for index in input.indices() {
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
        let input = ParserInput::new(&lexed);
        // Pieces can form a `//` that hides the wrapping paren's closer;
        // only a `(` the stream closes suspends termination.
        prop_assume!(input.partner(SigIdx::new(1)) == Some(input.end() - 1));
        for index in input.indices() {
            prop_assert!(
                !input.boundary_before(index),
                "boundary before token {:?} in {:?}", index, source
            );
        }
    }
}

/// Walk `tree` and check every structural invariant: extents partition the
/// nodes; children are ordered, disjoint, and inside their parent; every
/// node but the root covers at least one token and starts and ends on a
/// significant one; the root covers the whole buffer.
fn check_tree(tree: &SyntaxTree, lexed: &LexedFile) -> Result<(), TestCaseError> {
    let raw_len = lexed.end();
    let root = tree.root();
    prop_assert_eq!(tree.kind(root), NodeKind::SourceFile);
    prop_assert_eq!(
        (tree.first_token(root), tree.end_token(root)),
        (RawIdx::new(0), raw_len)
    );

    let mut visited = 0usize;
    let mut pending = vec![root];
    while let Some(node) = pending.pop() {
        visited += 1;
        let (first, end) = (tree.first_token(node), tree.end_token(node));
        if node != root {
            prop_assert!(first < end, "node {:?} is empty", node);
            prop_assert!(
                !is_trivia(lexed.kind(first)),
                "node {:?} starts on trivia",
                node
            );
            prop_assert!(
                !is_trivia(lexed.kind(end - 1)),
                "node {:?} ends on trivia",
                node
            );
        }
        // Children come last first, so ordering is checked back to front.
        let mut next_start = end;
        for child in tree.children(node) {
            prop_assert!(
                tree.end_token(child) <= next_start,
                "children of {:?} overlap",
                node
            );
            prop_assert!(
                tree.first_token(child) >= first,
                "child {:?} escapes {:?}",
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
        let input = ParserInput::new(&lexed);
        let parse = parse(&input);
        let tree = parse.tree();
        check_tree(tree, &lexed)?;

        // The tree is lossless: walking its elements reprints the source.
        prop_assert_eq!(&sumi_format::reprint(tree, &lexed, &source), &source);

        // The parser attaches no token to the root itself: every significant
        // token lies in some item or top-level error node.
        let mut items: Vec<NodeIdx> = tree.children(tree.root()).collect();
        items.reverse();
        let mut children = items.into_iter().peekable();
        for index in input.indices() {
            let token = input.token(index);
            while children.peek().is_some_and(|&child| tree.end_token(child) <= token) {
                children.next();
            }
            prop_assert!(
                children.peek().is_some_and(|&child| tree.first_token(child) <= token),
                "token {:?} is attached to the root", token
            );
        }

        // Present syntax gets nonempty in-bounds raw ranges. Missing syntax
        // gets the exact, possibly empty trivia interval between significant
        // tokens. Recovery effects are nonempty in-bounds ranges too.
        let raw_len = lexed.end();
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
                    if let Some(before) = gap.trivia_start().checked_sub(1) {
                        prop_assert!(!is_trivia(lexed.kind(before)));
                    }
                    for token in gap.trivia_start().until(gap.trivia_end()) {
                        prop_assert!(is_trivia(lexed.kind(token)));
                    }
                    if gap.trivia_end() < raw_len {
                        prop_assert!(!is_trivia(lexed.kind(gap.trivia_end())));
                    }
                }
            }
        }
    }

    #[test]
    fn well_formed_programs_produce_no_parse_evidence(source in program()) {
        let lexed = lex(&source).expect("generated sources fit in u32");
        prop_assert!(lexed.errors().is_empty(), "lexer errors in {:?}", source);
        let parse = parse(&ParserInput::new(&lexed));
        check_tree(parse.tree(), &lexed)?;
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
        let touched: Vec<RawIdx> = touched.iter().map(|&index| original.input.token(sig(index))).collect();
        let moved: Vec<RawIdx> = moved.iter().map(|&index| original.input.token(sig(index))).collect();
        let after = front(&edited);
        let survivors: HashSet<_> = after.parse.tree().nodes()
            .map(|node| (after.node_span(node), after.shape(&edited, node)))
            .collect();
        for node in original.guarded(&touched, &moved) {
            let shape = original.shape(&source, node);
            let span = impact.map(original.node_span(node));
            prop_assert!(
                survivors.contains(&(span, shape.clone())),
                "{:?} at token {} ({:?}) disturbs the {:?} {:?}\n--- original ---\n{}\n--- edited ---\n{}\nevidence: {:?}",
                edit, index, original.input.get(sig(index)), original.parse.tree().kind(node), shape.0,
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
        let touched: Vec<RawIdx> = touched.iter().map(|&index| original.input.token(sig(index))).collect();
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
                edit, index, original.input.get(sig(index)), shape.0, source, edited,
                after.parse.evidence()
            );
        }
    }
}
