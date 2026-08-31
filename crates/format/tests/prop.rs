//! Normalization properties over generated token soup.

use proptest::prelude::*;
use sumi_format::normalize;
use sumi_lexer::{LexedFile, lex};
use sumi_syntax::{CookedFile, NodeKind, Parse, ParserInput, SyntaxKind, SyntaxTree, cook, parse};

/// Source fragments, valid and pathological, echoing the parser soup
/// property; concatenation composes the adjacencies goldens cannot
/// enumerate.
const FRAGMENTS: &[&str] = &[
    "fn", "let", "if", "else", "return", "true", "false", "mut", "x", "foo", "_", "Δx", "0", "123",
    "1.5", "2.5e-3", "1e", "0123", "1u32", "\"abc\"", "\"open", "'a'", "r\"a\"", "(", ")", "{",
    "}", ",", ":", ".", "=", "<", ">", "!", "+", "-", "*", "/", "%", "&", "|", ";", "[", " ", "\t",
    "\n", "\r\n", "\r", "// c", "€",
];

/// Token soup, half the time wrapped in a function body: violations are
/// recorded while parsing expressions, which live in blocks.
fn soup() -> impl Strategy<Value = String> {
    let fragments = proptest::collection::vec(prop::sample::select(FRAGMENTS), 0..48)
        .prop_map(|fragments| fragments.concat());
    prop_oneof![
        1 => fragments.clone(),
        1 => fragments.prop_map(|soup| format!("fn f() {{ {soup} }}")),
    ]
}

struct Front {
    lexed: LexedFile,
    cooked: CookedFile,
    parse: Parse,
}

fn front(source: &str) -> Front {
    let lexed = lex(source).expect("generated sources fit in u32");
    let cooked = cook(source, &lexed);
    let parse = parse(&ParserInput::new(&cooked));
    Front {
        lexed,
        cooked,
        parse,
    }
}

/// The tree's shape: depth and kind per node, in preorder — everything
/// about the parse that layout edits must not move.
fn shape(tree: &SyntaxTree) -> Vec<(usize, NodeKind)> {
    let mut nodes = Vec::new();
    let mut pending = vec![(tree.root(), 0usize)];
    while let Some((node, depth)) = pending.pop() {
        nodes.push((depth, tree.kind(node)));
        pending.extend(tree.children(node).map(|child| (child, depth + 1)));
    }
    nodes
}

/// The significant tokens, kinds and texts in order: the stream normalize
/// may respace but never rewrite.
fn significant<'src>(front: &Front, source: &'src str) -> Vec<(SyntaxKind, &'src str)> {
    (0..front.cooked.len())
        .filter(|&index| {
            !matches!(
                front.cooked.kind(index),
                SyntaxKind::Whitespace | SyntaxKind::Newline | SyntaxKind::LineComment
            )
        })
        .map(|index| (front.cooked.kind(index), front.lexed.text(source, index)))
        .collect()
}

/// The comments in order: an operator may hop one, but none is ever
/// deleted or reordered against another.
fn comments<'src>(front: &Front, source: &'src str) -> Vec<&'src str> {
    (0..front.cooked.len())
        .filter(|&index| front.cooked.kind(index) == SyntaxKind::LineComment)
        .map(|index| front.lexed.text(source, index))
        .collect()
}

proptest! {
    #[test]
    fn normalize_preserves_the_parse_and_settles(source in soup()) {
        let before = front(&source);
        let normalized = normalize(&source, &before.lexed, &before.cooked, &before.parse);
        let after = front(&normalized);

        // Layout edits keep every significant token and every comment.
        prop_assert_eq!(
            significant(&after, &normalized),
            significant(&before, &source),
            "normalize rewrote tokens of {:?} -> {:?}", source, normalized
        );
        prop_assert_eq!(
            comments(&after, &normalized),
            comments(&before, &source),
            "normalize lost a comment of {:?} -> {:?}", source, normalized
        );

        // And reparse to the same tree.
        prop_assert_eq!(
            shape(after.parse.tree()),
            shape(before.parse.tree()),
            "normalize changed the shape of {:?} -> {:?}", source, normalized
        );

        // A second pass finds nothing left to do.
        let again = normalize(&normalized, &after.lexed, &after.cooked, &after.parse);
        prop_assert_eq!(&again, &normalized, "normalize of {:?} is not idempotent", source);
    }
}
