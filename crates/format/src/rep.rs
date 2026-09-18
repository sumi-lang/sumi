//! Layout equivalence as a value. Two sources are layout-equivalent when
//! they lex to the same significant tokens, parse to the same tree over
//! them, and hold the same comments and retained blank lines at the same
//! positions among those tokens. [`rep`] is everything the parser sees
//! plus that retained signal, and nothing else: the formatter writes a
//! result only when its `rep` is the input's.
//!
//! The comma before a list closer is a layout token, the one token the
//! formatter may add or remove, so `rep` erases it and counts positions
//! without it.

use sumi_lexer::LexedFile;
use sumi_syntax::{NodeIdx, NodeKind, Parse, SigIdx, SyntaxKind};

use crate::trivia::{GapSignal, signal};

/// The layout-free content of one file: its items, and the signal of the
/// gaps around them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Rep<'s> {
    /// One entry per child of the root, in source order.
    pub(crate) items: Vec<ItemRep<'s>>,
    /// The gap before each item, then the gap after the last one.
    pub(crate) edges: Vec<GapSignal<'s>>,
}

/// The layout-free content of one top-level item.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ItemRep<'s> {
    kind: NodeKind,
    /// The significant tokens, layout commas erased.
    tokens: Vec<(SyntaxKind, &'s str)>,
    /// Every node of the subtree in preorder: its kind, extent, and range
    /// in erased significant indices relative to the item.
    nodes: Vec<(NodeKind, u32, u32, u32)>,
    /// The signal of every gap inside the item, in order; the gaps around
    /// an erased comma count as one.
    gaps: Vec<GapSignal<'s>>,
}

/// The layout-free content of `source`, which `lexed` and `parse` must be
/// the products of.
pub fn rep<'s>(source: &'s str, lexed: &LexedFile, parse: &Parse) -> Rep<'s> {
    let (input, tree) = (parse.input(), parse.tree());
    let n = input.len();
    let first_sig = |node: NodeIdx| crate::first_sig(tree, input, node);
    let end_sig = |node: NodeIdx| crate::end_sig(tree, input, node);

    let mut erased = vec![false; n];
    for node in tree.nodes() {
        if matches!(tree.kind(node), NodeKind::ArgList | NodeKind::ParamList)
            && !tree.has_error(node)
        {
            let end = end_sig(node) as usize;
            if end >= first_sig(node) as usize + 3
                && input.get(SigIdx::new(end as u32 - 2)) == Some(SyntaxKind::Comma)
                && input.get(SigIdx::new(end as u32 - 1)) == Some(SyntaxKind::RParen)
            {
                erased[end - 2] = true;
            }
        }
    }
    // Erased tokens before each significant index, one entry past the end.
    let mut before = vec![0u32; n + 1];
    for sig in 0..n {
        before[sig + 1] = before[sig] + u32::from(erased[sig]);
    }
    let erased_index = |sig: u32| sig - before[sig as usize];

    // The trivia of gap `gap`, the tokens before an erased comma included.
    let trivia = |gap: usize| {
        let range = input.trivia_before(SigIdx::new(gap as u32));
        range.start.until(range.end)
    };
    let signal_of = |gap: usize| {
        let before_comma = (gap > 0 && erased[gap - 1]).then(|| trivia(gap - 1));
        let tokens = before_comma.into_iter().flatten().chain(trivia(gap));
        signal(source, lexed, input, gap, tokens)
    };

    let mut items = Vec::new();
    let mut edges = Vec::new();
    for item in tree.children(tree.root()) {
        let (first, end) = (first_sig(item), end_sig(item));
        edges.push(signal_of(first as usize));
        let tokens = (first..end)
            .filter(|&sig| !erased[sig as usize])
            .map(|sig| {
                let sig = SigIdx::new(sig);
                (
                    input.get(sig).expect("a token in range"),
                    lexed.text(source, input.token(sig)),
                )
            })
            .collect();
        let base = erased_index(first);
        let nodes = (item.to_usize()..item.to_usize() + tree.subtree_len(item))
            .map(|node| NodeIdx::new(node as u32))
            .map(|node| {
                (
                    tree.kind(node),
                    tree.subtree_len(node) as u32,
                    erased_index(first_sig(node)) - base,
                    erased_index(end_sig(node)) - base,
                )
            })
            .collect();
        // The gap before an erased comma merges into the one after it.
        let gaps = (first as usize + 1..end as usize)
            .filter(|&gap| !erased[gap])
            .map(signal_of)
            .collect();
        items.push(ItemRep {
            kind: tree.kind(item),
            tokens,
            nodes,
            gaps,
        });
    }
    edges.push(signal_of(n));
    Rep { items, edges }
}
