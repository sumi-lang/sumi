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

use sumi_lexer::{LexedFile, RawIdx};
use sumi_syntax::{NodeIdx, NodeKind, ParserInput, SigIdx, SyntaxKind, SyntaxTree};

use crate::trivia::{GapSignal, signal};

/// The layout-free content of one file: its items, and the signal of the
/// gaps around them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Rep<'s> {
    /// One entry per child of the root, in source order.
    pub items: Vec<ItemRep<'s>>,
    /// The gap before each item, then the gap after the last one.
    pub edges: Vec<GapSignal<'s>>,
}

/// The layout-free content of one top-level item.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ItemRep<'s> {
    pub kind: NodeKind,
    /// The significant tokens, layout commas erased.
    pub tokens: Vec<(SyntaxKind, &'s str)>,
    /// Every node of the subtree in postorder: its kind, extent, and range
    /// in erased significant indices relative to the item.
    pub nodes: Vec<(NodeKind, u32, u32, u32)>,
    /// The signal of every gap inside the item, in order; the gaps around
    /// an erased comma count as one.
    pub gaps: Vec<GapSignal<'s>>,
}

/// The layout-free content of `source`, which `lexed`, `input`, and `tree`
/// must be the products of.
pub fn rep<'s>(
    source: &'s str,
    lexed: &LexedFile,
    input: &ParserInput,
    tree: &SyntaxTree,
) -> Rep<'s> {
    let n = input.len();
    let sig_of_raw = sig_of_raw(input, lexed);
    let first_sig = |node: NodeIdx| sig_of_raw[tree.first_token(node).to_usize()];
    let end_sig = |node: NodeIdx| {
        let end = tree.end_token(node);
        if end == tree.first_token(node) {
            first_sig(node)
        } else {
            sig_of_raw[end.to_usize() - 1] + 1
        }
    };

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
    let trivia = |gap: usize| -> Vec<RawIdx> {
        let start = |gap: usize| {
            if gap == 0 {
                RawIdx::new(0)
            } else {
                input.token(SigIdx::new(gap as u32 - 1)) + 1
            }
        };
        let end = if gap == n {
            lexed.end()
        } else {
            input.token(SigIdx::new(gap as u32))
        };
        let mut tokens: Vec<RawIdx> = Vec::new();
        if gap > 0 && erased[gap - 1] {
            tokens.extend(start(gap - 1).until(input.token(SigIdx::new(gap as u32 - 1))));
        }
        tokens.extend(start(gap).until(end));
        tokens
    };
    let signal_of = |gap: usize| signal(source, lexed, input, gap, trivia(gap).into_iter());

    let mut items = Vec::new();
    let mut edges = Vec::new();
    for item in tree.children_in_order(tree.root()) {
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
        let subtree_start = item.to_usize() + 1 - tree.subtree_len(item);
        let nodes = (subtree_start..=item.to_usize())
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

/// The significant index of every raw token, meaningful at the significant
/// ones only.
pub(crate) fn sig_of_raw(input: &ParserInput, lexed: &LexedFile) -> Vec<u32> {
    let mut map = vec![u32::MAX; lexed.len()];
    for sig in input.indices() {
        map[input.token(sig).to_usize()] = sig.to_u32();
    }
    map
}
