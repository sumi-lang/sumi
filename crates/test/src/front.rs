//! Every front-end product for one source, with the span and shape helpers
//! the recovery measurements compare across an edit.

use sumi_lexer::{LexedFile, lex};
use sumi_syntax::{NodeIdx, NodeKind, Parse, ParserInput, RawIdx, parse};

/// Every front-end product for one source.
pub struct Front {
    pub lexed: LexedFile,
    pub parse: Parse,
}

pub fn front(source: &str) -> Front {
    let lexed = lex(source).expect("test sources fit in u32");
    let parse = parse(ParserInput::new(&lexed));
    Front { lexed, parse }
}

impl Front {
    /// The byte spans of the significant tokens.
    pub fn spans(&self) -> Vec<(usize, usize)> {
        let input = self.parse.input();
        input
            .indices()
            .map(|index| {
                let range = self.lexed.range(input.token(index));
                (range.start().to_usize(), range.end().to_usize())
            })
            .collect()
    }

    /// The byte span of a node.
    pub fn node_span(&self, node: NodeIdx) -> (usize, usize) {
        let range = self.parse.tree().byte_range(node, &self.lexed);
        (range.start().to_usize(), range.end().to_usize())
    }

    /// A node's text and the shape of its subtree: kinds with byte spans
    /// relative to the node, in preorder.
    pub fn shape(&self, source: &str, node: NodeIdx) -> (String, Vec<(NodeKind, usize, usize)>) {
        let tree = self.parse.tree();
        let (base, stop) = self.node_span(node);
        let nodes = (node.to_usize()..node.to_usize() + tree.subtree_len(node))
            .map(|index| NodeIdx::new(index as u32))
            .map(|node| {
                let (start, end) = self.node_span(node);
                (tree.kind(node), start - base, end - base)
            })
            .collect();
        (source[base..stop].to_owned(), nodes)
    }

    /// The items, and the statements of their bodies, that cover none of
    /// the raw tokens in `touched`: what an edit there must leave alone.
    /// The statements of a body whose `{` is among the raw tokens in
    /// `moved` are not among them: an edit that removes or moves the
    /// delimiter they sit inside necessarily reparents them.
    pub fn guarded(&self, touched: &[RawIdx], moved: &[RawIdx]) -> Vec<NodeIdx> {
        let tree = self.parse.tree();
        let mut nodes = Vec::new();
        for item in tree.children(tree.root()) {
            nodes.push(item);
            for child in tree.children(item) {
                if tree.kind(child) == NodeKind::Block && !moved.contains(&tree.first_token(child))
                {
                    nodes.extend(tree.children(child));
                }
            }
        }
        nodes.retain(|&node| {
            !touched
                .iter()
                .any(|&token| tree.first_token(node) <= token && token < tree.end_token(node))
        });
        nodes
    }
}

/// The start byte of raw token `token`, or the end of the source one past
/// the last token.
pub fn start_byte(lexed: &LexedFile, token: RawIdx) -> u32 {
    lexed.boundary(token).to_u32()
}
