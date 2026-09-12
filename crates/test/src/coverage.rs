//! Grammar coverage: whether a body of trees reaches every node kind and
//! every child `sumi.grammar` allows a node. The witnesses are generated
//! from the grammar, one per child of every node rule; this module gives
//! them their shape and keeps the account over trees. Only a node without
//! an error counts, since one with an error may lack any child, and its
//! lacking one then says nothing about what the grammar allows.

use sumi_lexer::{LexedFile, RawIdx};
use sumi_syntax::{BinaryOp, NodeIdx, NodeKind, SyntaxKind, SyntaxTree, binary_operator};

pub use crate::generated::WITNESSES;

/// One child a node rule allows, and how to tell whether a node has it.
pub struct Witness {
    /// The node kind whose rule allows the child.
    pub parent: NodeKind,
    /// The child as the rule writes it: a token text, a token kind, or an
    /// accessor and the kind it answers.
    pub name: &'static str,
    /// Whether the rule lets a node lack the child: under `?` or `*`.
    pub optional: bool,
    /// Whether this node, of the parent kind and without an error, has
    /// the child.
    pub present: fn(&LexedFile, &SyntaxTree, NodeIdx) -> bool,
}

/// The raw tokens `node` covers that none of its children does.
fn own_tokens(tree: &SyntaxTree, node: NodeIdx) -> Vec<RawIdx> {
    (tree.first_token(node).to_usize()..tree.end_token(node).to_usize())
        .map(|raw| RawIdx::new(raw as u32))
        .filter(|&raw| tree.covering(raw) == node)
        .collect()
}

/// Whether `node` itself holds a glued run of tokens of these kinds.
pub fn has_tokens(
    lexed: &LexedFile,
    tree: &SyntaxTree,
    node: NodeIdx,
    kinds: &[SyntaxKind],
) -> bool {
    let own = own_tokens(tree, node);
    own.iter().any(|&first| {
        kinds.iter().enumerate().all(|(offset, &kind)| {
            let raw = RawIdx::new((first.to_usize() + offset) as u32);
            own.contains(&raw) && lexed.kind(raw) == kind
        })
    })
}

/// Whether `node` itself holds the tokens of binary operator `op`.
pub fn has_operator(lexed: &LexedFile, tree: &SyntaxTree, node: NodeIdx, op: BinaryOp) -> bool {
    own_tokens(tree, node).into_iter().any(|raw| {
        let next = RawIdx::new(raw.to_usize() as u32 + 1);
        let glued = (next < tree.end_token(node))
            .then(|| lexed.kind(next))
            .filter(|kind| !kind.is_trivia());
        binary_operator(lexed.kind(raw), glued).is_some_and(|(found, _)| found == op)
    })
}

/// The account of what a body of trees has witnessed.
pub struct Coverage {
    kinds: Vec<bool>,
    present: Vec<bool>,
    absent: Vec<bool>,
}

impl Default for Coverage {
    fn default() -> Self {
        Self::new()
    }
}

impl Coverage {
    pub fn new() -> Self {
        Self {
            kinds: vec![false; NodeKind::ALL.len()],
            present: vec![false; WITNESSES.len()],
            absent: vec![false; WITNESSES.len()],
        }
    }

    /// Record every node of `tree` without an error. `lexed` must be the
    /// file the tree was parsed from.
    pub fn record(&mut self, lexed: &LexedFile, tree: &SyntaxTree) {
        for node in tree.nodes() {
            if tree.has_error(node) {
                continue;
            }
            let kind = tree.kind(node);
            self.kinds[kind as usize] = true;
            for (index, witness) in WITNESSES.iter().enumerate() {
                if witness.parent != kind {
                    continue;
                }
                if (witness.present)(lexed, tree, node) {
                    self.present[index] = true;
                } else {
                    self.absent[index] = true;
                }
            }
        }
    }

    /// What the grammar allows that no recorded tree has shown, one line
    /// each: a node kind that never appears, a child never present, or an
    /// optional child never absent. Empty when the trees cover the grammar.
    pub fn missing(&self) -> Vec<String> {
        let mut missing = Vec::new();
        for (kind, &seen) in NodeKind::ALL.iter().zip(&self.kinds) {
            if !seen && *kind != NodeKind::Error {
                missing.push(format!("{kind:?} never appears"));
            }
        }
        for (index, witness) in WITNESSES.iter().enumerate() {
            let Witness { parent, name, .. } = witness;
            if !self.present[index] {
                missing.push(format!("{parent:?} never has {name}"));
            }
            if witness.optional && !self.absent[index] {
                missing.push(format!("{parent:?} never lacks {name}"));
            }
        }
        missing
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Kinds index the account by discriminant, in the order `ALL` lists.
    #[test]
    fn kinds_index_by_discriminant() {
        for (index, kind) in NodeKind::ALL.iter().enumerate() {
            assert_eq!(*kind as usize, index);
        }
    }
}
