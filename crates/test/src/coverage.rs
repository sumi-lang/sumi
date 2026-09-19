//! Grammar coverage: whether a body of trees reaches every node kind and
//! every child the grammar allows a node. The witnesses are the children
//! each view declares, read from [`NodeKind::children`], and [`RULES`],
//! what the rules say beyond the accessors. Only a node without an error
//! counts, since one with an error may lack any child, and its lacking one
//! then says nothing about what the grammar allows.

use sumi_lexer::{LexedFile, RawIdx};
use sumi_syntax::{BinaryOp, NodeIdx, NodeKind, SyntaxKind, SyntaxTree, binary_operator};

use NodeKind as N;
use SyntaxKind as T;

/// One child a node rule allows, and how to tell whether a node has it.
#[derive(Clone, Copy, Debug)]
pub enum Child {
    /// A child the view declares, as its accessor answers: absent when
    /// the slot holds a node of another kind than the view declares.
    Declared(fn(&SyntaxTree, NodeIdx) -> bool),
    /// The single child in this field slot, of this kind.
    FieldOf(u8, NodeKind),
    /// A glued run of tokens of these kinds among the node's own.
    Tokens(&'static [SyntaxKind]),
    /// A binary operator among the node's own tokens.
    Operator(BinaryOp),
}

/// What each rule allows beyond what its view declares: the tokens a node
/// holds itself, in the rule's order, the operator of a binary
/// expression, and the kinds an alternation admits in one field. `true`
/// marks a child the rule lets a node lack.
pub const RULES: &[(NodeKind, bool, Child)] = &[
    (N::FnItem, false, Child::Tokens(&[T::FnKw])),
    (N::FnItem, true, Child::Tokens(&[T::Minus, T::Gt])),
    (N::FnItem, true, Child::Tokens(&[T::Eq])),
    (N::ParamList, false, Child::Tokens(&[T::LParen])),
    (N::ParamList, true, Child::Tokens(&[T::Comma])),
    (N::ParamList, false, Child::Tokens(&[T::RParen])),
    (N::Param, true, Child::Tokens(&[T::Colon])),
    (N::Name, false, Child::Tokens(&[T::Ident])),
    (N::TypeRef, false, Child::Tokens(&[T::Ident])),
    (N::Block, false, Child::Tokens(&[T::LBrace])),
    (N::Block, false, Child::Tokens(&[T::RBrace])),
    (N::LetStmt, false, Child::Tokens(&[T::LetKw])),
    (N::LetStmt, true, Child::Tokens(&[T::MutKw])),
    (N::LetStmt, true, Child::Tokens(&[T::Colon])),
    (N::LetStmt, false, Child::Tokens(&[T::Eq])),
    (N::AssignStmt, false, Child::Tokens(&[T::Eq])),
    (N::DiscardStmt, false, Child::Tokens(&[T::Underscore])),
    (N::DiscardStmt, false, Child::Tokens(&[T::Eq])),
    (N::ReturnStmt, false, Child::Tokens(&[T::ReturnKw])),
    (N::NameRef, false, Child::Tokens(&[T::Ident])),
    (N::LiteralExpr, true, Child::Tokens(&[T::IntLiteral])),
    (N::LiteralExpr, true, Child::Tokens(&[T::StringLiteral])),
    (N::LiteralExpr, true, Child::Tokens(&[T::TrueKw])),
    (N::LiteralExpr, true, Child::Tokens(&[T::FalseKw])),
    (N::PrefixExpr, true, Child::Tokens(&[T::Minus])),
    (N::PrefixExpr, true, Child::Tokens(&[T::Bang])),
    (N::BinaryExpr, true, Child::Operator(BinaryOp::Or)),
    (N::BinaryExpr, true, Child::Operator(BinaryOp::And)),
    (N::BinaryExpr, true, Child::Operator(BinaryOp::Eq)),
    (N::BinaryExpr, true, Child::Operator(BinaryOp::Ne)),
    (N::BinaryExpr, true, Child::Operator(BinaryOp::Lt)),
    (N::BinaryExpr, true, Child::Operator(BinaryOp::Le)),
    (N::BinaryExpr, true, Child::Operator(BinaryOp::Gt)),
    (N::BinaryExpr, true, Child::Operator(BinaryOp::Ge)),
    (N::BinaryExpr, true, Child::Operator(BinaryOp::Add)),
    (N::BinaryExpr, true, Child::Operator(BinaryOp::Sub)),
    (N::BinaryExpr, true, Child::Operator(BinaryOp::Mul)),
    (N::BinaryExpr, true, Child::Operator(BinaryOp::Div)),
    (N::BinaryExpr, true, Child::Operator(BinaryOp::Rem)),
    (N::ParenExpr, false, Child::Tokens(&[T::LParen])),
    (N::ParenExpr, false, Child::Tokens(&[T::RParen])),
    (N::ArgList, false, Child::Tokens(&[T::LParen])),
    (N::ArgList, true, Child::Tokens(&[T::Comma])),
    (N::ArgList, false, Child::Tokens(&[T::RParen])),
    (N::IfExpr, false, Child::Tokens(&[T::IfKw])),
    (N::IfExpr, true, Child::Tokens(&[T::ElseKw])),
    (N::IfExpr, true, Child::FieldOf(2, N::IfExpr)),
    (N::IfExpr, true, Child::FieldOf(2, N::Block)),
    (N::ClosureExpr, false, Child::Tokens(&[T::FnKw])),
    (N::ClosureExpr, true, Child::Tokens(&[T::Minus, T::Gt])),
    (N::ClosureExpr, true, Child::Tokens(&[T::Eq])),
];

/// One child a node rule allows, as the account keeps it.
struct Witness {
    parent: NodeKind,
    /// The child as the rule writes it.
    name: String,
    /// Whether the rule lets a node lack the child.
    optional: bool,
    child: Child,
}

/// Every witness: the children each view declares, then [`RULES`].
fn witnesses() -> Vec<Witness> {
    let declared = NodeKind::ALL.iter().flat_map(|&parent| {
        parent.children().iter().map(move |child| Witness {
            parent,
            name: child.name.to_owned(),
            optional: child.optional,
            child: Child::Declared(child.present),
        })
    });
    let ruled = RULES.iter().map(|&(parent, optional, child)| Witness {
        parent,
        name: match child {
            Child::Tokens(kinds) => match kinds
                .iter()
                .map(|kind| kind.text())
                .collect::<Option<Vec<_>>>()
            {
                Some(text) => format!("'{}'", text.concat()),
                None => format!("{kinds:?}"),
            },
            Child::Operator(op) => format!("{op:?}"),
            Child::FieldOf(slot, kind) => {
                let field = &parent.children()[slot as usize];
                format!("{}: {kind:?}", field.name)
            }
            Child::Declared(_) => unreachable!("the views declare these"),
        },
        optional,
        child,
    });
    declared.chain(ruled).collect()
}

/// The raw tokens `node` covers that none of its children does.
fn own_tokens(tree: &SyntaxTree, node: NodeIdx) -> Vec<RawIdx> {
    (tree.first_token(node).to_usize()..tree.end_token(node).to_usize())
        .map(|raw| RawIdx::new(raw as u32))
        .filter(|&raw| tree.covering(raw) == node)
        .collect()
}

/// Whether `node` itself holds a glued run of tokens of these kinds.
fn has_tokens(lexed: &LexedFile, tree: &SyntaxTree, node: NodeIdx, kinds: &[SyntaxKind]) -> bool {
    let own = own_tokens(tree, node);
    own.iter().any(|&first| {
        kinds.iter().enumerate().all(|(offset, &kind)| {
            let raw = RawIdx::new((first.to_usize() + offset) as u32);
            own.contains(&raw) && lexed.kind(raw) == kind
        })
    })
}

/// Whether `node` itself holds the tokens of binary operator `op`.
fn has_operator(lexed: &LexedFile, tree: &SyntaxTree, node: NodeIdx, op: BinaryOp) -> bool {
    own_tokens(tree, node).into_iter().any(|raw| {
        let next = RawIdx::new(raw.to_usize() as u32 + 1);
        let glued = (next < tree.end_token(node))
            .then(|| lexed.kind(next))
            .filter(|kind| !kind.is_trivia());
        binary_operator(lexed.kind(raw), glued).is_some_and(|(found, _)| found == op)
    })
}

/// Whether this node, of the witness's parent kind and without an error,
/// has the child.
fn present(lexed: &LexedFile, tree: &SyntaxTree, node: NodeIdx, child: Child) -> bool {
    match child {
        Child::Declared(present) => present(tree, node),
        Child::FieldOf(slot, kind) => tree
            .child_in_field(node, slot)
            .is_some_and(|child| tree.kind(child) == kind),
        Child::Tokens(kinds) => has_tokens(lexed, tree, node, kinds),
        Child::Operator(op) => has_operator(lexed, tree, node, op),
    }
}

/// The account of what a body of trees has witnessed.
pub struct Coverage {
    witnesses: Vec<Witness>,
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
        let witnesses = witnesses();
        Self {
            kinds: vec![false; NodeKind::ALL.len()],
            present: vec![false; witnesses.len()],
            absent: vec![false; witnesses.len()],
            witnesses,
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
            for (index, witness) in self.witnesses.iter().enumerate() {
                if witness.parent != kind {
                    continue;
                }
                if present(lexed, tree, node, witness.child) {
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
        for (index, witness) in self.witnesses.iter().enumerate() {
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
    use crate::front;

    /// One small program shows what it shows and lacks the rest, named as
    /// the rule writes it.
    #[test]
    fn the_account_names_what_a_program_lacks() {
        let mut coverage = Coverage::new();
        let front = front("fn f(x: int) -> int {\n    if x < 0 { 0 } else { x }\n}\n");
        coverage.record(&front.lexed, front.parse.tree());
        let missing = coverage.missing();
        for shown in [
            "FnItem never has name",
            "FnItem never has 'fn'",
            "FnItem never has ret",
            "IfExpr never has else_branch: Block",
            "BinaryExpr never has Lt",
        ] {
            assert!(!missing.iter().any(|line| line == shown), "{shown}");
        }
        for lacked in [
            "LetStmt never appears",
            "FnItem never lacks ret",
            "FnItem never lacks '->'",
            "IfExpr never has else_branch: IfExpr",
            "IfExpr never lacks 'else'",
            "BinaryExpr never has Add",
            "ParamList never lacks params",
        ] {
            assert!(
                missing.iter().any(|line| line == lacked),
                "{lacked}: {missing:?}"
            );
        }
    }
}
