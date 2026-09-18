//! Grammar coverage: whether a body of trees reaches every node kind and
//! every child the grammar allows a node. The witnesses are the children
//! each view declares, read from [`NodeKind::children`], then [`RULES`],
//! what the rules say beyond the accessors, and one per operator of
//! [`BinaryOp::ALL`]: 80 in all today. Only a node without an error
//! counts, since one with an error may lack any child, and its lacking one
//! then says nothing about what the grammar allows.

use sumi_lexer::{LexedFile, RawIdx};
use sumi_syntax::{BinaryOp, NodeIdx, NodeKind, SyntaxKind, SyntaxTree, binary_operator};

use NodeKind as N;
use SyntaxKind as T;

/// One child a node rule allows beyond what its view declares.
#[derive(Clone, Copy, Debug)]
pub enum Child {
    /// A glued run of tokens of these kinds among the node's own.
    Tokens(&'static [SyntaxKind]),
    /// The single child of this kind in the named field: one member of the
    /// alternation the field admits.
    Member(&'static str, NodeKind),
}

/// What each rule allows beyond what its view declares: the tokens a node
/// holds itself, in the rule's order, and each member of an alternation a
/// field admits. `true` marks a child the rule lets a node lack; a member
/// is always lackable, since the field holds one member at a time, even
/// where the field itself is required. The operators of a binary
/// expression are not listed: [`witnesses`] takes them from
/// [`BinaryOp::ALL`].
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
    (N::ParenExpr, false, Child::Tokens(&[T::LParen])),
    (N::ParenExpr, false, Child::Tokens(&[T::RParen])),
    (N::ArgList, false, Child::Tokens(&[T::LParen])),
    (N::ArgList, true, Child::Tokens(&[T::Comma])),
    (N::ArgList, false, Child::Tokens(&[T::RParen])),
    (N::IfExpr, false, Child::Tokens(&[T::IfKw])),
    (N::IfExpr, true, Child::Tokens(&[T::ElseKw])),
    (N::IfExpr, true, Child::Member("else_branch", N::IfExpr)),
    (N::IfExpr, true, Child::Member("else_branch", N::Block)),
    (N::ClosureExpr, false, Child::Tokens(&[T::FnKw])),
    (N::ClosureExpr, true, Child::Tokens(&[T::Minus, T::Gt])),
    (N::ClosureExpr, true, Child::Tokens(&[T::Eq])),
];

/// How to tell whether a node has a child.
#[derive(Clone, Copy)]
enum Check {
    /// As the view's accessor answers: absent when the slot holds a node
    /// of another kind than the view declares.
    Declared(fn(&SyntaxTree, NodeIdx) -> bool),
    /// The single child in this field slot is of this kind.
    Member(u8, NodeKind),
    /// A glued run of tokens of these kinds is among the node's own.
    Tokens(&'static [SyntaxKind]),
    /// A binary operator is among the node's own tokens.
    Operator(BinaryOp),
}

/// One child a node rule allows, as the account keeps it.
struct Witness {
    parent: NodeKind,
    /// The child as the rule writes it.
    name: String,
    /// Whether the rule lets a node lack the child.
    optional: bool,
    check: Check,
}

/// Every witness, by parent kind in grammar order: the children each
/// view declares, then [`RULES`], then the operators of a binary
/// expression.
fn witnesses() -> Vec<Witness> {
    let declared = NodeKind::ALL.iter().flat_map(|&parent| {
        parent.children().iter().map(move |child| Witness {
            parent,
            name: child.name.to_owned(),
            optional: child.optional,
            check: Check::Declared(child.present),
        })
    });
    let ruled = RULES.iter().map(|&(parent, optional, child)| {
        let (name, check) = match child {
            Child::Tokens(kinds) => {
                let name = match kinds
                    .iter()
                    .map(|kind| kind.text())
                    .collect::<Option<Vec<_>>>()
                {
                    Some(text) => format!("'{}'", text.concat()),
                    None => format!("{kinds:?}"),
                };
                (name, Check::Tokens(kinds))
            }
            Child::Member(field, kind) => {
                let slot = parent
                    .children()
                    .iter()
                    .find(|child| child.name == field)
                    .and_then(|child| child.slot)
                    .unwrap_or_else(|| panic!("{parent:?} declares no single field {field}"));
                (format!("{field}: {kind:?}"), Check::Member(slot, kind))
            }
        };
        Witness {
            parent,
            name,
            optional,
            check,
        }
    });
    let operators = BinaryOp::ALL.iter().map(|&op| Witness {
        parent: N::BinaryExpr,
        name: format!("{op:?}"),
        optional: true,
        check: Check::Operator(op),
    });
    let mut witnesses: Vec<Witness> = declared.chain(ruled).chain(operators).collect();
    witnesses.sort_by_key(|witness| witness.parent as u8);
    witnesses
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
fn present(lexed: &LexedFile, tree: &SyntaxTree, node: NodeIdx, check: Check) -> bool {
    match check {
        Check::Declared(present) => present(tree, node),
        Check::Member(slot, kind) => tree
            .child_in_field(node, slot)
            .is_some_and(|child| tree.kind(child) == kind),
        Check::Tokens(kinds) => has_tokens(lexed, tree, node, kinds),
        Check::Operator(op) => has_operator(lexed, tree, node, op),
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
                if present(lexed, tree, node, witness.check) {
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

    /// The witnesses are grouped by parent in grammar order, an
    /// alternation's members resolve to the field's slot, and every
    /// operator has a row.
    #[test]
    fn the_witnesses_follow_the_grammar() {
        let witnesses = witnesses();
        assert_eq!(witnesses.len(), 80);
        assert!(
            witnesses
                .windows(2)
                .all(|pair| pair[0].parent as u8 <= pair[1].parent as u8)
        );
        let else_branch = NodeKind::IfExpr
            .children()
            .iter()
            .find(|child| child.name == "else_branch")
            .and_then(|child| child.slot);
        let members: Vec<_> = witnesses
            .iter()
            .filter_map(|witness| match witness.check {
                Check::Member(slot, kind) => Some((witness.parent, slot, kind)),
                _ => None,
            })
            .collect();
        assert_eq!(
            members,
            [
                (N::IfExpr, else_branch.unwrap(), N::IfExpr),
                (N::IfExpr, else_branch.unwrap(), N::Block),
            ]
        );
        let operators = witnesses
            .iter()
            .filter(|witness| matches!(witness.check, Check::Operator(_)))
            .count();
        assert_eq!(operators, BinaryOp::ALL.len());
    }

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
