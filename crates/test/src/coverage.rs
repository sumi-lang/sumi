//! Grammar coverage: whether a body of trees reaches every node kind and child the grammar allows.
//! Only a node without an error counts; an erroring node may lack any child.

use sumi_lexer::LexedFile;
use sumi_syntax::ast::TokenRule;
use sumi_syntax::{NodeIdx, NodeKind, SyntaxKind, SyntaxTree};

use NodeKind as N;

/// The members of an alternation a field admits that the corpus must each reach, as `(parent,
/// field, member)`.
pub const MEMBERS: &[(NodeKind, &str, NodeKind)] = &[
    (N::IfExpr, "else_branch", N::IfExpr),
    (N::IfExpr, "else_branch", N::Block),
];

#[derive(Clone, Copy)]
enum Check {
    Declared(fn(&SyntaxTree, NodeIdx) -> bool),
    Member(u8, NodeKind),
    Tokens(SyntaxKind, Option<SyntaxKind>),
    Variant(fn(&SyntaxTree, &LexedFile, NodeIdx, usize) -> bool, usize),
}

struct Witness {
    parent: NodeKind,
    name: String,
    optional: bool,
    check: Check,
}

fn witnesses() -> Vec<Witness> {
    let declared = NodeKind::ALL.iter().flat_map(|&parent| {
        parent.children().iter().map(move |child| Witness {
            parent,
            name: child.name.to_owned(),
            optional: child.optional,
            check: Check::Declared(child.present),
        })
    });
    // A read value's witnesses are its variants, each optional: the node reads one of them.
    let held = NodeKind::ALL.iter().flat_map(|&parent| {
        parent
            .tokens()
            .iter()
            .flat_map(move |rule| -> Vec<Witness> {
                match *rule {
                    TokenRule::Kind {
                        first,
                        glued,
                        optional,
                    } => vec![Witness {
                        parent,
                        name: rule.to_string(),
                        optional,
                        check: Check::Tokens(first, glued),
                    }],
                    TokenRule::Flag { kind, .. } => vec![Witness {
                        parent,
                        name: rule.to_string(),
                        optional: true,
                        check: Check::Tokens(kind, None),
                    }],
                    TokenRule::Field {
                        variants,
                        variant,
                        present,
                        ..
                    } => (0..variants)
                        .map(|index| Witness {
                            parent,
                            name: variant(index),
                            optional: true,
                            check: Check::Variant(present, index),
                        })
                        .collect(),
                }
            })
    });
    let members = MEMBERS.iter().map(|&(parent, field, kind)| {
        let slot = parent
            .children()
            .iter()
            .find(|child| child.name == field)
            .and_then(|child| child.slot)
            .unwrap_or_else(|| panic!("{parent:?} declares no single field {field}"));
        Witness {
            parent,
            name: format!("{field}: {kind:?}"),
            optional: true,
            check: Check::Member(slot, kind),
        }
    });
    let mut witnesses: Vec<Witness> = declared.chain(held).chain(members).collect();
    witnesses.sort_by_key(|witness| witness.parent as u8);
    witnesses
}

fn present(lexed: &LexedFile, tree: &SyntaxTree, node: NodeIdx, check: Check) -> bool {
    match check {
        Check::Declared(present) => present(tree, node),
        Check::Member(slot, kind) => tree
            .child_in_field(node, slot)
            .is_some_and(|child| tree.kind(child) == kind),
        Check::Tokens(first, glued) => tree.holds(node, lexed, first, glued),
        Check::Variant(present, index) => present(tree, lexed, node, index),
    }
}

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

    /// `lexed` must be the file `tree` was parsed from.
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

    /// One line per gap: a kind that never appears, a child never present, or an optional child
    /// never absent.
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
    use sumi_syntax::{BinaryOp, TokenField};

    use super::*;
    use crate::front;

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
            .filter(|witness| {
                witness.parent == N::BinaryExpr && matches!(witness.check, Check::Variant(..))
            })
            .count();
        assert_eq!(operators, <BinaryOp as TokenField>::ALL.len());
    }

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
            "BinaryExpr never has `<`",
        ] {
            assert!(!missing.iter().any(|line| line == shown), "{shown}");
        }
        for lacked in [
            "LetStmt never appears",
            "FnItem never lacks ret",
            "FnItem never lacks '->'",
            "IfExpr never has else_branch: IfExpr",
            "IfExpr never lacks 'else'",
            "BinaryExpr never has `+`",
            "ParamList never lacks params",
        ] {
            assert!(
                missing.iter().any(|line| line == lacked),
                "{lacked}: {missing:?}"
            );
        }
    }
}
