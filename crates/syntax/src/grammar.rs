//! Token classes, bracket pairs, and operator tables.

use std::fmt::Debug;
use std::hash::Hash;

use sumi_lexer::SyntaxKind as T;

pub use sumi_lexer::SyntaxKind;

/// A value a rule reads from a token it holds, or from that token and the one glued after it.
pub trait TokenField: Copy + Debug + Eq + Hash + 'static {
    const ALL: &[Self];

    /// The value at `first`, and whether it spans `glued`, the token joint after `first` inside
    /// the same node.
    fn read(first: SyntaxKind, glued: Option<SyntaxKind>) -> Option<(Self, bool)>;
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum PrefixOp {
    Neg,
    Not,
}

impl TokenField for PrefixOp {
    const ALL: &[Self] = &[Self::Neg, Self::Not];

    fn read(first: SyntaxKind, _: Option<SyntaxKind>) -> Option<(Self, bool)> {
        let op = match first {
            T::Minus => Self::Neg,
            T::Bang => Self::Not,
            _ => return None,
        };
        Some((op, false))
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Literal {
    Int,
    String,
    True,
    False,
}

impl TokenField for Literal {
    const ALL: &[Self] = &[Self::Int, Self::String, Self::True, Self::False];

    fn read(first: SyntaxKind, _: Option<SyntaxKind>) -> Option<(Self, bool)> {
        let literal = match first {
            T::IntLiteral => Self::Int,
            T::StringLiteral => Self::String,
            T::TrueKw => Self::True,
            T::FalseKw => Self::False,
            _ => return None,
        };
        Some((literal, false))
    }
}

pub fn starts_expression(kind: SyntaxKind) -> bool {
    is_literal(kind)
        || is_prefix_operator(kind)
        || matches!(kind, T::Ident | T::FnKw | T::IfKw | T::LParen | T::LBrace)
}

/// Statement starters that are not expression starters.
pub fn introduces_statement(kind: SyntaxKind) -> bool {
    matches!(kind, T::LetKw | T::ReturnKw | T::Underscore | T::Error)
}

pub fn starts_statement(kind: SyntaxKind) -> bool {
    introduces_statement(kind) || starts_expression(kind)
}

pub fn can_end_statement(kind: SyntaxKind) -> bool {
    is_literal(kind)
        || matches!(
            kind,
            T::Ident | T::ReturnKw | T::Underscore | T::RParen | T::RBrace | T::Error
        )
}

pub fn starts_item(kind: SyntaxKind) -> bool {
    kind == T::FnKw
}

/// A glued prefix operator opens an operand, so it continues nothing.
pub fn continues_statement(kind: SyntaxKind, glued: Option<SyntaxKind>) -> bool {
    kind == T::ElseKw
        || match binary_operator(kind, glued) {
            Some((_, 2)) => true,
            Some(_) => glued.is_none() || !is_prefix_operator(kind),
            None => false,
        }
}

pub const BRACKET_PAIRS: [(SyntaxKind, SyntaxKind); 2] =
    [(T::LParen, T::RParen), (T::LBrace, T::RBrace)];

/// The index in [`BRACKET_PAIRS`] of the pair `kind` opens or closes.
pub fn pair_index(kind: SyntaxKind) -> Option<usize> {
    Some(match kind {
        T::LParen | T::RParen => 0,
        T::LBrace | T::RBrace => 1,
        _ => return None,
    })
}

pub fn closer(opener: SyntaxKind) -> Option<SyntaxKind> {
    Some(match opener {
        T::LParen => T::RParen,
        T::LBrace => T::RBrace,
        _ => return None,
    })
}

pub fn opener(closer: SyntaxKind) -> Option<SyntaxKind> {
    Some(match closer {
        T::RParen => T::LParen,
        T::RBrace => T::LBrace,
        _ => return None,
    })
}

pub fn is_opener(kind: SyntaxKind) -> bool {
    closer(kind).is_some()
}

pub fn is_closer(kind: SyntaxKind) -> bool {
    opener(kind).is_some()
}

pub fn is_bracket(kind: SyntaxKind) -> bool {
    is_opener(kind) || is_closer(kind)
}

pub fn encloses_statements(opener: SyntaxKind) -> bool {
    opener == T::LBrace
}

pub fn is_prefix_operator(kind: SyntaxKind) -> bool {
    PrefixOp::read(kind, None).is_some()
}

pub fn is_literal(kind: SyntaxKind) -> bool {
    Literal::read(kind, None).is_some()
}

/// A binding power above every binary operator's.
pub const PREFIX_BP: u8 = 11;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BinaryOp {
    Or,
    And,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    Add,
    Sub,
    Mul,
    Div,
    Rem,
}

impl TokenField for BinaryOp {
    const ALL: &[Self] = &[
        Self::Or,
        Self::And,
        Self::Eq,
        Self::Ne,
        Self::Lt,
        Self::Le,
        Self::Gt,
        Self::Ge,
        Self::Add,
        Self::Sub,
        Self::Mul,
        Self::Div,
        Self::Rem,
    ];

    fn read(first: SyntaxKind, glued: Option<SyntaxKind>) -> Option<(Self, bool)> {
        binary_operator(first, glued).map(|(op, width)| (op, width == 2))
    }
}

impl BinaryOp {
    fn level(self) -> u8 {
        match self {
            Self::Or => 1,
            Self::And => 2,
            Self::Eq | Self::Ne | Self::Lt | Self::Le | Self::Gt | Self::Ge => 3,
            Self::Add | Self::Sub => 4,
            Self::Mul | Self::Div | Self::Rem => 5,
        }
    }

    /// `(left, right)`. Comparisons associate left like the rest, so a chain parses and is then
    /// rejected.
    pub fn binding_power(self) -> (u8, u8) {
        let right = 2 * self.level();
        (right - 1, right)
    }

    pub fn is_comparison(self) -> bool {
        matches!(
            self,
            Self::Eq | Self::Ne | Self::Lt | Self::Le | Self::Gt | Self::Ge
        )
    }
}

/// `glued` is the kind of the token glued after `first`, if any; the `usize` is the operator's
/// width in tokens.
pub fn binary_operator(first: SyntaxKind, glued: Option<SyntaxKind>) -> Option<(BinaryOp, usize)> {
    Some(match first {
        T::Pipe if glued == Some(T::Pipe) => (BinaryOp::Or, 2),
        T::Amp if glued == Some(T::Amp) => (BinaryOp::And, 2),
        T::Eq if glued == Some(T::Eq) => (BinaryOp::Eq, 2),
        T::Bang if glued == Some(T::Eq) => (BinaryOp::Ne, 2),
        T::Lt if glued == Some(T::Eq) => (BinaryOp::Le, 2),
        T::Gt if glued == Some(T::Eq) => (BinaryOp::Ge, 2),
        T::Lt => (BinaryOp::Lt, 1),
        T::Gt => (BinaryOp::Gt, 1),
        T::Plus => (BinaryOp::Add, 1),
        T::Minus => (BinaryOp::Sub, 1),
        T::Star => (BinaryOp::Mul, 1),
        T::Slash => (BinaryOp::Div, 1),
        T::Percent => (BinaryOp::Rem, 1),
        _ => return None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn prefix_binds_tightest() {
        let tightest = BinaryOp::ALL
            .iter()
            .map(|op| op.binding_power().1)
            .max()
            .unwrap();
        assert_eq!(PREFIX_BP, tightest + 1);
    }

    #[test]
    fn operators_continue_statements() {
        assert!(continues_statement(T::Plus, Some(T::Ident)));
        assert!(continues_statement(T::Minus, None));
        assert!(!continues_statement(T::Minus, Some(T::Ident)));
        assert!(continues_statement(T::Bang, Some(T::Eq)));
        assert!(!continues_statement(T::Bang, Some(T::Ident)));
        assert!(continues_statement(T::Pipe, Some(T::Pipe)));
        assert!(!continues_statement(T::Pipe, None));
        assert!(!continues_statement(T::Eq, None));
        assert!(continues_statement(T::ElseKw, None));
        assert!(!continues_statement(T::Ident, None));
    }
}
