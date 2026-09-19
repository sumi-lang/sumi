//! The grammar's token side: the classes the newline rule and the parser
//! sort tokens into, the bracket pairs the token stream matches, and the
//! operator tables.

use sumi_lexer::SyntaxKind as T;

/// The language-level kind of a token, assigned by the fused lexer and
/// re-exported here where the grammar consumes it.
///
/// Kept separate from the tree's [`NodeKind`](crate::NodeKind): nodes
/// cover ranges of tokens rather than sitting among them, so the two
/// vocabularies never share a slot.
pub use sumi_lexer::SyntaxKind;

/// Whether a token of this kind can begin an expression: a value, an
/// opener, a prefix operator, or a keyword that begins one.
pub fn starts_expression(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        T::Ident
            | T::IntLiteral
            | T::StringLiteral
            | T::TrueKw
            | T::FalseKw
            | T::FnKw
            | T::IfKw
            | T::LParen
            | T::LBrace
            | T::Minus
            | T::Bang
    )
}

/// Whether a token of this kind begins a statement that is not an
/// expression: a declaration keyword, `_`, or an `Error` run.
pub fn introduces_statement(kind: SyntaxKind) -> bool {
    matches!(kind, T::LetKw | T::ReturnKw | T::Underscore | T::Error)
}

/// Whether a token of this kind can begin a statement.
pub fn starts_statement(kind: SyntaxKind) -> bool {
    introduces_statement(kind) || starts_expression(kind)
}

/// Whether a statement can end after a token of this kind: values and
/// closers can; operators, openers, and introducer keywords need more.
pub fn can_end_statement(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        T::Ident
            | T::IntLiteral
            | T::StringLiteral
            | T::TrueKw
            | T::FalseKw
            | T::ReturnKw
            | T::Underscore
            | T::RParen
            | T::RBrace
            | T::Error
    )
}

/// Whether a token of this kind begins a top-level item.
pub fn starts_item(kind: SyntaxKind) -> bool {
    kind == T::FnKw
}

/// Whether a token of this kind continues a statement left open on the
/// previous line; `glued` is the kind of the token glued after it, if
/// any.
///
/// Continuation tokens can never start a statement: `else`, and the
/// binary operators — a compound one only when glued into shape, and one
/// that is also a prefix operator only when spaced from what follows,
/// since glued it opens an operand instead.
pub fn continues_statement(kind: SyntaxKind, glued: Option<SyntaxKind>) -> bool {
    kind == T::ElseKw
        || match binary_operator(kind, glued) {
            Some((_, 2)) => true,
            Some(_) => glued.is_none() || !is_prefix_operator(kind),
            None => false,
        }
}

/// The bracket pairs the token stream matches, opener then closer.
pub const BRACKET_PAIRS: [(SyntaxKind, SyntaxKind); 2] =
    [(T::LParen, T::RParen), (T::LBrace, T::RBrace)];

/// The index in [`BRACKET_PAIRS`] of the pair a token of this kind opens
/// or closes.
pub fn pair_index(kind: SyntaxKind) -> Option<usize> {
    Some(match kind {
        T::LParen | T::RParen => 0,
        T::LBrace | T::RBrace => 1,
        _ => return None,
    })
}

/// The closer pairing with an opener of this kind.
pub fn closer(opener: SyntaxKind) -> Option<SyntaxKind> {
    Some(match opener {
        T::LParen => T::RParen,
        T::LBrace => T::RBrace,
        _ => return None,
    })
}

/// The opener pairing with a closer of this kind.
pub fn opener(closer: SyntaxKind) -> Option<SyntaxKind> {
    Some(match closer {
        T::RParen => T::LParen,
        T::RBrace => T::LBrace,
        _ => return None,
    })
}

/// Whether a token of this kind opens a bracket pair.
pub fn is_opener(kind: SyntaxKind) -> bool {
    closer(kind).is_some()
}

/// Whether a token of this kind closes a bracket pair.
pub fn is_closer(kind: SyntaxKind) -> bool {
    opener(kind).is_some()
}

/// Whether a token of this kind opens or closes a bracket pair.
pub fn is_bracket(kind: SyntaxKind) -> bool {
    is_opener(kind) || is_closer(kind)
}

/// Whether the pair opened by this kind encloses statements, so that line
/// breaks inside it end statements as a block's do. Every other pair
/// suspends the newline rule between its brackets.
pub fn encloses_statements(opener: SyntaxKind) -> bool {
    opener == T::LBrace
}

/// Whether a token of this kind is a prefix operator.
pub fn is_prefix_operator(kind: SyntaxKind) -> bool {
    matches!(kind, T::Minus | T::Bang)
}

/// The binding power of a prefix operator's operand: tighter than every
/// binary operator, so only a call binds closer.
pub const PREFIX_BP: u8 = 11;

/// A binary operator.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BinaryOp {
    /// `||`
    Or,
    /// `&&`
    And,
    /// `==`
    Eq,
    /// `!=`
    Ne,
    /// `<`
    Lt,
    /// `<=`
    Le,
    /// `>`
    Gt,
    /// `>=`
    Ge,
    /// `+`
    Add,
    /// `-`
    Sub,
    /// `*`
    Mul,
    /// `/`
    Div,
    /// `%`
    Rem,
}

impl BinaryOp {
    /// Every operator, in the order of [`binary_operator`]'s table.
    pub const ALL: &[Self] = &[
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

    /// The precedence level: higher binds tighter.
    fn level(self) -> u8 {
        match self {
            Self::Or => 1,
            Self::And => 2,
            Self::Eq | Self::Ne | Self::Lt | Self::Le | Self::Gt | Self::Ge => 3,
            Self::Add | Self::Sub => 4,
            Self::Mul | Self::Div | Self::Rem => 5,
        }
    }

    /// Left and right binding powers. Every operator associates left, so
    /// it binds tighter on the right; comparisons too, so a chain parses
    /// left to right and is then rejected.
    pub fn binding_power(self) -> (u8, u8) {
        let right = 2 * self.level();
        (right - 1, right)
    }

    /// Whether the operator is a comparison, which does not chain.
    pub fn is_comparison(self) -> bool {
        matches!(
            self,
            Self::Eq | Self::Ne | Self::Lt | Self::Le | Self::Gt | Self::Ge
        )
    }
}

/// The binary operator a token of kind `first` begins, and its width in
/// tokens; `glued` is the kind of the token glued after it, if any. A
/// compound operator is its tokens glued; a lone `=` is no operator.
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

    /// The prefix binding power is above every binary operator's.
    #[test]
    fn prefix_binds_tightest() {
        let tightest = BinaryOp::ALL
            .iter()
            .map(|op| op.binding_power().1)
            .max()
            .unwrap();
        assert_eq!(PREFIX_BP, tightest + 1);
    }

    /// A binary operator continues a line unless, being a prefix operator
    /// too, it is glued to an operand; a compound only when glued into
    /// shape.
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
