//! Token classes, bracket pairs, and operator tables.

use std::fmt::{self, Debug};
use std::hash::Hash;

use sumi_lexer::SyntaxKind as T;

pub use sumi_lexer::{Fixed, SyntaxKind};

/// A value a rule reads from a token it holds, or from that token and the one glued after it; it
/// displays as the token reads after "expected".
pub trait TokenField: Copy + Debug + fmt::Display + Eq + Hash + 'static {
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

impl PrefixOp {
    pub const fn token(self) -> Fixed {
        match self {
            Self::Neg => Fixed::Minus,
            Self::Not => Fixed::Bang,
        }
    }
}

/// Per token kind, the prefix operator it is.
const PREFIX_BY_KIND: [Option<PrefixOp>; SyntaxKind::ALL.len()] = {
    let mut table = [None; SyntaxKind::ALL.len()];
    let mut index = 0;
    while index < PrefixOp::ALL.len() {
        let op = PrefixOp::ALL[index];
        table[op.token().kind() as usize] = Some(op);
        index += 1;
    }
    table
};

impl TokenField for PrefixOp {
    const ALL: &[Self] = &[Self::Neg, Self::Not];

    fn read(first: SyntaxKind, _: Option<SyntaxKind>) -> Option<(Self, bool)> {
        PREFIX_BY_KIND[first as usize].map(|op| (op, false))
    }
}

impl fmt::Display for PrefixOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.token().kind().describe())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Literal {
    Int,
    String,
    True,
    False,
}

impl Literal {
    pub const fn token(self) -> SyntaxKind {
        match self {
            Self::Int => T::IntLiteral,
            Self::String => T::StringLiteral,
            Self::True => T::TrueKw,
            Self::False => T::FalseKw,
        }
    }
}

/// Per token kind, the literal it is.
const LITERAL_BY_KIND: [Option<Literal>; SyntaxKind::ALL.len()] = {
    let mut table = [None; SyntaxKind::ALL.len()];
    let mut index = 0;
    while index < Literal::ALL.len() {
        let literal = Literal::ALL[index];
        table[literal.token() as usize] = Some(literal);
        index += 1;
    }
    table
};

impl TokenField for Literal {
    const ALL: &[Self] = &[Self::Int, Self::String, Self::True, Self::False];

    fn read(first: SyntaxKind, _: Option<SyntaxKind>) -> Option<(Self, bool)> {
        LITERAL_BY_KIND[first as usize].map(|literal| (literal, false))
    }
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.token().describe())
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

/// A bracket pair.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Pair {
    Paren,
    Brace,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Side {
    Open,
    Close,
}

impl Pair {
    pub const ALL: [Self; 2] = [Self::Paren, Self::Brace];

    pub fn opener(self) -> Fixed {
        match self {
            Self::Paren => Fixed::LParen,
            Self::Brace => Fixed::LBrace,
        }
    }

    pub fn closer(self) -> Fixed {
        match self {
            Self::Paren => Fixed::RParen,
            Self::Brace => Fixed::RBrace,
        }
    }

    /// Whether a line break inside ends a statement.
    pub fn encloses_statements(self) -> bool {
        match self {
            Self::Paren => false,
            Self::Brace => true,
        }
    }

    pub fn index(self) -> usize {
        self as usize
    }
}

/// The pair `kind` opens or closes.
pub fn bracket(kind: SyntaxKind) -> Option<(Pair, Side)> {
    Some(match kind {
        T::LParen => (Pair::Paren, Side::Open),
        T::RParen => (Pair::Paren, Side::Close),
        T::LBrace => (Pair::Brace, Side::Open),
        T::RBrace => (Pair::Brace, Side::Close),
        _ => return None,
    })
}

pub fn is_opener(kind: SyntaxKind) -> bool {
    matches!(bracket(kind), Some((_, Side::Open)))
}

pub fn is_closer(kind: SyntaxKind) -> bool {
    matches!(bracket(kind), Some((_, Side::Close)))
}

pub fn is_bracket(kind: SyntaxKind) -> bool {
    bracket(kind).is_some()
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
pub enum ArithOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CmpOp {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BinaryOp {
    Or,
    And,
    Cmp(CmpOp),
    Arith(ArithOp),
}

impl TokenField for BinaryOp {
    const ALL: &[Self] = &[
        Self::Or,
        Self::And,
        Self::Cmp(CmpOp::Eq),
        Self::Cmp(CmpOp::Ne),
        Self::Cmp(CmpOp::Lt),
        Self::Cmp(CmpOp::Le),
        Self::Cmp(CmpOp::Gt),
        Self::Cmp(CmpOp::Ge),
        Self::Arith(ArithOp::Add),
        Self::Arith(ArithOp::Sub),
        Self::Arith(ArithOp::Mul),
        Self::Arith(ArithOp::Div),
        Self::Arith(ArithOp::Rem),
    ];

    fn read(first: SyntaxKind, glued: Option<SyntaxKind>) -> Option<(Self, bool)> {
        binary_operator(first, glued).map(|(op, width)| (op, width == 2))
    }
}

impl fmt::Display for BinaryOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (first, glued) = self.tokens();
        write!(f, "`{}{}`", first.text(), glued.map_or("", Fixed::text))
    }
}

/// Per first token kind, the operator spanning a glued token and the one not.
const OPERATORS_BY_FIRST: [[Option<BinaryOp>; 2]; SyntaxKind::ALL.len()] = {
    let mut table = [[None; 2]; SyntaxKind::ALL.len()];
    let mut index = 0;
    while index < BinaryOp::ALL.len() {
        let op = BinaryOp::ALL[index];
        let (first, glued) = op.tokens();
        let slot = &mut table[first.kind() as usize][glued.is_none() as usize];
        assert!(slot.is_none(), "one operator per first token and width");
        *slot = Some(op);
        index += 1;
    }
    table
};

impl BinaryOp {
    /// The operator's first token and the one glued after it.
    pub const fn tokens(self) -> (Fixed, Option<Fixed>) {
        match self {
            Self::Or => (Fixed::Pipe, Some(Fixed::Pipe)),
            Self::And => (Fixed::Amp, Some(Fixed::Amp)),
            Self::Cmp(CmpOp::Eq) => (Fixed::Eq, Some(Fixed::Eq)),
            Self::Cmp(CmpOp::Ne) => (Fixed::Bang, Some(Fixed::Eq)),
            Self::Cmp(CmpOp::Le) => (Fixed::Lt, Some(Fixed::Eq)),
            Self::Cmp(CmpOp::Ge) => (Fixed::Gt, Some(Fixed::Eq)),
            Self::Cmp(CmpOp::Lt) => (Fixed::Lt, None),
            Self::Cmp(CmpOp::Gt) => (Fixed::Gt, None),
            Self::Arith(ArithOp::Add) => (Fixed::Plus, None),
            Self::Arith(ArithOp::Sub) => (Fixed::Minus, None),
            Self::Arith(ArithOp::Mul) => (Fixed::Star, None),
            Self::Arith(ArithOp::Div) => (Fixed::Slash, None),
            Self::Arith(ArithOp::Rem) => (Fixed::Percent, None),
        }
    }

    fn level(self) -> u8 {
        match self {
            Self::Or => 1,
            Self::And => 2,
            Self::Cmp(_) => 3,
            Self::Arith(ArithOp::Add | ArithOp::Sub) => 4,
            Self::Arith(ArithOp::Mul | ArithOp::Div | ArithOp::Rem) => 5,
        }
    }

    /// `(left, right)`. Comparisons associate left like the rest, so a chain parses and is then
    /// rejected.
    pub fn binding_power(self) -> (u8, u8) {
        let right = 2 * self.level();
        (right - 1, right)
    }

    pub fn is_comparison(self) -> bool {
        matches!(self, Self::Cmp(_))
    }
}

/// `glued` is the kind of the token glued after `first`, if any; the `usize` is the operator's
/// width in tokens.
pub fn binary_operator(first: SyntaxKind, glued: Option<SyntaxKind>) -> Option<(BinaryOp, usize)> {
    let [spanning, alone] = OPERATORS_BY_FIRST[first as usize];
    if let Some(op) = spanning
        && let (_, Some(second)) = op.tokens()
        && glued == Some(second.kind())
    {
        return Some((op, 2));
    }
    alone.map(|op| (op, 1))
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
    fn every_operator_reads_back_as_its_tokens() {
        assert_eq!(BinaryOp::ALL.len(), 13);
        for &op in BinaryOp::ALL {
            let (first, glued) = op.tokens();
            let width = 1 + usize::from(glued.is_some());
            assert_eq!(
                binary_operator(first.kind(), glued.map(Fixed::kind)),
                Some((op, width)),
                "{op}"
            );
            assert_eq!(
                BinaryOp::read(first.kind(), glued.map(Fixed::kind)),
                Some((op, width == 2))
            );
        }
        assert_eq!(
            binary_operator(T::Lt, Some(T::Ident)),
            Some((BinaryOp::Cmp(CmpOp::Lt), 1))
        );
        assert_eq!(binary_operator(T::Eq, None), None);
        assert_eq!(BinaryOp::Cmp(CmpOp::Le).to_string(), "`<=`");
        assert_eq!(PrefixOp::Not.to_string(), "`!`");
        assert_eq!(Literal::Int.to_string(), "an integer literal");
        assert_eq!(Literal::True.to_string(), "`true`");
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
