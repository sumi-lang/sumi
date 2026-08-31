/// The language-level kind of a token, assigned by the fused lexer and
/// re-exported here where the grammar consumes it.
///
/// Kept separate from the tree's [`NodeKind`] above it: nodes cover ranges
/// of tokens rather than sitting among them, so the two vocabularies never
/// share a slot.
pub use sumi_lexer::SyntaxKind;

/// Whether a token of this kind can begin an expression.
///
/// A free function rather than a method: the kind is defined where the
/// lexer assigns it, but what begins an expression is grammar, and grammar
/// lives here.
pub fn starts_expression(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::Ident
            | SyntaxKind::IntLiteral
            | SyntaxKind::FloatLiteral
            | SyntaxKind::StringLiteral
            | SyntaxKind::RawStringLiteral
            | SyntaxKind::CharLiteral
            | SyntaxKind::TrueKw
            | SyntaxKind::FalseKw
            | SyntaxKind::Minus
            | SyntaxKind::Bang
            | SyntaxKind::LParen
            | SyntaxKind::LBrace
            | SyntaxKind::IfKw
    )
}

/// Whether a token of this kind can begin a statement: what the parser
/// takes at statement position, an `Error` run included.
pub(crate) fn starts_statement(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::LetKw | SyntaxKind::Underscore | SyntaxKind::ReturnKw | SyntaxKind::Error
    ) || starts_expression(kind)
}

/// The kind of a syntax tree node.
///
/// A node is structure only, so this vocabulary is disjoint from
/// [`SyntaxKind`]: a tree slot never holds a token kind, and a
/// token buffer slot never holds a node kind.
#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum NodeKind {
    SourceFile,
    FnItem,
    ParamList,
    Param,
    Block,
    LetStmt,
    DiscardStmt,
    ReturnStmt,
    NameExpr,
    LiteralExpr,
    PrefixExpr,
    BinaryExpr,
    ParenExpr,
    CallExpr,
    ArgList,
    IfExpr,
    /// Covers tokens the parser could not parse.
    Error,
}
