//! The parser and flat syntax tree for Sumi. Compound operators are glued from adjacent tokens by
//! the parser, not the lexer.

pub mod ast;
mod grammar;
mod index;
mod input;
mod parser;
mod tree;

pub use ast::NodeKind;
pub use grammar::{
    ArithOp, BRACKET_PAIRS, BinaryOp, CmpOp, Literal, PrefixOp, SyntaxKind, TokenField,
    binary_operator, is_bracket, is_closer, is_opener,
};
pub use index::{NodeIdx, SigIdx};
pub use input::ParserInput;
pub use parser::{
    MAX_DEPTH, ParseAnchor, ParseEvidence, ParseRecovery, ParseRecoveryKind, ParseViolation,
    ParseViolationKind, RawGap, RawTokenRange, parse,
};
pub use sumi_lexer::RawIdx;
pub use tree::{Parse, SyntaxTree};
