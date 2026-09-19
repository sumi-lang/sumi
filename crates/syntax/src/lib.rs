//! Grammar and validity for Sumi.
//!
//! `sumi-syntax` consumes the classified, validated token stream from
//! `sumi-lexer` and builds the parser-facing token stream, flat token-anchored
//! syntax tree, and parse evidence. Compound operators are glued by the
//! parser, using token adjacency. The vocabulary — node kinds, token
//! classes, bracket pairs, and operator tables — is generated from
//! `sumi.grammar` at the workspace root.

mod generated;
mod index;
mod input;
mod parser;
mod tree;

pub use generated::ast;
pub use generated::{
    BRACKET_PAIRS, BinaryOp, NodeKind, SyntaxKind, binary_operator, is_bracket, is_closer,
    is_opener,
};
pub use index::{NodeIdx, SigIdx};
pub use input::ParserInput;
pub use parser::{
    MAX_DEPTH, ParseAnchor, ParseEvidence, ParseRecovery, ParseRecoveryKind, ParseViolation,
    ParseViolationKind, RawGap, RawTokenRange, parse,
};
pub use sumi_lexer::RawIdx;
pub use tree::{Parse, SyntaxTree};
