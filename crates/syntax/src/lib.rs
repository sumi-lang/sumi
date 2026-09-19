//! Grammar and validity for Sumi.
//!
//! `sumi-syntax` consumes the classified, validated token stream from
//! `sumi-lexer` and builds the parser-facing token stream, flat token-anchored
//! syntax tree, and parse evidence. Compound operators are glued by the
//! parser, using token adjacency. The node vocabulary and the typed views
//! are declared once in `ast`; the token classes, bracket pairs, and
//! operator tables in `grammar`.

pub mod ast;
mod grammar;
mod index;
mod input;
mod parser;
mod tree;

pub use ast::NodeKind;
pub use grammar::{
    BRACKET_PAIRS, BinaryOp, SyntaxKind, binary_operator, is_bracket, is_closer, is_opener,
};
pub use index::{NodeIdx, SigIdx};
pub use input::ParserInput;
pub use parser::{
    MAX_DEPTH, ParseAnchor, ParseEvidence, ParseRecovery, ParseRecoveryKind, ParseViolation,
    ParseViolationKind, RawGap, RawTokenRange, parse,
};
pub use sumi_lexer::RawIdx;
pub use tree::{Parse, SyntaxTree};
