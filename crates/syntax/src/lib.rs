//! Grammar and validity for Sumi.
//!
//! `sumi-syntax` consumes the classified, validated token stream from
//! `sumi-lexer` and builds the parser-facing token stream, flat token-anchored
//! syntax tree, and parse evidence. Compound operators are glued by the
//! parser, using token adjacency.

mod input;
mod kind;
mod parser;
mod tree;

pub use input::ParserInput;
pub use kind::{NodeKind, SyntaxKind, starts_expression};
pub use parser::{
    MAX_DEPTH, ParseAnchor, ParseEvidence, ParseExpected, ParseRecovery, ParseRecoveryKind,
    ParseViolation, ParseViolationKind, RawGap, RawTokenRange, parse,
};
pub use tree::{CompletedMarker, Marker, Parse, SyntaxTree, raw_boundary};
