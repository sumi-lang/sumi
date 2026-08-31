//! Grammar and validity for Sumi.
//!
//! `sumi-syntax` consumes the classified token stream from `sumi-lexer` and
//! judges it: literal validation, the parser-facing token stream, the flat
//! token-anchored syntax tree, and the parser that builds it. Compound
//! operators are glued by the parser, using token adjacency.

mod input;
mod kind;
mod literal;
mod parser;
mod tree;
mod validate;

pub use input::ParserInput;
pub use kind::{NodeKind, SyntaxKind, starts_expression};
pub use parser::{
    MAX_DEPTH, ParseAnchor, ParseEvidence, ParseExpected, ParseRecovery, ParseRecoveryKind,
    ParseViolation, ParseViolationKind, RawGap, RawTokenRange, parse,
};
pub use tree::{CompletedMarker, Marker, Parse, SyntaxTree, raw_boundary};
pub use validate::{SyntaxError, SyntaxErrorKind, validate};
