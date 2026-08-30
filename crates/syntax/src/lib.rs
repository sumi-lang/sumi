//! Language-level token classification for Sumi.
//!
//! `sumi-syntax` consumes the raw, shape-only token stream from `sumi-lexer`
//! and assigns language meaning: cooked [`SyntaxKind`]s, keyword
//! classification, literal validation, the parser-facing token stream, the
//! flat token-anchored syntax tree, and the parser that builds it. Cooking is
//! strictly 1:1 with raw tokens — compound operators are glued later, by the
//! parser, using token adjacency.

mod cook;
mod input;
mod kind;
mod literal;
mod parser;
mod tree;

pub use cook::{CookedFile, SyntaxError, SyntaxErrorKind, cook};
pub use input::ParserInput;
pub use kind::{NodeKind, SyntaxKind};
pub use parser::{
    MAX_DEPTH, ParseAnchor, ParseEvidence, ParseExpected, ParseRecovery, ParseRecoveryKind,
    ParseViolation, ParseViolationKind, RawGap, RawTokenRange, parse,
};
pub use tree::{CompletedMarker, Marker, Parse, SyntaxTree};
