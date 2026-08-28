//! Language-level token classification for Jolt.
//!
//! `jolt-syntax` consumes the raw, shape-only token stream from `jolt-lexer`
//! and assigns language meaning: cooked [`SyntaxKind`]s, keyword
//! classification, and literal validation now; the lossless CST as the
//! language grows. Cooking is strictly 1:1 with raw tokens — compound
//! operators are glued later, by the parser, using token adjacency.

mod cook;
mod kind;
mod literal;

pub use cook::{CookedFile, SyntaxError, SyntaxErrorKind, cook};
pub use kind::SyntaxKind;
