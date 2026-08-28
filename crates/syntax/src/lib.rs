//! Language-level token classification for Jolt.
//!
//! `jolt-syntax` consumes the raw, shape-only token stream from `jolt-lexer`
//! and assigns language meaning: cooked [`SyntaxKind`]s now; keyword
//! classification, literal validation, and the lossless CST as the language
//! grows. Cooking is strictly 1:1 with raw tokens — compound operators are
//! glued later, by the parser, using token adjacency.

mod cook;
mod kind;

pub use cook::{CookedFile, cook};
pub use kind::SyntaxKind;
