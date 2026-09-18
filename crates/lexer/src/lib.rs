//! Lexical analysis for Sumi.
//!
//! The lexer is total: any `&str` lexes. It is lossless: the tokens
//! partition the source, trivia included. It is line-bounded: no token but
//! a line break spans a line, and an unterminated string ends at its line.
//! It is token-local: every [`LexError`] names its token and a range inside
//! it.

mod generated;
mod index;
mod lex;
mod token;

pub use generated::SyntaxKind;
pub use index::RawIdx;
pub use lex::{
    LexError, LexErrorKind, LexedFile, SourceTooLarge, canonicalize_number_literal, lex,
};
pub use token::TokenFlags;
