//! Lexical analysis for Sumi: total (any `&str` lexes) and lossless (the tokens partition the
//! source, trivia included). No token but `Newline` contains a line break.

mod index;
mod kind;
mod lex;
mod token;

pub use index::RawIdx;
pub use kind::{Fixed, SyntaxKind};
pub use lex::{
    LexError, LexErrorKind, LexedFile, SourceTooLarge, canonicalize_number_literal, lex,
};
pub use token::TokenFlags;
