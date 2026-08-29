//! Raw lexical analysis for Sumi.
//!
//! The raw lexer is total, lossless, and context-free: any `&str` produces a
//! token stream that exactly partitions the source, retaining whitespace,
//! comments, and malformed input. Raw tokens describe lexical shape only —
//! keyword classification, punctuation gluing, and literal validation happen
//! later, in the token cooker.

mod file;
mod lexer;
mod token;

pub use file::{LexError, LexErrorKind, LexedFile, SourceTooLarge, lex};
pub use token::{RawKind, TokenFlags};
