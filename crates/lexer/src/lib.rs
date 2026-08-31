//! Lexical analysis for Sumi.
//!
//! The lexer is total, lossless, and context-free: any `&str` produces a
//! token stream that exactly partitions the source, retaining whitespace,
//! comments, and malformed input. The scan classifies each token's
//! language-level [`SyntaxKind`] while its bytes are cache-hot — keywords,
//! punctuation roles, int/float — and stores the shape-only [`RawKind`]
//! beside it. Punctuation gluing and literal validation happen later:
//! gluing in the parser, validation in the literal validator, which
//! re-examines only the tokens the scan flagged.

mod file;
mod kind;
mod lexer;
mod token;

pub use file::{LexError, LexErrorKind, LexedFile, SourceTooLarge, lex};
pub use kind::SyntaxKind;
pub use token::{RawKind, TokenFlags};
