//! Lexical analysis for Sumi.
//!
//! The lexer is total, lossless, and context-free: any `&str` produces a
//! token stream that exactly partitions the source, retaining whitespace,
//! comments, and malformed input. The scan classifies each token's
//! language-level [`SyntaxKind`] while its bytes are cache-hot — keywords,
//! punctuation roles, int/float — and stores the shape-only [`RawKind`]
//! beside it. Token-local validity is established before [`lex`] returns by
//! selectively re-examining malformed numbers, escaped literals, character
//! literals, and roleless punctuation. Punctuation gluing happens later in
//! the parser.

mod file;
mod generated;
mod index;
mod lexer;
mod literal;
mod token;

pub use file::{LexError, LexErrorKind, LexedFile, SourceTooLarge, lex};
pub use generated::SyntaxKind;
pub use index::RawIdx;
pub use literal::canonicalize_number_literal;
pub use token::{RawKind, TokenFlags};
