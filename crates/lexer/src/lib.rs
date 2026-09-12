//! Lexical analysis for Sumi.
//!
//! The lexer is total, lossless, and context-free above the line: any
//! `&str` produces a token stream that exactly partitions the source,
//! retaining whitespace, comments, and malformed input, and no state
//! crosses a line break. The scan classifies each token's language-level
//! [`SyntaxKind`] while its bytes are cache-hot — keywords and punctuation
//! roles — and stores the shape-only [`RawKind`] beside it. Token-local
//! validity is established before [`lex`] returns by selectively
//! re-examining malformed numbers, escaped literals, and roleless
//! punctuation. Punctuation gluing happens later in
//! the parser.
//!
//! Every literal is bounded by its line: an unterminated `"…"` ends at the
//! line break, so a stray delimiter costs its line and never the file, and
//! the scan keeps no state between tokens.

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
