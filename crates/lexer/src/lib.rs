//! Lexical analysis for Sumi.
//!
//! The lexer is total, lossless, and context-free above the line: any
//! `&str` produces a token stream that exactly partitions the source,
//! retaining whitespace, comments, and malformed input, and no state
//! crosses a line break but the inside of a `"""` literal. The scan
//! classifies each token's language-level [`SyntaxKind`] while its bytes
//! are cache-hot — keywords, punctuation roles, int/float — and stores the
//! shape-only [`RawKind`] beside it. Token-local validity is established
//! before [`lex`] returns by selectively re-examining malformed numbers,
//! escaped literals, character literals, the layout of multi-line
//! literals, and roleless punctuation. Punctuation gluing happens later in
//! the parser.
//!
//! Every literal but the multi-line forms is bounded by its line: an
//! unterminated `"…"`, `r"…"`, or `'…'` ends at the line break, so a stray
//! delimiter costs its line and never the file. A hole in a string
//! literal, `{expr}`, is the one place the scan keeps state between tokens
//! — the literal to resume, and the braces open in the hole's code — and
//! a hole ends with its line too: one left open there is an error, and the
//! `"…"` literal around it ends with the line as an unterminated one does,
//! while a `"""` literal takes the break as its text.

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
