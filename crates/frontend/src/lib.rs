//! The source-owning syntactic frontend for Sumi. Detection stays in the lexer and parser; this
//! crate turns that evidence into diagnostics.

pub mod codes;
mod diagnostic;
mod lower;
pub use lower::diagnostics;

pub use diagnostic::{Diagnostic, DiagnosticCode, DiagnosticGroup, Fix, Label};
pub use sumi_lexer::SourceTooLarge;
use sumi_lexer::{LexedFile, lex};
use sumi_syntax::{Parse, ParserInput, parse};

/// Malformed source still produces every syntactic product. The only failure is a source too large
/// for Sumi's `u32` coordinate space.
pub fn parse_source(source: Box<str>) -> Result<ParsedSource, SourceTooLarge> {
    let lexed = lex(&source)?;
    let parse = parse(ParserInput::new(&lexed));
    let diagnostics = diagnostics(&source, &lexed, &parse);

    Ok(ParsedSource {
        source,
        lexed,
        parse,
        diagnostics,
    })
}

#[derive(Clone, Debug)]
pub struct ParsedSource {
    source: Box<str>,
    lexed: LexedFile,
    parse: Parse,
    diagnostics: Box<[Diagnostic]>,
}

impl ParsedSource {
    pub fn source(&self) -> &str {
        &self.source
    }

    pub fn lexed(&self) -> &LexedFile {
        &self.lexed
    }

    pub fn parse(&self) -> &Parse {
        &self.parse
    }

    /// Canonical diagnostics in source order.
    pub fn diagnostics(&self) -> &[Diagnostic] {
        &self.diagnostics
    }
}
