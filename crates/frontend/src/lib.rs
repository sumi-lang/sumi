//! The source-owning syntactic frontend for Sumi.
//!
//! [`parse_source`] runs every syntactic phase and lowers their immutable,
//! phase-local evidence into canonical diagnostics. Detection remains in
//! the lexer and parser; cross-phase wording, grouping,
//! suppression, and ordering live here.

mod lower;

pub mod codes;

pub use sumi_diagnostics::{
    Diagnostic, DiagnosticCode, DiagnosticGroup, Fix, Label, Location, Severity,
};
pub use sumi_lexer::SourceTooLarge;
use sumi_lexer::{LexedFile, lex};
use sumi_syntax::{Parse, ParserInput, parse};
pub use sumi_text::TextEdit;

/// Parse one immutable source snapshot.
///
/// Malformed source still produces every syntactic product. The only failure
/// is a source too large for Sumi's `u32` file-local coordinate space.
pub fn parse_source(source: Box<str>) -> Result<ParsedSource, SourceTooLarge> {
    let lexed = lex(&source)?;
    let input = ParserInput::new(&lexed);
    let parse = parse(&input);
    let diagnostics = lower::diagnostics(&source, &lexed, &parse);

    Ok(ParsedSource {
        source,
        lexed,
        parse,
        diagnostics,
    })
}

/// All immutable syntactic products for one source revision.
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
