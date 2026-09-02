//! The source-owning syntactic frontend for Sumi.
//!
//! [`parse_source`] runs every syntactic phase and lowers their immutable,
//! phase-local evidence into canonical diagnostics. Detection remains in
//! the lexer and parser; cross-phase wording, grouping,
//! suppression, and ordering live here.

mod lower;

pub mod codes;

pub use sumi_diagnostics::{
    Applicability, Diagnostic, DiagnosticCode, DiagnosticGroup, Fix, Label, Location, Place,
    Severity,
};
pub use sumi_lexer::SourceTooLarge;
use sumi_lexer::{LexedFile, lex};
use sumi_syntax::{Parse, ParserInput, parse};
pub use sumi_text::{FileId, Span, TextEdit};

/// Parse one immutable source snapshot, the text of `file`.
///
/// Malformed source still produces every syntactic product. The only failure
/// is a source too large for Sumi's `u32` file-local coordinate space. The
/// caller allocates the [`FileId`]; every diagnostic label names it.
pub fn parse_source(file: FileId, source: Box<str>) -> Result<ParsedSource, SourceTooLarge> {
    let lexed = lex(&source)?;
    let input = ParserInput::new(&lexed);
    let parse = parse(&input);
    let diagnostics = lower::diagnostics(file, &source, &lexed, &parse);

    Ok(ParsedSource {
        file,
        source,
        lexed,
        parse,
        diagnostics,
    })
}

/// All immutable syntactic products for one source revision.
#[derive(Clone, Debug)]
pub struct ParsedSource {
    file: FileId,
    source: Box<str>,
    lexed: LexedFile,
    parse: Parse,
    diagnostics: Box<[Diagnostic]>,
}

impl ParsedSource {
    /// The file the source is the text of.
    pub fn file(&self) -> FileId {
        self.file
    }

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
