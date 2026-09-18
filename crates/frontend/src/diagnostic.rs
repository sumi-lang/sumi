//! Renderer-independent diagnostics, as the frontend and every later
//! phase produce them: a stable code, wording, labels, and a fix. Every
//! diagnostic rejects the program. Every span names its file, so a
//! diagnostic produced from one file can point into another — "defined
//! here" — and renderers only project this canonical representation for
//! their audience.

use std::fmt;

use sumi_text::{Span, TextEdit};

/// A namespace for related diagnostic codes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct DiagnosticGroup(&'static str);

impl DiagnosticGroup {
    pub const fn new(value: &'static str) -> Self {
        assert!(valid_component(value), "invalid diagnostic group");
        Self(value)
    }

    pub const fn as_str(self) -> &'static str {
        self.0
    }
}

/// A stable, public identifier for one class of diagnostic.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct DiagnosticCode {
    group: DiagnosticGroup,
    name: &'static str,
}

impl DiagnosticCode {
    pub const fn new(group: DiagnosticGroup, name: &'static str) -> Self {
        assert!(valid_component(name), "invalid diagnostic code name");
        Self { group, name }
    }

    pub const fn group(self) -> DiagnosticGroup {
        self.group
    }

    pub const fn name(self) -> &'static str {
        self.name
    }
}

/// The code's public spelling: its group and name joined by `/`, which
/// neither component may contain.
impl fmt::Display for DiagnosticCode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}/{}", self.group.0, self.name)
    }
}

const fn valid_component(value: &str) -> bool {
    let bytes = value.as_bytes();
    if bytes.is_empty() {
        return false;
    }

    let mut index = 0;
    while index < bytes.len() {
        if bytes[index] == b'/' {
            return false;
        }
        index += 1;
    }

    true
}

/// Related evidence for a diagnostic: a span and what it shows.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Label {
    pub span: Span,
    pub message: Box<str>,
}

/// One source action offered for a diagnostic. The edit is mechanically
/// right — it keeps the program's meaning, or restores the one the
/// diagnostic says was intended — so a tool may apply it unread. Every
/// edit is relative to the same source snapshot and applies atomically.
/// Edits must not overlap; their order is retained for insertions at the
/// same byte boundary.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Fix {
    pub message: Box<str>,
    pub edits: Box<[TextEdit]>,
}

/// One canonical diagnostic, independent of terminal, protocol, or editor
/// presentation. Every diagnostic is an error: it rejects the program.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Diagnostic {
    pub code: DiagnosticCode,
    pub message: Box<str>,
    /// Where the diagnostic is: source text, or an empty span at the byte
    /// boundary where syntax is absent.
    pub primary: Span,
    /// Related evidence, rendered after the primary span.
    pub labels: Box<[Label]>,
    /// A source action for the diagnostic's source snapshot.
    pub fix: Option<Fix>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn diagnostic_codes_have_structured_identity() {
        const LEXER: DiagnosticGroup = DiagnosticGroup::new("lexer");
        const UNKNOWN_CHARACTER: DiagnosticCode = DiagnosticCode::new(LEXER, "unknown-character");

        assert_eq!(UNKNOWN_CHARACTER.group(), LEXER);
        assert_eq!(UNKNOWN_CHARACTER.group().as_str(), "lexer");
        assert_eq!(UNKNOWN_CHARACTER.name(), "unknown-character");
        assert_eq!(UNKNOWN_CHARACTER.to_string(), "lexer/unknown-character");
    }

    #[test]
    #[should_panic(expected = "invalid diagnostic group")]
    fn diagnostic_groups_cannot_contain_the_serialization_separator() {
        DiagnosticGroup::new("front/end");
    }

    #[test]
    #[should_panic(expected = "invalid diagnostic code name")]
    fn diagnostic_code_names_cannot_contain_the_serialization_separator() {
        DiagnosticCode::new(DiagnosticGroup::new("frontend"), "unknown/character");
    }
}
