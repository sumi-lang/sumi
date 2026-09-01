//! Renderer-independent diagnostics for Sumi.
//!
//! Diagnostics are source-local: a frontend or later compiler phase owns the
//! source snapshot and assigns stable codes, wording, and labels. Renderers
//! only project this canonical representation for their audience.

use sumi_text::{TextEdit, TextRange, TextSize};

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

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Severity {
    Error,
    Warning,
}

/// Where a diagnostic label sits in its source snapshot.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Location {
    /// Source text relevant to the diagnostic. The range may be empty when
    /// the producer reported an empty source range, such as an empty
    /// character literal's contents.
    Range(TextRange),
    /// A byte boundary where syntax is absent.
    Point(TextSize),
}

impl Location {
    pub const fn start(self) -> TextSize {
        match self {
            Self::Range(range) => range.start(),
            Self::Point(point) => point,
        }
    }

    pub const fn end(self) -> TextSize {
        match self {
            Self::Range(range) => range.end(),
            Self::Point(point) => point,
        }
    }
}

/// One source label. The primary label establishes the diagnostic's source
/// location; secondary labels retain related evidence.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Label {
    pub location: Location,
    pub message: Option<Box<str>>,
}

/// One source action offered for a diagnostic. Every edit is relative to
/// the same source snapshot and applies atomically. Edits must not overlap;
/// their order is retained for insertions at the same byte boundary.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Fix {
    pub message: Box<str>,
    pub edits: Box<[TextEdit]>,
}

/// One canonical diagnostic, independent of terminal, protocol, or editor
/// presentation.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Diagnostic {
    pub code: DiagnosticCode,
    pub severity: Severity,
    pub message: Box<str>,
    pub primary: Label,
    pub secondary: Box<[Label]>,
    /// A source action safe to apply to the diagnostic's source snapshot.
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

    #[test]
    fn empty_ranges_remain_distinct_from_missing_syntax() {
        let position = TextSize::new(3);
        let range = Location::Range(TextRange::new(position, position));
        let point = Location::Point(position);

        assert_ne!(range, point);
        assert_eq!((range.start(), range.end()), (position, position));
        assert_eq!((point.start(), point.end()), (position, position));
    }
}
