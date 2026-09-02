//! Renderer-independent diagnostics for Sumi.
//!
//! A frontend or later compiler phase owns the source snapshots and assigns
//! stable codes, wording, labels, notes, and fixes. Every label names its
//! file, so a diagnostic produced from one file can point into another —
//! "defined here" — and renderers only project this canonical
//! representation for their audience.

use sumi_text::{FileId, Span, TextEdit, TextRange, TextSize};

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

/// How much a diagnostic matters: whether it rejects the program, and how
/// a renderer or an editor presents it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Severity {
    /// The program is rejected.
    Error,
    /// The program is accepted, but something in it is probably wrong.
    Warning,
    /// Something worth knowing that is neither: an allowed but notable
    /// construct, or the outcome of an analysis.
    Info,
    /// A suggestion an editor shows unobtrusively, such as an unused name
    /// it greys out.
    Hint,
}

/// Where a diagnostic label sits: a file, and within it either source text
/// or a byte boundary where syntax is absent.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Location {
    pub file: FileId,
    pub place: Place,
}

/// The part of a file a label points at.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Place {
    /// Source text relevant to the diagnostic. The range may be empty when
    /// the producer reported an empty source range, such as an empty
    /// character literal's contents.
    Range(TextRange),
    /// A byte boundary where syntax is absent.
    Point(TextSize),
}

impl Location {
    /// A label over the text of `span`.
    pub const fn range(span: Span) -> Self {
        Self {
            file: span.file(),
            place: Place::Range(span.range()),
        }
    }

    /// A label at a byte boundary of `file` where syntax is absent.
    pub const fn point(file: FileId, offset: TextSize) -> Self {
        Self {
            file,
            place: Place::Point(offset),
        }
    }

    /// The bytes the label covers; a point covers none.
    pub const fn span(self) -> Span {
        Span::new(self.file, TextRange::new(self.start(), self.end()))
    }

    pub const fn start(self) -> TextSize {
        match self.place {
            Place::Range(range) => range.start(),
            Place::Point(point) => point,
        }
    }

    pub const fn end(self) -> TextSize {
        match self.place {
            Place::Range(range) => range.end(),
            Place::Point(point) => point,
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

/// Whether a fix may be applied without anyone reading it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Applicability {
    /// The edit is mechanically right: it keeps the program's meaning, or
    /// restores the one the diagnostic says was intended. A tool may apply
    /// it on its own.
    Safe,
    /// The edit is a plausible guess — a name that was probably meant, an
    /// operand that would type-check — and needs a person to confirm it.
    MaybeIncorrect,
}

/// One source action offered for a diagnostic. Every edit is relative to
/// the same source snapshot and applies atomically. Edits must not overlap;
/// their order is retained for insertions at the same byte boundary.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Fix {
    pub message: Box<str>,
    pub applicability: Applicability,
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
    /// Explanations that belong to no source location — what the rule is
    /// and why, or what to do instead — rendered after the labels.
    pub notes: Box<[Box<str>]>,
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
        let file = FileId::new(7);
        let position = TextSize::new(3);
        let range = Location::range(Span::new(file, TextRange::new(position, position)));
        let point = Location::point(file, position);

        assert_ne!(range, point);
        assert_eq!((range.start(), range.end()), (position, position));
        assert_eq!((point.start(), point.end()), (position, position));
        assert_eq!(range.span(), point.span());
        assert_eq!(point.span().file(), file);
    }
}
