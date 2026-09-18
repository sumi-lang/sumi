//! Renderer-independent diagnostics, as the frontend and every later
//! phase produce them: a stable code, wording, labels, and a fix. Every
//! diagnostic rejects the program, and every range is into the one source
//! it was produced from; renderers only project this canonical
//! representation for their audience.

use std::fmt;

use sumi_text::{TextEdit, TextRange};

/// A namespace for related diagnostic codes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct DiagnosticGroup(pub &'static str);

/// A stable, public identifier for one class of diagnostic, declared in
/// its group's `codes!` declaration and spelled `group/name`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct DiagnosticCode {
    pub group: DiagnosticGroup,
    pub name: &'static str,
}

impl fmt::Display for DiagnosticCode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}/{}", self.group.0, self.name)
    }
}

/// Related evidence for a diagnostic: a range and what it shows.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Label {
    pub range: TextRange,
    pub message: Box<str>,
}

/// One source action offered for a diagnostic: one edit, relative to the
/// diagnostic's source snapshot. The edit is mechanically right — it keeps
/// the program's meaning, or restores the one the diagnostic says was
/// intended — so a tool may apply it unread.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Fix {
    pub message: Box<str>,
    pub edit: TextEdit,
}

/// One canonical diagnostic, independent of terminal, protocol, or editor
/// presentation. Every diagnostic is an error: it rejects the program.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Diagnostic {
    pub code: DiagnosticCode,
    pub message: Box<str>,
    /// Where the diagnostic is: source text, or an empty range at the byte
    /// boundary where syntax is absent.
    pub primary: TextRange,
    /// Related evidence, rendered after the primary range.
    pub labels: Box<[Label]>,
    /// A source action for the diagnostic's source snapshot.
    pub fix: Option<Fix>,
}

/// Declare one group of diagnostic codes: the group constant, a documented
/// constant per code, and `ALL`, every code of the group in declaration
/// order, so a code cannot go unlisted.
#[macro_export]
macro_rules! codes {
    (
        $(#[$group_doc:meta])* $group:ident = $group_name:literal;
        $($(#[$doc:meta])* $code:ident = $name:literal;)*
    ) => {
        $(#[$group_doc])*
        pub const $group: $crate::DiagnosticGroup = $crate::DiagnosticGroup($group_name);
        $(
            $(#[$doc])*
            pub const $code: $crate::DiagnosticCode = $crate::DiagnosticCode {
                group: $group,
                name: $name,
            };
        )*
        /// Every code of the group, in declaration order.
        pub const ALL: &[$crate::DiagnosticCode] = &[$($code,)*];
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_code_is_spelled_group_slash_name() {
        const LEXER: DiagnosticGroup = DiagnosticGroup("lexer");
        const UNKNOWN_CHARACTER: DiagnosticCode = DiagnosticCode {
            group: LEXER,
            name: "unknown-character",
        };
        assert_eq!(UNKNOWN_CHARACTER.to_string(), "lexer/unknown-character");
    }
}
