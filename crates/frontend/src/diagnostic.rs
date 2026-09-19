//! Renderer-independent diagnostics. Every diagnostic rejects the program, and every range is into
//! the one source it was produced from.

use std::fmt;

use sumi_text::{TextEdit, TextRange};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct DiagnosticGroup(pub &'static str);

/// Stable: a code is never renamed or reused, so tools may match on it.
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

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Label {
    pub range: TextRange,
    pub message: Box<str>,
}

/// The edit is against the diagnostic's source and may be applied unread.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Fix {
    pub message: Box<str>,
    pub edit: TextEdit,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Diagnostic {
    pub code: DiagnosticCode,
    pub message: Box<str>,
    /// An empty range marks the byte boundary where syntax is absent.
    pub primary: TextRange,
    pub labels: Box<[Label]>,
    pub fix: Option<Fix>,
}

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
        /// In declaration order.
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
