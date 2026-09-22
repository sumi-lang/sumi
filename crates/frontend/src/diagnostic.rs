//! Renderer-independent diagnostics. An error rejects the program and a warning does not; every
//! range is into the one source it was produced from.

use std::fmt;

use sumi_text::{TextEdit, TextRange};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct DiagnosticGroup(pub &'static str);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Severity {
    Error,
    Warning,
}

impl fmt::Display for Severity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Error => "error",
            Self::Warning => "warning",
        })
    }
}

/// Stable: a code is never renamed or reused, so tools may match on it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct DiagnosticCode {
    pub group: DiagnosticGroup,
    pub name: &'static str,
    pub severity: Severity,
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

impl Diagnostic {
    pub fn is_error(&self) -> bool {
        self.code.severity == Severity::Error
    }
}

#[macro_export]
macro_rules! codes {
    (
        $(#[$group_doc:meta])* $group:ident = $group_name:literal;
        $($(#[$doc:meta])* $code:ident: $severity:ident = $name:literal;)*
    ) => {
        $(#[$group_doc])*
        pub const $group: $crate::DiagnosticGroup = $crate::DiagnosticGroup($group_name);
        $(
            $(#[$doc])*
            pub const $code: $crate::DiagnosticCode = $crate::DiagnosticCode {
                group: $group,
                name: $name,
                severity: $crate::Severity::$severity,
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
            severity: Severity::Error,
        };
        assert_eq!(UNKNOWN_CHARACTER.to_string(), "lexer/unknown-character");
    }

    mod declared {
        crate::codes! {
            LINT = "lint";

            SHADOWED: Warning = "shadowed";
        }
    }

    #[test]
    fn a_code_declares_its_severity() {
        assert_eq!(declared::SHADOWED.severity, Severity::Warning);
        assert_eq!(declared::ALL, &[declared::SHADOWED]);
        assert_eq!(
            format!("{}[{}]", declared::SHADOWED.severity, declared::SHADOWED),
            "warning[lint/shadowed]"
        );
    }
}
