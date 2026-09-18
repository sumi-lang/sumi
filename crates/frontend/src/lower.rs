//! Lowering the lexer's errors and the parser's evidence into diagnostics:
//! the code and wording of each, the fix where the repair is a token (a
//! closer or a canonical literal), the suppression of parser evidence a
//! lexer error already explains, and source order.

use std::collections::HashSet;

use sumi_lexer::{LexError, LexErrorKind, LexedFile, TokenFlags, canonicalize_number_literal};
use sumi_syntax::{
    Parse, ParseAnchor, ParseEvidence, ParseRecovery, ParseRecoveryKind, ParseViolation,
    ParseViolationKind, RawTokenRange, SyntaxKind,
};
use sumi_text::{TextEdit, TextRange};

use crate::codes;
use crate::diagnostic::{Diagnostic, DiagnosticCode, Fix, Label};

/// The canonical diagnostics of one source snapshot, from the evidence its
/// lexed file and parse hold: what [`parse_source`](crate::parse_source)
/// lowers, for a caller that already ran the phases.
pub fn diagnostics(source: &str, lexed: &LexedFile, parse: &Parse) -> Box<[Diagnostic]> {
    let snapshot = Snapshot { source, lexed };
    let mut diagnostics: Vec<Diagnostic> = lexed
        .errors()
        .iter()
        .map(|error| snapshot.lex_error(error))
        .collect();
    let mut closer_fix_sites = HashSet::new();
    diagnostics.extend(
        parse
            .evidence()
            .iter()
            .filter_map(|evidence| match evidence {
                ParseEvidence::Recovery(recovery) => {
                    snapshot.recovery(recovery, &mut closer_fix_sites)
                }
                ParseEvidence::Violation(violation) => snapshot.violation(*violation),
            }),
    );
    // This sort is stable: phase precedence and producer observation order
    // break ties at the same source location.
    diagnostics.sort_by_key(|diagnostic| {
        (
            diagnostic.primary.start().to_u32(),
            diagnostic.primary.end().to_u32(),
        )
    });
    diagnostics.into_boxed_slice()
}

/// The source snapshot being lowered: its text and its tokens.
struct Snapshot<'a> {
    source: &'a str,
    lexed: &'a LexedFile,
}

impl Snapshot<'_> {
    fn raw_range(&self, range: RawTokenRange) -> TextRange {
        TextRange::new(
            self.lexed.boundary(range.start()),
            self.lexed.boundary(range.end()),
        )
    }

    /// The range an anchor names: a gap is the empty range at the byte
    /// boundary where syntax is absent.
    fn anchor(&self, anchor: ParseAnchor) -> TextRange {
        match anchor {
            ParseAnchor::Gap(gap) => {
                let at = self.lexed.boundary(gap.trivia_end());
                TextRange::new(at, at)
            }
            ParseAnchor::Tokens(range) => self.raw_range(range),
        }
    }

    fn has_error(&self, range: RawTokenRange) -> bool {
        range
            .iter()
            .any(|raw| self.lexed.kind(raw) == SyntaxKind::Error)
    }

    /// Whether the lexer already reported what the anchor points at: a
    /// token of the range, or the token after the gap.
    fn anchor_has_error(&self, anchor: ParseAnchor) -> bool {
        match anchor {
            ParseAnchor::Gap(gap) => {
                gap.trivia_end() < self.lexed.end()
                    && self.lexed.kind(gap.trivia_end()) == SyntaxKind::Error
            }
            ParseAnchor::Tokens(range) => self.has_error(range),
        }
    }

    fn lex_error(&self, error: &LexError) -> Diagnostic {
        let (code, message, fix) = match error.kind {
            LexErrorKind::LeadingZero => (
                codes::NONCANONICAL_NUMBER,
                "integer literal has leading zeros",
                canonicalize_number_literal(self.lexed.text(self.source, error.token)).map(
                    |replacement| Fix {
                        message: "remove the leading zeros".into(),
                        edit: TextEdit::new(self.lexed.range(error.token), replacement),
                    },
                ),
            ),
            LexErrorKind::UnterminatedString => (
                codes::UNTERMINATED_STRING,
                "unterminated string literal",
                None,
            ),
            LexErrorKind::LoneCarriageReturn => (
                codes::LONE_CARRIAGE_RETURN,
                "carriage return must be followed by a line feed",
                None,
            ),
            LexErrorKind::UnknownCharacter => (
                codes::UNKNOWN_CHARACTER,
                "character has no meaning in Sumi source",
                None,
            ),
            LexErrorKind::UnknownSuffix => (
                codes::UNKNOWN_SUFFIX,
                "literal suffixes are not supported",
                None,
            ),
            LexErrorKind::UnknownEscape => (codes::UNKNOWN_ESCAPE, "unknown escape sequence", None),
            LexErrorKind::UnknownPunctuation => (
                codes::UNKNOWN_PUNCTUATION,
                "punctuation has no meaning in Sumi source",
                None,
            ),
        };
        Diagnostic {
            code,
            message: message.into(),
            primary: error.range,
            labels: Box::new([]),
            fix,
        }
    }

    /// A recovery's diagnostic, or none where the lexer already reported
    /// the tokens it recovered around.
    fn recovery(
        &self,
        recovery: &ParseRecovery,
        closer_fix_sites: &mut HashSet<(SyntaxKind, u32)>,
    ) -> Option<Diagnostic> {
        if self.anchor_has_error(recovery.anchor) {
            return None;
        }
        let (code, message): (DiagnosticCode, Box<str>) = match recovery.kind {
            ParseRecoveryKind::Item => (codes::EXPECTED_ITEM, "expected a function item".into()),
            ParseRecoveryKind::Statement => {
                (codes::EXPECTED_STATEMENT, "expected a statement".into())
            }
            ParseRecoveryKind::Expression => {
                (codes::EXPECTED_EXPRESSION, "expected an expression".into())
            }
            ParseRecoveryKind::Name => (codes::EXPECTED_NAME, "expected a name".into()),
            ParseRecoveryKind::Type => (codes::EXPECTED_TYPE, "expected a type".into()),
            ParseRecoveryKind::Body => (codes::EXPECTED_BODY, "expected a body, `{` or `=`".into()),
            ParseRecoveryKind::Token(kind) | ParseRecoveryKind::Closer { kind, .. } => (
                codes::EXPECTED_TOKEN,
                format!("expected {}", kind.describe()).into(),
            ),
            ParseRecoveryKind::Boundary => (
                codes::EXPECTED_BOUNDARY,
                "expected a line break between statements".into(),
            ),
            ParseRecoveryKind::Unexpected => (
                codes::UNEXPECTED_SYNTAX,
                "unexpected syntax in expression".into(),
            ),
            ParseRecoveryKind::NestingTooDeep => (
                codes::NESTING_TOO_DEEP,
                "expression nesting limit exceeded".into(),
            ),
            ParseRecoveryKind::PriorPhaseError => return None,
        };
        let primary = self.anchor(recovery.anchor);
        let opener = match recovery.kind {
            ParseRecoveryKind::Closer { opener, .. } => Some(Label {
                range: self.raw_range(opener),
                message: "opening delimiter is here".into(),
            }),
            _ => None,
        };
        let skipped = recovery
            .skipped
            .iter()
            .map(|&range| self.raw_range(range))
            .filter(|&skipped| skipped != primary)
            .map(|range| Label {
                range,
                message: "skipped while recovering".into(),
            });
        Some(Diagnostic {
            code,
            message,
            primary,
            labels: opener.into_iter().chain(skipped).collect(),
            fix: self.closer_fix(recovery, closer_fix_sites),
        })
    }

    fn closer_fix(
        &self,
        recovery: &ParseRecovery,
        sites: &mut HashSet<(SyntaxKind, u32)>,
    ) -> Option<Fix> {
        let lexed = self.lexed;
        let (ParseRecoveryKind::Closer { kind, .. }, ParseAnchor::Gap(gap)) =
            (recovery.kind, recovery.anchor)
        else {
            return None;
        };
        let replacement = kind
            .text()
            .unwrap_or_else(|| unreachable!("closer evidence names a closing delimiter"));
        // An unterminated string's tail absorbs an insertion at its boundary,
        // as its text rather than the promised delimiter.
        let previous = gap.trivia_start().checked_sub(1);
        if previous.is_some_and(|token| lexed.flags(token).contains(TokenFlags::UNTERMINATED)) {
            return None;
        }
        let at = lexed.boundary(gap.trivia_start());
        // At one site a closer binds the innermost same-kind opener, regardless
        // of which diagnostic offered it. Fix that one now; a reparse can then
        // offer the next outer closer without a misleading duplicate action.
        if !sites.insert((kind, at.to_u32())) {
            return None;
        }
        Some(Fix {
            message: format!("insert {}", kind.describe()).into(),
            edit: TextEdit::new(TextRange::new(at, at), replacement),
        })
    }

    /// A violation's diagnostic, or none where the lexer already reported
    /// its tokens. No violation names a fix: layout is the formatter's to
    /// repair, and `sumi fmt` repairs every one it can.
    fn violation(&self, violation: ParseViolation) -> Option<Diagnostic> {
        if self.has_error(violation.range) {
            return None;
        }
        let (code, message) = match violation.kind {
            ParseViolationKind::UnspacedBinaryOperator => (
                codes::UNSPACED_BINARY_OPERATOR,
                "binary operator must have spaces on both sides",
            ),
            ParseViolationKind::SpacedPrefixOperator => (
                codes::SPACED_PREFIX_OPERATOR,
                "prefix operator must be adjacent to its operand",
            ),
            ParseViolationKind::SpacedListOpener => (
                codes::SPACED_LIST_OPENER,
                "opening `(` must be adjacent to the function name or callee",
            ),
            ParseViolationKind::FunctionNameOnNextLine => (
                codes::FUNCTION_NAME_ON_NEXT_LINE,
                "function name must be on the same line as `fn`",
            ),
            ParseViolationKind::FunctionItemOnSameLine => (
                codes::FUNCTION_ITEM_ON_SAME_LINE,
                "function item must begin on a new line",
            ),
            ParseViolationKind::BindingNameOnNextLine => (
                codes::BINDING_NAME_ON_NEXT_LINE,
                "binding name must be on the same line as `let`",
            ),
            ParseViolationKind::ChainedComparison => (
                codes::CHAINED_COMPARISON,
                "comparison operators cannot be chained",
            ),
        };
        Some(Diagnostic {
            code,
            message: message.into(),
            primary: self.raw_range(violation.range),
            labels: Box::new([]),
            fix: None,
        })
    }
}
