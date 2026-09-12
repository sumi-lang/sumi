use std::collections::HashSet;

use sumi_diagnostics::{Applicability, Diagnostic, DiagnosticCode, Fix, Label, Location, Severity};
use sumi_format::layout_violation_edits;
use sumi_lexer::{LexError, LexErrorKind, LexedFile, TokenFlags, canonicalize_number_literal};
use sumi_syntax::{
    Parse, ParseAnchor, ParseEvidence, ParseExpected, ParseRecovery, ParseRecoveryKind,
    ParseViolation, ParseViolationKind, RawGap, RawTokenRange, SyntaxKind,
};
use sumi_text::{FileId, Span, TextEdit, TextRange, TextSize};

use crate::codes;

/// The source snapshot being lowered: the file its diagnostics name, its
/// text, and its tokens.
struct Snapshot<'a> {
    file: FileId,
    source: &'a str,
    lexed: &'a LexedFile,
}

impl Snapshot<'_> {
    fn range(&self, range: TextRange) -> Location {
        Location::range(Span::new(self.file, range))
    }

    fn point(&self, offset: TextSize) -> Location {
        Location::point(self.file, offset)
    }

    fn raw_range(&self, range: RawTokenRange) -> Location {
        self.range(lower_raw_range(range, self.lexed))
    }

    fn anchor(&self, anchor: ParseAnchor) -> Location {
        match anchor {
            ParseAnchor::Gap(gap) => self.point(self.lexed.boundary(gap.trivia_end())),
            ParseAnchor::Tokens(range) => self.raw_range(range),
        }
    }
}

pub(crate) fn diagnostics(
    file: FileId,
    source: &str,
    lexed: &LexedFile,
    parse: &Parse,
) -> Box<[Diagnostic]> {
    let snapshot = Snapshot {
        file,
        source,
        lexed,
    };
    let mut diagnostics = Vec::new();
    lower_lex(&snapshot, &mut diagnostics);
    lower_parse(&snapshot, parse, &mut diagnostics);

    // This sort is stable: phase precedence and producer observation order
    // break ties at the same source location.
    diagnostics.sort_by_key(|diagnostic| {
        (
            diagnostic.primary.location.start().to_u32(),
            diagnostic.primary.location.end().to_u32(),
        )
    });
    diagnostics.into_boxed_slice()
}

fn lower_lex(snapshot: &Snapshot<'_>, diagnostics: &mut Vec<Diagnostic>) {
    let errors = snapshot.lexed.errors();
    let mut start = 0;
    while start < errors.len() {
        let token = errors[start].token;
        let mut end = start + 1;
        while end < errors.len() && errors[end].token == token {
            end += 1;
        }
        lower_token_errors(snapshot, &errors[start..end], diagnostics);
        start = end;
    }
}

fn lower_token_errors(
    snapshot: &Snapshot<'_>,
    errors: &[LexError],
    diagnostics: &mut Vec<Diagnostic>,
) {
    for error in errors {
        let (code, message) = match error.kind {
            LexErrorKind::LeadingZero => {
                let mut diagnostic = primary(
                    codes::NONCANONICAL_NUMBER,
                    "integer literal has leading zeros",
                    snapshot.range(error.range),
                );
                let token_range = snapshot.lexed.range(error.token);
                let text = snapshot.lexed.text(snapshot.source, error.token);
                diagnostic.fix = canonicalize_number_literal(text).map(|replacement| Fix {
                    message: "remove the leading zeros".into(),
                    applicability: Applicability::Safe,
                    edits: vec![TextEdit::new(token_range, replacement)].into_boxed_slice(),
                });
                diagnostics.push(diagnostic);
                continue;
            }
            LexErrorKind::UnterminatedString => {
                (codes::UNTERMINATED_STRING, "unterminated string literal")
            }
            LexErrorKind::UnclosedHole => (
                codes::UNCLOSED_HOLE,
                "hole in string literal is not closed on its line",
            ),
            LexErrorKind::LoneCarriageReturn => (
                codes::LONE_CARRIAGE_RETURN,
                "carriage return must be followed by a line feed",
            ),
            LexErrorKind::UnknownCharacter => (
                codes::UNKNOWN_CHARACTER,
                "character has no meaning in Sumi source",
            ),
            LexErrorKind::UnknownSuffix => {
                (codes::UNKNOWN_SUFFIX, "literal suffixes are not supported")
            }
            LexErrorKind::UnknownEscape => (codes::UNKNOWN_ESCAPE, "unknown escape sequence"),
            LexErrorKind::UnknownPunctuation => (
                codes::UNKNOWN_PUNCTUATION,
                "punctuation has no meaning in Sumi source",
            ),
        };
        let mut diagnostic = primary(code, message, snapshot.range(error.range));
        if error.kind == LexErrorKind::UnclosedHole {
            diagnostic.notes = Box::new([
                "a `{` in a string literal opens a hole for an expression, which ends \
                 with its line; a `{` meant as text is written `\\{`"
                    .into(),
            ]);
        }
        diagnostics.push(diagnostic);
    }
}

fn lower_parse(snapshot: &Snapshot<'_>, parse: &Parse, diagnostics: &mut Vec<Diagnostic>) {
    let mut closer_fix_sites = HashSet::new();
    for evidence in parse.evidence() {
        match evidence {
            ParseEvidence::Recovery(recovery) => {
                if recovery.kind == ParseRecoveryKind::PriorPhaseError
                    || anchor_has_error(recovery.anchor, snapshot.lexed)
                {
                    continue;
                }
                diagnostics.push(lower_recovery(snapshot, recovery, &mut closer_fix_sites));
            }
            ParseEvidence::Violation(violation) => {
                if !tokens_have_error(violation.range, snapshot.lexed) {
                    diagnostics.push(lower_violation(snapshot, *violation));
                }
            }
        }
    }
}

fn lower_recovery(
    snapshot: &Snapshot<'_>,
    recovery: &ParseRecovery,
    closer_fix_sites: &mut HashSet<(SyntaxKind, u32)>,
) -> Diagnostic {
    let location = snapshot.anchor(recovery.anchor);
    let (code, message) = match recovery.kind {
        ParseRecoveryKind::Expected(expected) => expected_diagnostic(expected),
        ParseRecoveryKind::Unexpected => (
            codes::UNEXPECTED_SYNTAX,
            "unexpected syntax in expression".into(),
        ),
        ParseRecoveryKind::NestingTooDeep => (
            codes::NESTING_TOO_DEEP,
            "expression nesting limit exceeded".into(),
        ),
        ParseRecoveryKind::PriorPhaseError => {
            unreachable!("prior-phase recovery is suppressed before lowering")
        }
    };
    let opener = match recovery.kind {
        ParseRecoveryKind::Expected(ParseExpected::Closer { opener, .. }) => Some(Label {
            location: snapshot.raw_range(opener),
            message: Some("opening delimiter is here".into()),
        }),
        _ => None,
    };
    let mut diagnostic = primary(code, message, location);
    diagnostic.secondary = opener
        .into_iter()
        .chain(
            recovery
                .skipped
                .iter()
                .map(|&range| snapshot.raw_range(range))
                .filter(|&skipped| skipped != location)
                .map(|location| Label {
                    location,
                    message: Some("skipped while recovering".into()),
                }),
        )
        .collect();
    diagnostic.fix = closer_fix(recovery, snapshot, closer_fix_sites);
    diagnostic
}

fn closer_fix(
    recovery: &ParseRecovery,
    snapshot: &Snapshot<'_>,
    sites: &mut HashSet<(SyntaxKind, u32)>,
) -> Option<Fix> {
    let lexed = snapshot.lexed;
    let (ParseRecoveryKind::Expected(ParseExpected::Closer { kind, .. }), ParseAnchor::Gap(gap)) =
        (recovery.kind, recovery.anchor)
    else {
        return None;
    };
    let replacement = kind
        .text()
        .unwrap_or_else(|| unreachable!("closer evidence names a closing delimiter"));
    // A raw token boundary is not necessarily code: after a string's start,
    // middle, or hole closer the lexer resumes literal text. An insertion
    // there changes the literal instead of adding the promised delimiter.
    // Unterminated tails likewise absorb it, including a StringEnd whose
    // late error names StringStart rather than the tail itself.
    let previous = gap.trivia_start().checked_sub(1);
    if previous.is_some_and(|token| {
        lexed.flags(token).contains(TokenFlags::UNTERMINATED)
            // Braces also control the lexer's hole depth. Conservatively
            // withhold them in holes rather than change a later brace's role.
            || (kind == SyntaxKind::RBrace && lexed.flags(token).contains(TokenFlags::HOLE_AFTER))
            // A quote in a hole closes the literal unless the rest of its
            // line closes a string begun there, escapes included. After a
            // stray backslash the inserted closer would be such an escape,
            // and a quote before the insertion would change its role.
            || (lexed.flags(token).contains(TokenFlags::HOLE_AFTER)
                && lexed.text(snapshot.source, token) == "\\")
            || matches!(
                lexed.kind(token),
                SyntaxKind::StringStart | SyntaxKind::StringMiddle | SyntaxKind::HoleClose
            )
    }) {
        return None;
    }
    let at = lexed.boundary(gap.trivia_start());
    let site = (kind, at.to_u32());
    // At one site a closer binds the innermost same-kind opener, regardless
    // of which diagnostic offered it. Fix that one now; a reparse can then
    // offer the next outer closer without a misleading duplicate action.
    if !sites.insert(site) {
        return None;
    }
    Some(Fix {
        message: format!("insert {}", kind.describe()).into(),
        applicability: Applicability::Safe,
        edits: vec![TextEdit::new(TextRange::new(at, at), replacement)].into_boxed_slice(),
    })
}

fn expected_diagnostic(expected: ParseExpected) -> (DiagnosticCode, Box<str>) {
    match expected {
        ParseExpected::Item => (codes::EXPECTED_ITEM, "expected a function item".into()),
        ParseExpected::Statement => (codes::EXPECTED_STATEMENT, "expected a statement".into()),
        ParseExpected::Expression => (codes::EXPECTED_EXPRESSION, "expected an expression".into()),
        ParseExpected::Name => (codes::EXPECTED_NAME, "expected a name".into()),
        ParseExpected::Type => (codes::EXPECTED_TYPE, "expected a type".into()),
        ParseExpected::Body => (codes::EXPECTED_BODY, "expected a body, `{` or `=`".into()),
        ParseExpected::Token(kind) | ParseExpected::Closer { kind, .. } => (
            codes::EXPECTED_TOKEN,
            format!("expected {}", kind.describe()).into(),
        ),
        ParseExpected::Boundary => (
            codes::EXPECTED_BOUNDARY,
            "expected a line break between statements".into(),
        ),
    }
}

fn lower_violation(snapshot: &Snapshot<'_>, violation: ParseViolation) -> Diagnostic {
    // Each rule: its code, its message, and the name of its layout fix when
    // one is mechanical.
    let (code, message, fix_message) = match violation.kind {
        ParseViolationKind::UnspacedBinaryOperator => (
            codes::UNSPACED_BINARY_OPERATOR,
            "binary operator must have spaces on both sides",
            Some("space binary operator"),
        ),
        ParseViolationKind::SpacedPrefixOperator => (
            codes::SPACED_PREFIX_OPERATOR,
            "prefix operator must be adjacent to its operand",
            Some("remove space after prefix operator"),
        ),
        ParseViolationKind::SpacedListOpener => (
            codes::SPACED_LIST_OPENER,
            "opening `(` must be adjacent to the function name or callee",
            Some("remove space before `(`"),
        ),
        ParseViolationKind::FunctionNameOnNextLine => (
            codes::FUNCTION_NAME_ON_NEXT_LINE,
            "function name must be on the same line as `fn`",
            Some("move function name onto `fn` line"),
        ),
        ParseViolationKind::FunctionItemOnSameLine => (
            codes::FUNCTION_ITEM_ON_SAME_LINE,
            "function item must begin on a new line",
            Some("move function item onto a new line"),
        ),
        ParseViolationKind::BindingNameOnNextLine => (
            codes::BINDING_NAME_ON_NEXT_LINE,
            "binding name must be on the same line as `let`",
            Some("move binding name onto `let` line"),
        ),
        ParseViolationKind::ChainedComparison => (
            codes::CHAINED_COMPARISON,
            "comparison operators cannot be chained",
            None,
        ),
    };
    let mut diagnostic = primary(code, message, snapshot.raw_range(violation.range));
    diagnostic.fix = layout_violation_edits(snapshot.lexed, violation).map(|edits| Fix {
        message: fix_message
            .unwrap_or_else(|| unreachable!("a rule with layout edits names its fix"))
            .into(),
        applicability: Applicability::Safe,
        edits,
    });
    diagnostic
}

fn primary(code: DiagnosticCode, message: impl Into<Box<str>>, location: Location) -> Diagnostic {
    Diagnostic {
        code,
        severity: Severity::Error,
        message: message.into(),
        primary: Label {
            location,
            message: None,
        },
        secondary: Box::new([]),
        notes: Box::new([]),
        fix: None,
    }
}

fn lower_raw_range(range: RawTokenRange, lexed: &LexedFile) -> TextRange {
    TextRange::new(lexed.boundary(range.start()), lexed.boundary(range.end()))
}

fn anchor_has_error(anchor: ParseAnchor, lexed: &LexedFile) -> bool {
    match anchor {
        ParseAnchor::Gap(gap) => gap_before_error(gap, lexed),
        ParseAnchor::Tokens(range) => tokens_have_error(range, lexed),
    }
}

fn gap_before_error(gap: RawGap, lexed: &LexedFile) -> bool {
    gap.trivia_end() < lexed.end() && lexed.kind(gap.trivia_end()) == SyntaxKind::Error
}

fn tokens_have_error(range: RawTokenRange, lexed: &LexedFile) -> bool {
    range.iter().any(|raw| lexed.kind(raw) == SyntaxKind::Error)
}
