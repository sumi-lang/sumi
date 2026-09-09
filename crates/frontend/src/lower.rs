use std::collections::HashSet;

use sumi_diagnostics::{Applicability, Diagnostic, DiagnosticCode, Fix, Label, Location, Severity};
use sumi_format::layout_violation_edits;
use sumi_lexer::{LexError, LexErrorKind, LexedFile, TokenFlags, canonicalize_number_literal};
use sumi_syntax::{
    Parse, ParseAnchor, ParseEvidence, ParseExpected, ParseRecovery, ParseRecoveryKind,
    ParseViolation, ParseViolationKind, RawGap, RawTokenRange, SyntaxKind, raw_boundary,
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
            ParseAnchor::Gap(gap) => self.point(raw_boundary(self.lexed, gap.trivia_end())),
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
    let mut number = None;
    let mut labels = Vec::new();
    for error in errors {
        let (code, message) = match error.kind {
            LexErrorKind::ReservedIdentifier(keyword) => {
                diagnostics.push(primary(
                    codes::RESERVED_IDENTIFIER,
                    format!(
                        "identifier normalizes to reserved spelling `{}`",
                        keyword.text().expect("reserved spelling")
                    ),
                    snapshot.range(error.range),
                ));
                continue;
            }
            LexErrorKind::LeadingZero => {
                (codes::NONCANONICAL_NUMBER, "integer part has leading zeros")
            }
            LexErrorKind::MisplacedUnderscore => (
                codes::NONCANONICAL_NUMBER,
                "underscore must be between two digits",
            ),
            LexErrorKind::UppercaseExponent => (
                codes::NONCANONICAL_NUMBER,
                "exponent marker must be lowercase `e`",
            ),
            LexErrorKind::ExponentPlusSign => (
                codes::NONCANONICAL_NUMBER,
                "`+` is not allowed in an exponent",
            ),
            LexErrorKind::ExponentLeadingZero => {
                (codes::NONCANONICAL_NUMBER, "exponent has leading zeros")
            }
            LexErrorKind::UnterminatedString => {
                (codes::UNTERMINATED_STRING, "unterminated string literal")
            }
            LexErrorKind::UnclosedHole => (
                codes::UNCLOSED_HOLE,
                "hole in string literal is not closed on its line",
            ),
            LexErrorKind::UnterminatedRawString => (
                codes::UNTERMINATED_RAW_STRING,
                "unterminated raw string literal",
            ),
            LexErrorKind::UnterminatedBlockString => (
                codes::UNTERMINATED_BLOCK_STRING,
                "unterminated multi-line string literal",
            ),
            LexErrorKind::UnterminatedRawBlockString => (
                codes::UNTERMINATED_RAW_BLOCK_STRING,
                "unterminated raw multi-line string literal",
            ),
            LexErrorKind::UnterminatedChar => {
                (codes::UNTERMINATED_CHAR, "unterminated character literal")
            }
            LexErrorKind::LoneCarriageReturn => (
                codes::LONE_CARRIAGE_RETURN,
                "carriage return must be followed by a line feed",
            ),
            LexErrorKind::MisplacedBom => (
                codes::MISPLACED_BOM,
                "byte-order mark is only allowed at the start of a file",
            ),
            LexErrorKind::UnknownCharacter => (
                codes::UNKNOWN_CHARACTER,
                "character has no meaning in Sumi source",
            ),
            LexErrorKind::UnknownSuffix => {
                (codes::UNKNOWN_SUFFIX, "literal suffixes are not supported")
            }
            LexErrorKind::MissingExponent => (codes::MISSING_EXPONENT, "exponent has no digits"),
            LexErrorKind::UnknownEscape => (codes::UNKNOWN_ESCAPE, "unknown escape sequence"),
            LexErrorKind::MalformedUnicodeEscape => {
                (codes::MALFORMED_UNICODE_ESCAPE, "malformed Unicode escape")
            }
            LexErrorKind::InvalidUnicodeScalar => (
                codes::INVALID_UNICODE_SCALAR,
                "Unicode escape is not a valid scalar value",
            ),
            LexErrorKind::EmptyCharLiteral => {
                (codes::EMPTY_CHAR_LITERAL, "character literal is empty")
            }
            LexErrorKind::MoreThanOneChar => (
                codes::MORE_THAN_ONE_CHAR,
                "character literal contains more than one character",
            ),
            LexErrorKind::UnknownPunctuation => (
                codes::UNKNOWN_PUNCTUATION,
                "punctuation has no meaning in Sumi source",
            ),
            LexErrorKind::BlockStringOpenerContent => (
                codes::BLOCK_STRING_OPENER_CONTENT,
                "multi-line string content must begin on the line after `\"\"\"`",
            ),
            LexErrorKind::BlockStringCloserContent => (
                codes::BLOCK_STRING_CLOSER_CONTENT,
                "closing `\"\"\"` must begin its own line",
            ),
            LexErrorKind::BlockStringIndentation => (
                codes::BLOCK_STRING_INDENTATION,
                "line is indented less than the closing `\"\"\"`",
            ),
        };
        if code == codes::NONCANONICAL_NUMBER {
            // Reserve its producer-order position at the first numeric fact.
            // Ordinary errors already go directly to their final destination.
            number.get_or_insert_with(|| {
                diagnostics.push(primary(
                    code,
                    "numeric literal is not in canonical form",
                    snapshot.range(error.range),
                ));
                diagnostics.len() - 1
            });
            labels.push(Label {
                location: snapshot.range(error.range),
                message: Some(message.into()),
            });
            continue;
        }
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
    if let Some(index) = number {
        let diagnostic = &mut diagnostics[index];
        // The scanner can report an earlier underscore last.
        labels.sort_by_key(|label| (label.location.start(), label.location.end()));
        diagnostic.primary = labels.remove(0);
        diagnostic.secondary = labels.into_boxed_slice();
        let token = errors[0].token;
        let token_range = snapshot.lexed.range(token);
        let text = snapshot.lexed.text(snapshot.source, token);
        diagnostic.fix = canonicalize_number_literal(text).map(|replacement| Fix {
            message: "canonicalize numeric literal".into(),
            applicability: Applicability::Safe,
            edits: vec![TextEdit::new(token_range, replacement)].into_boxed_slice(),
        });
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
    let secondary = opener
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
    let fix = closer_fix(recovery, snapshot, closer_fix_sites);

    Diagnostic {
        code,
        severity: Severity::Error,
        message,
        primary: Label {
            location,
            message: None,
        },
        secondary,
        notes: Box::new([]),
        fix,
    }
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
            || matches!(
                lexed.kind(token),
                SyntaxKind::StringStart | SyntaxKind::StringMiddle | SyntaxKind::HoleClose
            )
    }) {
        return None;
    }
    // In a damaged hole the lexer keeps `r` separate from the first two
    // quotes of `r\"\"\"`, so the third can close the surrounding literal.
    // Inserting before that third quote breaks the triple and makes the
    // existing `r\"\"` one raw-string token instead.
    if previous.is_some_and(|quote| {
        lexed.kind(quote) == SyntaxKind::StringLiteral
            && lexed.text(snapshot.source, quote) == "\"\""
            && quote.checked_sub(1).is_some_and(|ident| {
                lexed.kind(ident) == SyntaxKind::Ident
                    && lexed.text(snapshot.source, ident) == "r"
                    && lexed.flags(ident).contains(TokenFlags::HOLE_AFTER)
            })
    }) {
        return None;
    }
    let at = raw_boundary(lexed, gap.trivia_start());
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
    let fix = layout_violation_edits(snapshot.lexed, violation).map(|edits| Fix {
        message: match violation.kind {
            ParseViolationKind::UnspacedBinaryOperator => "space binary operator",
            ParseViolationKind::SpacedPrefixOperator => "remove space after prefix operator",
            ParseViolationKind::SpacedListOpener => "remove space before `(`",
            ParseViolationKind::FunctionNameOnNextLine => "move function name onto `fn` line",
            ParseViolationKind::FunctionItemOnSameLine => "move function item onto a new line",
            ParseViolationKind::BindingNameOnNextLine => "move binding name onto `let` line",
            ParseViolationKind::ChainedComparison => {
                unreachable!("chained comparisons have no mechanical layout fix")
            }
        }
        .into(),
        applicability: Applicability::Safe,
        edits,
    });
    let mut diagnostic = primary(code, message, snapshot.raw_range(violation.range));
    diagnostic.fix = fix;
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
    TextRange::new(
        raw_boundary(lexed, range.start()),
        raw_boundary(lexed, range.end()),
    )
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
