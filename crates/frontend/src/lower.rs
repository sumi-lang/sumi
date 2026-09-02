use std::collections::HashSet;

use sumi_diagnostics::{Applicability, Diagnostic, DiagnosticCode, Fix, Label, Location, Severity};
use sumi_format::layout_violation_edits;
use sumi_lexer::{LexError, LexErrorKind, LexedFile, canonicalize_number_literal};
use sumi_syntax::{
    Parse, ParseAnchor, ParseEvidence, ParseExpected, ParseRecovery, ParseRecoveryKind,
    ParseViolation, ParseViolationKind, RawGap, RawIdx, RawTokenRange, SyntaxKind, raw_boundary,
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

struct NumberFact {
    order: usize,
    range: TextRange,
    message: &'static str,
}

fn lower_token_errors(
    snapshot: &Snapshot<'_>,
    errors: &[LexError],
    diagnostics: &mut Vec<Diagnostic>,
) {
    let mut emitted = Vec::new();
    let mut number_facts = Vec::new();

    for (order, error) in errors.iter().enumerate() {
        match error.kind {
            LexErrorKind::UnterminatedString => emitted.push((
                order,
                primary(
                    codes::UNTERMINATED_STRING,
                    "unterminated string literal",
                    snapshot.range(error.range),
                ),
            )),
            LexErrorKind::UnterminatedRawString => emitted.push((
                order,
                primary(
                    codes::UNTERMINATED_RAW_STRING,
                    "unterminated raw string literal",
                    snapshot.range(error.range),
                ),
            )),
            LexErrorKind::UnterminatedChar => emitted.push((
                order,
                primary(
                    codes::UNTERMINATED_CHAR,
                    "unterminated character literal",
                    snapshot.range(error.range),
                ),
            )),
            LexErrorKind::LoneCarriageReturn => emitted.push((
                order,
                primary(
                    codes::LONE_CARRIAGE_RETURN,
                    "carriage return must be followed by a line feed",
                    snapshot.range(error.range),
                ),
            )),
            LexErrorKind::MisplacedBom => emitted.push((
                order,
                primary(
                    codes::MISPLACED_BOM,
                    "byte-order mark is only allowed at the start of a file",
                    snapshot.range(error.range),
                ),
            )),
            LexErrorKind::UnknownCharacter => emitted.push((
                order,
                primary(
                    codes::UNKNOWN_CHARACTER,
                    "character has no meaning in Sumi source",
                    snapshot.range(error.range),
                ),
            )),
            LexErrorKind::LeadingZero => number_facts.push(NumberFact {
                order,
                range: error.range,
                message: "integer part has leading zeros",
            }),
            LexErrorKind::MisplacedUnderscore => number_facts.push(NumberFact {
                order,
                range: error.range,
                message: "underscore must be between two digits",
            }),
            LexErrorKind::UppercaseExponent => number_facts.push(NumberFact {
                order,
                range: error.range,
                message: "exponent marker must be lowercase `e`",
            }),
            LexErrorKind::ExponentPlusSign => number_facts.push(NumberFact {
                order,
                range: error.range,
                message: "`+` is not allowed in an exponent",
            }),
            LexErrorKind::ExponentLeadingZero => number_facts.push(NumberFact {
                order,
                range: error.range,
                message: "exponent has leading zeros",
            }),
            LexErrorKind::UnknownSuffix => emitted.push((
                order,
                primary(
                    codes::UNKNOWN_SUFFIX,
                    "literal suffixes are not supported",
                    snapshot.range(error.range),
                ),
            )),
            LexErrorKind::MissingExponent => emitted.push((
                order,
                primary(
                    codes::MISSING_EXPONENT,
                    "exponent has no digits",
                    snapshot.range(error.range),
                ),
            )),
            LexErrorKind::UnknownEscape => emitted.push((
                order,
                primary(
                    codes::UNKNOWN_ESCAPE,
                    "unknown escape sequence",
                    snapshot.range(error.range),
                ),
            )),
            LexErrorKind::MalformedUnicodeEscape => emitted.push((
                order,
                primary(
                    codes::MALFORMED_UNICODE_ESCAPE,
                    "malformed Unicode escape",
                    snapshot.range(error.range),
                ),
            )),
            LexErrorKind::InvalidUnicodeScalar => emitted.push((
                order,
                primary(
                    codes::INVALID_UNICODE_SCALAR,
                    "Unicode escape is not a valid scalar value",
                    snapshot.range(error.range),
                ),
            )),
            LexErrorKind::EmptyCharLiteral => emitted.push((
                order,
                primary(
                    codes::EMPTY_CHAR_LITERAL,
                    "character literal is empty",
                    snapshot.range(error.range),
                ),
            )),
            LexErrorKind::MoreThanOneChar => emitted.push((
                order,
                primary(
                    codes::MORE_THAN_ONE_CHAR,
                    "character literal contains more than one character",
                    snapshot.range(error.range),
                ),
            )),
            LexErrorKind::UnknownPunctuation => emitted.push((
                order,
                primary(
                    codes::UNKNOWN_PUNCTUATION,
                    "punctuation has no meaning in Sumi source",
                    snapshot.range(error.range),
                ),
            )),
        }
    }

    if !number_facts.is_empty() {
        let order = number_facts
            .iter()
            .map(|fact| fact.order)
            .min()
            .expect("a numeric fact exists");
        number_facts.sort_by_key(|fact| {
            (
                fact.range.start().to_u32(),
                fact.range.end().to_u32(),
                fact.order,
            )
        });
        let mut facts = number_facts.into_iter();
        let first = facts.next().expect("a numeric fact exists");
        let token = errors[0].token;
        let token_range = snapshot.lexed.range(token);
        let text = snapshot.lexed.text(snapshot.source, token);
        let fix = canonicalize_number_literal(text).map(|replacement| Fix {
            message: "canonicalize numeric literal".into(),
            applicability: Applicability::Safe,
            edits: vec![TextEdit::new(token_range, replacement)].into_boxed_slice(),
        });
        emitted.push((
            order,
            Diagnostic {
                code: codes::NONCANONICAL_NUMBER,
                severity: Severity::Error,
                message: "numeric literal is not in canonical form".into(),
                primary: Label {
                    location: snapshot.range(first.range),
                    message: Some(first.message.into()),
                },
                secondary: facts
                    .map(|fact| Label {
                        location: snapshot.range(fact.range),
                        message: Some(fact.message.into()),
                    })
                    .collect(),
                notes: Box::new([]),
                fix,
            },
        ));
    }

    emitted.sort_by_key(|(order, _)| *order);
    diagnostics.extend(emitted.into_iter().map(|(_, diagnostic)| diagnostic));
}

fn lower_parse(snapshot: &Snapshot<'_>, parse: &Parse, diagnostics: &mut Vec<Diagnostic>) {
    let has_recovery = parse
        .evidence()
        .iter()
        .any(|evidence| matches!(evidence, ParseEvidence::Recovery(_)));
    let unterminated_literals: HashSet<RawIdx> = snapshot
        .lexed
        .errors()
        .iter()
        .filter(|error| {
            matches!(
                error.kind,
                LexErrorKind::UnterminatedString
                    | LexErrorKind::UnterminatedRawString
                    | LexErrorKind::UnterminatedChar
            )
        })
        .map(|error| error.token)
        .collect();
    let mut closer_fix_sites = HashSet::new();
    for evidence in parse.evidence() {
        match evidence {
            ParseEvidence::Recovery(recovery) => {
                if recovery.kind == ParseRecoveryKind::PriorPhaseError
                    || anchor_has_error(recovery.anchor, snapshot.lexed)
                {
                    continue;
                }
                diagnostics.push(lower_recovery(
                    snapshot,
                    recovery,
                    &unterminated_literals,
                    &mut closer_fix_sites,
                ));
            }
            ParseEvidence::Violation(violation) => {
                if !tokens_have_error(violation.range, snapshot.lexed) {
                    diagnostics.push(lower_violation(snapshot, *violation, has_recovery));
                }
            }
        }
    }
}

fn lower_recovery(
    snapshot: &Snapshot<'_>,
    recovery: &ParseRecovery,
    unterminated_literals: &HashSet<RawIdx>,
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
    let fix = closer_fix(
        recovery,
        snapshot.lexed,
        unterminated_literals,
        closer_fix_sites,
    );

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
    lexed: &LexedFile,
    unterminated_literals: &HashSet<RawIdx>,
    sites: &mut HashSet<(SyntaxKind, u32)>,
) -> Option<Fix> {
    let (ParseRecoveryKind::Expected(ParseExpected::Closer { kind, .. }), ParseAnchor::Gap(gap)) =
        (recovery.kind, recovery.anchor)
    else {
        return None;
    };
    let replacement = kind
        .text()
        .unwrap_or_else(|| unreachable!("closer evidence names a closing delimiter"));
    // A delimiter immediately after an unterminated literal becomes part of
    // that token and repairs nothing. Keep the diagnostic, but offer no edit.
    let previous = gap.trivia_start().checked_sub(1);
    if previous.is_some_and(|token| unterminated_literals.contains(&token)) {
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

fn lower_violation(
    snapshot: &Snapshot<'_>,
    violation: ParseViolation,
    has_recovery: bool,
) -> Diagnostic {
    let (code, message) = match violation.kind {
        ParseViolationKind::BlockOnNewLine => (
            codes::BLOCK_ON_NEW_LINE,
            "block must open on the line of its owner",
        ),
        ParseViolationKind::UnspacedBinaryOperator => (
            codes::UNSPACED_BINARY_OPERATOR,
            "binary operator must have spaces on both sides",
        ),
        ParseViolationKind::TrailingOperator => (
            codes::TRAILING_OPERATOR,
            "binary operator must begin the continuation line",
        ),
        ParseViolationKind::SpacedPrefixOperator => (
            codes::SPACED_PREFIX_OPERATOR,
            "prefix operator must be adjacent to its operand",
        ),
        ParseViolationKind::ChainedComparison => (
            codes::CHAINED_COMPARISON,
            "comparison operators cannot be chained",
        ),
    };
    let movement = matches!(
        violation.kind,
        ParseViolationKind::BlockOnNewLine | ParseViolationKind::TrailingOperator
    );
    let fix = (!movement || !has_recovery)
        .then(|| layout_violation_edits(snapshot.source, snapshot.lexed, violation))
        .flatten()
        .map(|edits| Fix {
            message: match violation.kind {
                ParseViolationKind::BlockOnNewLine => "move block to its owner's line",
                ParseViolationKind::UnspacedBinaryOperator => "space binary operator",
                ParseViolationKind::TrailingOperator => "move operator to the continuation line",
                ParseViolationKind::SpacedPrefixOperator => "remove space after prefix operator",
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
