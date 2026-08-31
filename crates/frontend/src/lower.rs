use sumi_diagnostics::{Diagnostic, DiagnosticCode, Label, Location, Severity};
use sumi_lexer::{LexErrorKind, LexedFile};
use sumi_syntax::{
    CookedFile, Parse, ParseAnchor, ParseEvidence, ParseExpected, ParseRecovery, ParseRecoveryKind,
    ParseViolation, ParseViolationKind, RawGap, RawTokenRange, SyntaxError, SyntaxErrorKind,
    SyntaxKind, raw_boundary,
};
use sumi_text::TextRange;

use crate::codes;

pub(crate) fn diagnostics(
    lexed: &LexedFile,
    cooked: &CookedFile,
    parse: &Parse,
) -> Box<[Diagnostic]> {
    let mut diagnostics = Vec::new();
    lower_lex(lexed, &mut diagnostics);
    lower_cook(cooked, &mut diagnostics);
    lower_parse(lexed, cooked, parse, &mut diagnostics);

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

fn lower_lex(lexed: &LexedFile, diagnostics: &mut Vec<Diagnostic>) {
    for error in lexed.errors() {
        let (code, message) = match error.kind {
            LexErrorKind::UnterminatedString => {
                (codes::UNTERMINATED_STRING, "unterminated string literal")
            }
            LexErrorKind::UnterminatedRawString => (
                codes::UNTERMINATED_RAW_STRING,
                "unterminated raw string literal",
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
        };
        diagnostics.push(primary(
            code,
            message,
            Location::Range(lexed.range(error.token as usize)),
        ));
    }
}

fn lower_cook(cooked: &CookedFile, diagnostics: &mut Vec<Diagnostic>) {
    let errors = cooked.errors();
    let mut start = 0;
    while start < errors.len() {
        let token = errors[start].token;
        let mut end = start + 1;
        while end < errors.len() && errors[end].token == token {
            end += 1;
        }
        lower_token_errors(&errors[start..end], diagnostics);
        start = end;
    }
}

struct NumberFact {
    order: usize,
    range: TextRange,
    message: &'static str,
}

fn lower_token_errors(errors: &[SyntaxError], diagnostics: &mut Vec<Diagnostic>) {
    let mut emitted = Vec::new();
    let mut number_facts = Vec::new();

    for (order, error) in errors.iter().enumerate() {
        match error.kind {
            SyntaxErrorKind::LeadingZero => number_facts.push(NumberFact {
                order,
                range: error.range,
                message: "integer part has leading zeros",
            }),
            SyntaxErrorKind::MisplacedUnderscore => number_facts.push(NumberFact {
                order,
                range: error.range,
                message: "underscore must be between two digits",
            }),
            SyntaxErrorKind::UppercaseExponent => number_facts.push(NumberFact {
                order,
                range: error.range,
                message: "exponent marker must be lowercase `e`",
            }),
            SyntaxErrorKind::ExponentPlusSign => number_facts.push(NumberFact {
                order,
                range: error.range,
                message: "`+` is not allowed in an exponent",
            }),
            SyntaxErrorKind::ExponentLeadingZero => number_facts.push(NumberFact {
                order,
                range: error.range,
                message: "exponent has leading zeros",
            }),
            SyntaxErrorKind::UnknownSuffix => emitted.push((
                order,
                primary(
                    codes::UNKNOWN_SUFFIX,
                    "literal suffixes are not supported",
                    Location::Range(error.range),
                ),
            )),
            SyntaxErrorKind::MissingExponent => emitted.push((
                order,
                primary(
                    codes::MISSING_EXPONENT,
                    "exponent has no digits",
                    Location::Range(error.range),
                ),
            )),
            SyntaxErrorKind::UnknownEscape => emitted.push((
                order,
                primary(
                    codes::UNKNOWN_ESCAPE,
                    "unknown escape sequence",
                    Location::Range(error.range),
                ),
            )),
            SyntaxErrorKind::MalformedUnicodeEscape => emitted.push((
                order,
                primary(
                    codes::MALFORMED_UNICODE_ESCAPE,
                    "malformed Unicode escape",
                    Location::Range(error.range),
                ),
            )),
            SyntaxErrorKind::InvalidUnicodeScalar => emitted.push((
                order,
                primary(
                    codes::INVALID_UNICODE_SCALAR,
                    "Unicode escape is not a valid scalar value",
                    Location::Range(error.range),
                ),
            )),
            SyntaxErrorKind::EmptyCharLiteral => emitted.push((
                order,
                primary(
                    codes::EMPTY_CHAR_LITERAL,
                    "character literal is empty",
                    Location::Range(error.range),
                ),
            )),
            SyntaxErrorKind::MoreThanOneChar => emitted.push((
                order,
                primary(
                    codes::MORE_THAN_ONE_CHAR,
                    "character literal contains more than one character",
                    Location::Range(error.range),
                ),
            )),
            SyntaxErrorKind::UnknownPunctuation => emitted.push((
                order,
                primary(
                    codes::UNKNOWN_PUNCTUATION,
                    "punctuation has no meaning in Sumi source",
                    Location::Range(error.range),
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
        emitted.push((
            order,
            Diagnostic {
                code: codes::NONCANONICAL_NUMBER,
                severity: Severity::Error,
                message: "numeric literal is not in canonical form".into(),
                primary: Label {
                    location: Location::Range(first.range),
                    message: Some(first.message.into()),
                },
                secondary: facts
                    .map(|fact| Label {
                        location: Location::Range(fact.range),
                        message: Some(fact.message.into()),
                    })
                    .collect(),
            },
        ));
    }

    emitted.sort_by_key(|(order, _)| *order);
    diagnostics.extend(emitted.into_iter().map(|(_, diagnostic)| diagnostic));
}

fn lower_parse(
    lexed: &LexedFile,
    cooked: &CookedFile,
    parse: &Parse,
    diagnostics: &mut Vec<Diagnostic>,
) {
    for evidence in parse.evidence() {
        match evidence {
            ParseEvidence::Recovery(recovery) => {
                if recovery.kind == ParseRecoveryKind::PriorPhaseError
                    || anchor_has_error(recovery.anchor, cooked)
                {
                    continue;
                }
                diagnostics.push(lower_recovery(recovery, lexed));
            }
            ParseEvidence::Violation(violation) => {
                if !tokens_have_error(violation.range, cooked) {
                    diagnostics.push(lower_violation(*violation, lexed));
                }
            }
        }
    }
}

fn lower_recovery(recovery: &ParseRecovery, lexed: &LexedFile) -> Diagnostic {
    let location = lower_anchor(recovery.anchor, lexed);
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
    let secondary = recovery
        .skipped
        .iter()
        .map(|&range| Location::Range(lower_raw_range(range, lexed)))
        .filter(|&skipped| skipped != location)
        .map(|location| Label {
            location,
            message: Some("skipped while recovering".into()),
        })
        .collect();

    Diagnostic {
        code,
        severity: Severity::Error,
        message,
        primary: Label {
            location,
            message: None,
        },
        secondary,
    }
}

fn expected_diagnostic(expected: ParseExpected) -> (DiagnosticCode, Box<str>) {
    match expected {
        ParseExpected::Item => (codes::EXPECTED_ITEM, "expected a function item".into()),
        ParseExpected::Statement => (codes::EXPECTED_STATEMENT, "expected a statement".into()),
        ParseExpected::Expression => (codes::EXPECTED_EXPRESSION, "expected an expression".into()),
        ParseExpected::Name => (codes::EXPECTED_NAME, "expected a name".into()),
        ParseExpected::Type => (codes::EXPECTED_TYPE, "expected a type".into()),
        ParseExpected::Token(kind) => (
            codes::EXPECTED_TOKEN,
            format!("expected {}", token_description(kind)).into(),
        ),
        ParseExpected::Boundary => (
            codes::EXPECTED_BOUNDARY,
            "expected a line break between statements".into(),
        ),
    }
}

fn token_description(kind: SyntaxKind) -> &'static str {
    match kind {
        SyntaxKind::Whitespace => "whitespace",
        SyntaxKind::Newline => "a line break",
        SyntaxKind::LineComment => "a line comment",
        SyntaxKind::Ident => "a name",
        SyntaxKind::Underscore => "`_`",
        SyntaxKind::ElseKw => "`else`",
        SyntaxKind::FalseKw => "`false`",
        SyntaxKind::FnKw => "`fn`",
        SyntaxKind::IfKw => "`if`",
        SyntaxKind::LetKw => "`let`",
        SyntaxKind::MutKw => "`mut`",
        SyntaxKind::ReturnKw => "`return`",
        SyntaxKind::TrueKw => "`true`",
        SyntaxKind::IntLiteral => "an integer literal",
        SyntaxKind::FloatLiteral => "a floating-point literal",
        SyntaxKind::StringLiteral => "a string literal",
        SyntaxKind::RawStringLiteral => "a raw string literal",
        SyntaxKind::CharLiteral => "a character literal",
        SyntaxKind::LParen => "`(`",
        SyntaxKind::RParen => "`)`",
        SyntaxKind::LBrace => "`{`",
        SyntaxKind::RBrace => "`}`",
        SyntaxKind::Comma => "`,`",
        SyntaxKind::Colon => "`:`",
        SyntaxKind::Dot => "`.`",
        SyntaxKind::Eq => "`=`",
        SyntaxKind::Lt => "`<`",
        SyntaxKind::Gt => "`>`",
        SyntaxKind::Bang => "`!`",
        SyntaxKind::Plus => "`+`",
        SyntaxKind::Minus => "`-`",
        SyntaxKind::Star => "`*`",
        SyntaxKind::Slash => "`/`",
        SyntaxKind::Percent => "`%`",
        SyntaxKind::Amp => "`&`",
        SyntaxKind::Pipe => "`|`",
        SyntaxKind::Error => "valid syntax",
    }
}

fn lower_violation(violation: ParseViolation, lexed: &LexedFile) -> Diagnostic {
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
    primary(
        code,
        message,
        Location::Range(lower_raw_range(violation.range, lexed)),
    )
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
    }
}

fn lower_anchor(anchor: ParseAnchor, lexed: &LexedFile) -> Location {
    match anchor {
        ParseAnchor::Gap(gap) => Location::Point(raw_boundary(lexed, gap.trivia_end())),
        ParseAnchor::Tokens(range) => Location::Range(lower_raw_range(range, lexed)),
    }
}

fn lower_raw_range(range: RawTokenRange, lexed: &LexedFile) -> TextRange {
    TextRange::new(
        raw_boundary(lexed, range.start()),
        raw_boundary(lexed, range.end()),
    )
}

fn anchor_has_error(anchor: ParseAnchor, cooked: &CookedFile) -> bool {
    match anchor {
        ParseAnchor::Gap(gap) => gap_before_error(gap, cooked),
        ParseAnchor::Tokens(range) => tokens_have_error(range, cooked),
    }
}

fn gap_before_error(gap: RawGap, cooked: &CookedFile) -> bool {
    (gap.trivia_end() as usize) < cooked.len()
        && cooked.kind(gap.trivia_end() as usize) == SyntaxKind::Error
}

fn tokens_have_error(range: RawTokenRange, cooked: &CookedFile) -> bool {
    (range.start()..range.end()).any(|raw| cooked.kind(raw as usize) == SyntaxKind::Error)
}
