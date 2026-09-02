//! Parser behavior a snapshot cannot express: the shape of the evidence a
//! recovery records, and bounds on how far recovery reaches. The trees,
//! evidence, and diagnostics of every case live in `tests/corpus` at the
//! workspace root.

mod common;

use sumi_lexer::{LexedFile, lex};
use sumi_syntax::{
    ParseAnchor, ParseEvidence, ParseExpected, ParseRecoveryKind, ParseViolationKind, ParserInput,
    RawIdx, parse,
};

fn raw_text<'a>(source: &'a str, lexed: &LexedFile, start: RawIdx, end: RawIdx) -> &'a str {
    let start = common::start_byte(lexed, start) as usize;
    let end = common::start_byte(lexed, end) as usize;
    &source[start..end]
}

fn evidence_name(evidence: &ParseEvidence) -> String {
    match evidence {
        ParseEvidence::Recovery(recovery) => match recovery.kind {
            ParseRecoveryKind::Expected(expected) => match expected {
                ParseExpected::Item => "ExpectedItem".into(),
                ParseExpected::Statement => "ExpectedStatement".into(),
                ParseExpected::Expression => "ExpectedExpression".into(),
                ParseExpected::Name => "ExpectedName".into(),
                ParseExpected::Type => "ExpectedType".into(),
                ParseExpected::Body => "ExpectedBody".into(),
                ParseExpected::Token(kind) => format!("Expected({kind:?})"),
                ParseExpected::Closer { kind, .. } => format!("Expected({kind:?})"),
                ParseExpected::Boundary => "ExpectedBoundary".into(),
            },
            kind => format!("{kind:?}"),
        },
        ParseEvidence::Violation(violation) => format!("{:?}", violation.kind),
    }
}

#[test]
fn a_missing_closer_retains_its_opener_and_insertion_gap() {
    let source = "fn f() { x // tail";
    let lexed = lex(source).expect("test source fits in u32");
    let parse = parse(&ParserInput::new(&lexed));
    let [ParseEvidence::Recovery(recovery)] = parse.evidence() else {
        panic!("the unclosed block has one recovery")
    };
    let ParseRecoveryKind::Expected(ParseExpected::Closer { kind, opener }) = recovery.kind else {
        panic!("the expected closer must retain its opener")
    };
    assert_eq!(kind, sumi_syntax::SyntaxKind::RBrace);
    assert_eq!(raw_text(source, &lexed, opener.start(), opener.end()), "{");
    let ParseAnchor::Gap(gap) = recovery.anchor else {
        panic!("missing syntax must anchor a gap")
    };
    assert_eq!(
        raw_text(source, &lexed, gap.trivia_start(), gap.trivia_end()),
        " // tail"
    );
    assert!(recovery.skipped.is_empty());
}

#[test]
fn present_syntax_anchors_nonempty_token_ranges() {
    let source = "fn f() { a==b }";
    let lexed = lex(source).expect("test source fits in u32");
    let parse = parse(&ParserInput::new(&lexed));
    let [ParseEvidence::Violation(violation)] = parse.evidence() else {
        panic!("the unspaced operator has one violation")
    };
    assert_eq!(violation.kind, ParseViolationKind::UnspacedBinaryOperator);
    assert_eq!(
        raw_text(
            source,
            &lexed,
            violation.range.start(),
            violation.range.end()
        ),
        "=="
    );
}

#[test]
fn recovery_records_the_ranges_it_skips() {
    let source = ": (x)";
    let lexed = lex(source).expect("test source fits in u32");
    let parse = parse(&ParserInput::new(&lexed));
    let [ParseEvidence::Recovery(recovery)] = parse.evidence() else {
        panic!("top-level garbage has one recovery")
    };
    assert_eq!(
        recovery.kind,
        ParseRecoveryKind::Expected(ParseExpected::Item)
    );
    let ParseAnchor::Tokens(anchor) = recovery.anchor else {
        panic!("rejected syntax must anchor tokens")
    };
    assert_eq!(raw_text(source, &lexed, anchor.start(), anchor.end()), ":");
    let [skipped] = &*recovery.skipped else {
        panic!("the recovery has one skipped range")
    };
    assert_eq!(
        raw_text(source, &lexed, skipped.start(), skipped.end()),
        source
    );
}

#[test]
fn prior_phase_tokens_are_recorded_as_recovery() {
    let source = "fn f() {\n  a ;\n  b\n}";
    let lexed = lex(source).expect("test source fits in u32");
    let parsed = parse(&ParserInput::new(&lexed));
    let ParseEvidence::Recovery(recovery) = &parsed.evidence()[1] else {
        panic!("the prior-phase token starts a recovery")
    };
    assert_eq!(recovery.kind, ParseRecoveryKind::PriorPhaseError);
    let ParseAnchor::Tokens(anchor) = recovery.anchor else {
        panic!("prior-phase syntax must anchor its tokens")
    };
    assert_eq!(raw_text(source, &lexed, anchor.start(), anchor.end()), ";");
    assert_eq!(recovery.skipped.as_ref(), &[anchor]);

    // Adjacent tokens diagnosed by earlier phases form one recovery run.
    let source = "fn f() { ; € }";
    let lexed = lex(source).expect("test source fits in u32");
    let parsed = parse(&ParserInput::new(&lexed));
    let [ParseEvidence::Recovery(recovery)] = parsed.evidence() else {
        panic!("adjacent prior-phase tokens form one recovery")
    };
    assert_eq!(recovery.kind, ParseRecoveryKind::PriorPhaseError);
    let ParseAnchor::Tokens(anchor) = recovery.anchor else {
        panic!("prior-phase syntax must anchor its tokens")
    };
    assert_eq!(
        raw_text(source, &lexed, anchor.start(), anchor.end()),
        "; €"
    );
    assert_eq!(recovery.skipped.as_ref(), &[anchor]);
}

/// Parse `source` and return its evidence kinds, asserting the tree is well
/// formed.
fn evidence_kinds(source: &str) -> Vec<String> {
    let lexed = lex(source).expect("test sources fit in u32");
    let parse = parse(&ParserInput::new(&lexed));
    let _ = common::dump(parse.tree(), &lexed, source);
    parse.evidence().iter().map(evidence_name).collect()
}

/// How many `fn` items `source` parses into.
fn items(source: &str) -> usize {
    let lexed = lex(source).expect("test sources fit in u32");
    let parse = parse(&ParserInput::new(&lexed));
    let tree = parse.tree();
    tree.nodes()
        .filter(|&node| tree.kind(node) == sumi_syntax::NodeKind::FnItem)
        .count()
}

#[test]
fn recovery_over_many_brackets_is_linear() {
    let n = 50_000;
    let source = format!(":{}{}{}", "{".repeat(n), "(".repeat(n), ")".repeat(n));
    assert_eq!(evidence_kinds(&source), ["ExpectedItem"]);
}

#[test]
fn recovery_over_nested_groups_spanning_a_boundary_is_linear() {
    // Every group of the ladder spans the central boundary inside an
    // unclosed body, so each is rejected and entered one token at a time;
    // rejecting one must not rescan its interior.
    let n = 50_000;
    let source = format!("fn f() {{\n: {}x\ny {}\n", "{ ".repeat(n), "} ".repeat(n));
    assert_eq!(
        evidence_kinds(&source),
        ["ExpectedStatement", "ExpectedItem"]
    );
    assert_eq!(items(&source), 1);
}

#[test]
fn nesting_is_bounded() {
    use sumi_syntax::MAX_DEPTH;
    let deep = |n: usize| format!("fn f() {{ {}x{} }}", "(".repeat(n), ")".repeat(n));
    assert_eq!(
        evidence_kinds(&deep(MAX_DEPTH as usize / 2)),
        Vec::<String>::new()
    );
    // At the limit with nothing left, or with a closer: no recovery run to
    // take a token that is not an expression's. Every open construct retains
    // its own missing-closer fact at EOF.
    let opens = |n: u32| format!("fn f() {{ {}", "(".repeat(n as usize));
    let assert_unclosed = |evidence: &[String], first: &str| {
        assert!(evidence.len() >= 2);
        assert_eq!(evidence.first().map(String::as_str), Some(first));
        assert_eq!(
            evidence.last().map(String::as_str),
            Some("Expected(RBrace)")
        );
        assert!(
            evidence[1..evidence.len() - 1]
                .iter()
                .all(|kind| kind == "Expected(RParen)")
        );
    };
    assert_unclosed(&evidence_kinds(&opens(MAX_DEPTH - 2)), "ExpectedExpression");
    // The `)` closes the innermost paren; the rest stay open to the end.
    assert_unclosed(
        &evidence_kinds(&format!("{})", opens(MAX_DEPTH - 2))),
        "ExpectedExpression",
    );
    assert_unclosed(&evidence_kinds(&opens(MAX_DEPTH + 40)), "NestingTooDeep");
    // The skip past the limit stops at the next item like any recovery:
    // the parens are unclosed, so the `fn` is not theirs to take.
    let next_item = format!("{}x fn g() {{}}", opens(MAX_DEPTH + 40));
    assert_unclosed(&evidence_kinds(&next_item), "NestingTooDeep");
    assert_eq!(items(&next_item), 2);
    // Far past the limit: one error, no crash, and the file still closes.
    assert_eq!(evidence_kinds(&deep(100_000)), ["NestingTooDeep"]);
    assert_eq!(
        evidence_kinds(&format!("fn f() {{ {}x }}", "!".repeat(100_000))),
        ["NestingTooDeep"]
    );
    assert_eq!(
        evidence_kinds(&format!(
            "fn f() {{ {}if a {{}} }}",
            "if a {} else ".repeat(100_000)
        )),
        ["NestingTooDeep"]
    );
}

#[test]
fn a_malformed_suffix_belongs_to_the_latest_statement_recovery() {
    let source = "fn f() { let _ x }";
    let lexed = lex(source).expect("test source fits in u32");
    let parse = parse(&ParserInput::new(&lexed));
    let [ParseEvidence::Recovery(name), ParseEvidence::Recovery(eq)] = parse.evidence() else {
        panic!("the malformed statement has two recovery causes")
    };
    assert_eq!(name.kind, ParseRecoveryKind::Expected(ParseExpected::Name));
    assert!(name.skipped.is_empty());
    assert_eq!(
        eq.kind,
        ParseRecoveryKind::Expected(ParseExpected::Token(sumi_syntax::SyntaxKind::Eq))
    );
    let [skipped] = &*eq.skipped else {
        panic!("the latest recovery owns the malformed suffix")
    };
    assert_eq!(
        raw_text(source, &lexed, skipped.start(), skipped.end()),
        "x"
    );
}

#[test]
fn lexer_errors_do_not_hide_statement_recovery() {
    // The lexer owns the primary diagnostic for `€`, while the parser retains
    // the independent fact that it was unexpected. The ambiguous `c` belongs
    // to the malformed statement rather than becoming a new statement.
    let source = "fn f() { a € + b c }";
    let lexed = lex(source).expect("test source fits in u32");
    let parse = parse(&ParserInput::new(&lexed));
    let [ParseEvidence::Recovery(recovery)] = parse.evidence() else {
        panic!("the malformed statement has one recovery cause")
    };
    let skipped: Vec<_> = recovery
        .skipped
        .iter()
        .map(|range| raw_text(source, &lexed, range.start(), range.end()))
        .collect();
    assert_eq!(skipped, ["€", "c"]);
}
