use proptest::prelude::*;
use sumi_frontend::{DiagnosticCode, Location, ParsedSource, Severity, codes, parse_source};
use sumi_syntax::{ParseAnchor, ParseEvidence};
use sumi_text::TextSize;

fn parsed(source: &str) -> ParsedSource {
    parse_source(source.into()).expect("test sources fit in u32")
}

fn diagnostic_codes(front: &ParsedSource) -> Vec<DiagnosticCode> {
    front
        .diagnostics()
        .iter()
        .map(|diagnostic| diagnostic.code)
        .collect()
}

fn location_text(front: &ParsedSource, location: Location) -> &str {
    match location {
        Location::Range(range) => range.text(front.source()),
        Location::Point(point) => &front.source()[point.to_usize()..point.to_usize()],
    }
}

fn raw_boundary(front: &ParsedSource, raw: u32) -> TextSize {
    sumi_syntax::raw_boundary(front.lexed(), raw)
}

#[test]
fn parsed_source_owns_every_syntactic_product() {
    let source = String::from("fn f() {}\n").into_boxed_str();
    let front = parse_source(source).expect("test source fits in u32");

    assert_eq!(front.source(), "fn f() {}\n");
    assert_eq!(front.lexed().source_len().to_usize(), front.source().len());
    assert_eq!(front.cooked().len(), front.lexed().len());
    let tree = front.parse().tree();
    assert_eq!(tree.first_token(tree.root()), 0);
    assert_eq!(tree.end_token(tree.root()) as usize, front.lexed().len());
    assert!(front.diagnostics().is_empty());

    assert!(parsed("").diagnostics().is_empty());
}

#[test]
fn frontend_diagnostic_identity_is_syntactic_not_phase_specific() {
    for code in [
        codes::UNKNOWN_CHARACTER,
        codes::NONCANONICAL_NUMBER,
        codes::EXPECTED_TOKEN,
    ] {
        assert_eq!(code.group(), codes::SYNTAX);
    }
}

#[test]
fn empty_producer_ranges_do_not_become_missing_syntax() {
    let front = parsed("fn f() { '' }");
    let [diagnostic] = front.diagnostics() else {
        panic!("an empty character literal has one diagnostic")
    };
    assert_eq!(diagnostic.code, codes::EMPTY_CHAR_LITERAL);
    let Location::Range(range) = diagnostic.primary.location else {
        panic!("empty literal content is still a producer range")
    };
    assert_eq!(range.start(), range.end());
    assert_eq!(range.start().to_usize(), 10);
}

#[test]
fn missing_syntax_points_at_the_parser_cursor() {
    let source = "// doc\nf() {}";
    let front = parsed(source);
    let [diagnostic] = front.diagnostics() else {
        panic!("the signature is only missing `fn`")
    };
    assert_eq!(diagnostic.code, codes::EXPECTED_TOKEN);
    assert_eq!(diagnostic.message.as_ref(), "expected `fn`");
    assert_eq!(
        diagnostic.primary.location,
        Location::Point(TextSize::new(source.find('f').unwrap() as u32))
    );

    let source = "fn f() { x // tail";
    let front = parsed(source);
    let [diagnostic] = front.diagnostics() else {
        panic!("the block is only missing a closing brace")
    };
    assert_eq!(diagnostic.code, codes::EXPECTED_TOKEN);
    assert_eq!(diagnostic.message.as_ref(), "expected `}`");
    assert_eq!(
        diagnostic.primary.location,
        Location::Point(TextSize::new(source.len() as u32))
    );

    let [ParseEvidence::Recovery(recovery)] = front.parse().evidence() else {
        panic!("the parse retains the missing closer evidence")
    };
    let ParseAnchor::Gap(gap) = recovery.anchor else {
        panic!("the closer is absent from a raw gap")
    };
    let start = raw_boundary(&front, gap.trivia_start()).to_usize();
    let end = raw_boundary(&front, gap.trivia_end()).to_usize();
    assert_eq!(&source[start..end], " // tail");
}

#[test]
fn raw_ranges_map_across_multibyte_source_and_parser_cascades_are_suppressed() {
    let front = parsed("fn f() { a € + b }");
    let [diagnostic] = front.diagnostics() else {
        panic!("the lexer owns the unknown character")
    };
    assert_eq!(diagnostic.code, codes::UNKNOWN_CHARACTER);
    assert_eq!(location_text(&front, diagnostic.primary.location), "€");
    assert!(matches!(
        front.parse().evidence(),
        [ParseEvidence::Recovery(_)]
    ));

    let front = parsed("fn f() {\n  a ;\n  b\n}");
    assert_eq!(diagnostic_codes(&front), [codes::UNKNOWN_PUNCTUATION]);
    assert_eq!(front.parse().evidence().len(), 2);
}

#[test]
fn an_error_in_a_skipped_effect_does_not_suppress_a_valid_cause() {
    let front = parsed(": €");
    assert_eq!(
        diagnostic_codes(&front),
        [codes::EXPECTED_ITEM, codes::UNKNOWN_CHARACTER]
    );
    let parser = &front.diagnostics()[0];
    assert_eq!(location_text(&front, parser.primary.location), ":");
    let [skipped] = &*parser.secondary else {
        panic!("the parser diagnostic retains its skipped effect")
    };
    assert_eq!(location_text(&front, skipped.location), ": €");
}

#[test]
fn diagnostics_are_globally_sorted_with_stable_ties() {
    // The lexer observes the later `€` before parser diagnostics are lowered,
    // so source sorting must move the missing `:` ahead of it.
    let front = parsed("fn f(a) { € }");
    assert_eq!(
        diagnostic_codes(&front),
        [codes::EXPECTED_TOKEN, codes::UNKNOWN_CHARACTER]
    );
    assert_eq!(front.diagnostics()[0].message.as_ref(), "expected `:`");

    // Both facts sit at EOF; stable sorting retains parser observation order.
    let front = parsed("fn f(a: int");
    assert_eq!(front.diagnostics().len(), 2);
    assert_eq!(front.diagnostics()[0].message.as_ref(), "expected `)`");
    assert_eq!(front.diagnostics()[1].message.as_ref(), "expected `{`");
    assert_eq!(
        front.diagnostics()[0].primary.location,
        front.diagnostics()[1].primary.location
    );
}

#[test]
fn numeric_canonicalization_facts_form_one_diagnostic() {
    let front = parsed("fn f() { 1E+05 }");
    let [diagnostic] = front.diagnostics() else {
        panic!("one literal has one canonicalization diagnostic")
    };
    assert_eq!(diagnostic.code, codes::NONCANONICAL_NUMBER);
    assert_eq!(location_text(&front, diagnostic.primary.location), "E");
    assert_eq!(
        diagnostic.primary.message.as_deref(),
        Some("exponent marker must be lowercase `e`")
    );
    assert_eq!(diagnostic.secondary.len(), 2);
    assert_eq!(location_text(&front, diagnostic.secondary[0].location), "+");
    assert_eq!(location_text(&front, diagnostic.secondary[1].location), "0");

    let front = parsed("fn f() { 01_ }");
    let [diagnostic] = front.diagnostics() else {
        panic!("both spelling facts form one diagnostic")
    };
    assert_eq!(diagnostic.code, codes::NONCANONICAL_NUMBER);
    assert_eq!(diagnostic.secondary.len(), 1);

    let front = parsed("fn f() { 01u32 }");
    assert_eq!(
        diagnostic_codes(&front),
        [codes::NONCANONICAL_NUMBER, codes::UNKNOWN_SUFFIX]
    );

    let front = parsed("fn f() { 1_e }");
    assert_eq!(
        diagnostic_codes(&front),
        [codes::NONCANONICAL_NUMBER, codes::MISSING_EXPONENT]
    );
}

#[test]
fn independent_same_token_facts_remain_independent() {
    let front = parsed(r#"fn f() { "\q\q" }"#);
    assert_eq!(
        diagnostic_codes(&front),
        [codes::UNKNOWN_ESCAPE, codes::UNKNOWN_ESCAPE]
    );
    assert_ne!(
        front.diagnostics()[0].primary.location,
        front.diagnostics()[1].primary.location
    );
}

const FRAGMENTS: &[&str] = &[
    "fn", "let", "if", "else", "return", "x", "_", "Δ", "0", "01_", "1E+05", "1e", r#""\q""#,
    "'ab'", "(", ")", "{", "}", ",", ":", "=", "+", "-", ";", " ", "\n", "// c", "€",
];

fn source() -> impl Strategy<Value = String> {
    proptest::collection::vec(prop::sample::select(FRAGMENTS), 0..64)
        .prop_map(|pieces| pieces.concat())
}

proptest! {
    #[test]
    fn every_canonical_location_is_valid(source in source()) {
        let front = parse_source(source.into_boxed_str()).expect("generated sources fit in u32");
        let source = front.source();
        let mut previous = None;
        for diagnostic in front.diagnostics() {
            prop_assert_eq!(diagnostic.severity, Severity::Error);
            let key = (
                diagnostic.primary.location.start().to_u32(),
                diagnostic.primary.location.end().to_u32(),
            );
            if let Some(previous) = previous {
                prop_assert!(previous <= key, "diagnostics are not source sorted");
            }
            previous = Some(key);

            for label in std::iter::once(&diagnostic.primary).chain(&*diagnostic.secondary) {
                let start = label.location.start().to_usize();
                let end = label.location.end().to_usize();
                prop_assert!(start <= end && end <= source.len());
                prop_assert!(source.is_char_boundary(start));
                prop_assert!(source.is_char_boundary(end));
                if let Location::Point(point) = label.location {
                    prop_assert_eq!(point.to_usize(), start);
                    prop_assert_eq!(start, end);
                }
            }
        }
    }
}
