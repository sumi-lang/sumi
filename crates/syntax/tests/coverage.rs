//! Coverage: the corpus and the program generator each reach every node kind and child the grammar
//! allows. A construct neither reaches has no snapshot and no property behind it.

use std::fs;

use sumi_test::coverage::Coverage;
use sumi_test::{Programs, corpus, front};

fn record(coverage: &mut Coverage, source: &str) {
    let front = front(source);
    coverage.record(&front.lexed, front.parse.tree());
}

fn assert_covered(coverage: &Coverage, body: &str) {
    let missing = coverage.missing();
    assert!(
        missing.is_empty(),
        "{body} never shows:\n  {}",
        missing.join("\n  ")
    );
}

#[test]
fn the_corpus_covers_the_grammar() {
    let cases = corpus::cases();
    assert!(
        !cases.is_empty(),
        "no cases under {}",
        corpus::root().display()
    );
    let mut coverage = Coverage::new();
    for case in cases {
        let source = fs::read_to_string(case.join("case.su")).expect("a case is UTF-8");
        record(&mut coverage, &source);
    }
    assert_covered(&coverage, "the corpus");
}

#[test]
fn generated_programs_cover_the_grammar() {
    let mut coverage = Coverage::new();
    for source in Programs::new(0).take(256) {
        record(&mut coverage, &source);
    }
    assert_covered(&coverage, "the program generator");
}
