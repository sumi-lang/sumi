//! Grammar coverage: the file-based corpus and the program generator each
//! reach every node kind and every child `sumi.grammar` allows, present
//! and, where the rule permits, absent. A construct the grammar admits
//! that neither reaches has no snapshot and no property behind it, and
//! every generated program is one the properties and the scorecard measure.

use std::fs;
use std::path::{Path, PathBuf};

use sumi_test::coverage::Coverage;
use sumi_test::{Programs, front};

/// Every directory under `dir` holding a `case.sumi`, recursively.
fn cases(dir: &Path, out: &mut Vec<PathBuf>) {
    let mut entries: Vec<PathBuf> = fs::read_dir(dir)
        .unwrap_or_else(|error| panic!("cannot read {}: {error}", dir.display()))
        .map(|entry| entry.expect("directory entry").path())
        .filter(|path| path.is_dir())
        .collect();
    entries.sort();
    for path in entries {
        if path.join("case.sumi").is_file() {
            out.push(path);
        } else {
            cases(&path, out);
        }
    }
}

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
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/corpus");
    let mut found = Vec::new();
    cases(&root, &mut found);
    assert!(!found.is_empty(), "no cases under {}", root.display());
    let mut coverage = Coverage::new();
    for case in found {
        let source = fs::read_to_string(case.join("case.sumi")).expect("a case is UTF-8");
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
