//! Every diagnostic code must appear in some corpus snapshot. A code no snapshot reports fails this
//! test.

use std::fs;

use sumi_frontend::DiagnosticCode;
use sumi_test::corpus::{self, Stage};

#[test]
fn every_code_is_shown_by_a_corpus_case() {
    let mut text = String::new();
    for case in corpus::cases() {
        for stage in Stage::ALL {
            if let Ok(snapshot) = fs::read_to_string(case.join(stage.filename())) {
                text.push_str(&snapshot);
            }
        }
    }
    assert!(
        !text.is_empty(),
        "no snapshots under {}",
        corpus::root().display()
    );
    let codes = sumi_frontend::codes::ALL
        .iter()
        .chain(sumi_hir::codes::ALL.iter());
    let unshown: Vec<String> = codes
        .filter(|code| !text.contains(&format!("[{code}]")))
        .map(DiagnosticCode::to_string)
        .collect();
    assert!(
        unshown.is_empty(),
        "no corpus snapshot reports:\n  {}",
        unshown.join("\n  ")
    );
}
