//! Every diagnostic code the registry declares is shown by a corpus case:
//! some snapshot under `tests/corpus` reports it. A code no case reports
//! has no witness in the repository and no example in the reference
//! chapter, which takes its examples from the same snapshots.

use std::fs;
use std::path::Path;

use sumi_diagnostics::DiagnosticCode;

/// Every snapshot under `dir`, concatenated.
fn snapshots(dir: &Path, out: &mut String) {
    let mut entries: Vec<_> = fs::read_dir(dir)
        .unwrap_or_else(|error| panic!("cannot read {}: {error}", dir.display()))
        .map(|entry| entry.expect("directory entry").path())
        .collect();
    entries.sort();
    for path in entries {
        if path.is_dir() {
            snapshots(&path, out);
        } else if path
            .extension()
            .is_some_and(|extension| extension == "snap")
        {
            out.push_str(&fs::read_to_string(&path).expect("a snapshot is UTF-8"));
        }
    }
}

#[test]
fn every_code_is_shown_by_a_corpus_case() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/corpus");
    let mut text = String::new();
    snapshots(&root, &mut text);
    assert!(!text.is_empty(), "no snapshots under {}", root.display());
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
