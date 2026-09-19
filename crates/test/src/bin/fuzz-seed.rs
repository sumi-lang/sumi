//! Seed every fuzz target's corpus under `fuzz/corpus/` from the file-based
//! cases, as `cargo run -p sumi-test --bin fuzz-seed`. `lex`, `parse`,
//! `check`, and `run` read a case as it is; `edit` reads the seeds
//! `edit_seeds` writes, one per edit kind. The corpus directories are
//! untracked; a seed that adds no coverage over what is already there is
//! simply not kept.

use std::fs;
use std::path::{Path, PathBuf};

use sumi_test::{corpus, edit_seeds};

/// The fuzz targets: every one but `edit` reads a case as it is.
const TARGETS: [&str; 5] = ["lex", "parse", "check", "run", "edit"];

fn main() {
    let cases = corpus::cases();
    assert!(
        !cases.is_empty(),
        "no cases under {}",
        corpus::root().display()
    );
    let out = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fuzz/corpus");
    for dir in TARGETS.map(|target| out.join(target)) {
        fs::create_dir_all(&dir)
            .unwrap_or_else(|error| panic!("cannot create {}: {error}", dir.display()));
    }
    let write = |path: PathBuf, bytes: &[u8]| {
        fs::write(&path, bytes)
            .unwrap_or_else(|error| panic!("cannot write {}: {error}", path.display()));
    };
    for case in &cases {
        let source = fs::read_to_string(case.join("case.sumi"))
            .unwrap_or_else(|error| panic!("cannot read {}: {error}", case.display()));
        let name = case
            .strip_prefix(corpus::root())
            .expect("under the corpus")
            .components()
            .map(|component| component.as_os_str().to_string_lossy())
            .collect::<Vec<_>>()
            .join("-");
        for target in TARGETS {
            let dir = out.join(target);
            if target == "edit" {
                for (kind, seed) in edit_seeds(&source).iter().enumerate() {
                    write(dir.join(format!("{name}-{kind}")), seed);
                }
            } else {
                write(dir.join(&name), source.as_bytes());
            }
        }
    }
    println!("seeded {} cases into fuzz/corpus/", cases.len());
}
