//! Seeds fuzz target corpora under `fuzz/corpus/` from the file-based cases. An optional target
//! limits the output to that target.

use std::fs;
use std::path::{Path, PathBuf};

use sumi_test::{corpus, edit_seeds};

const TARGETS: [&str; 5] = ["lex", "parse", "check", "run", "edit"];

fn main() {
    let cases = corpus::cases();
    assert!(
        !cases.is_empty(),
        "no cases under {}",
        corpus::root().display()
    );
    let requested = std::env::args().nth(1);
    let targets: Vec<&str> = match requested.as_deref() {
        Some(target) => {
            assert!(TARGETS.contains(&target), "unknown fuzz target {target:?}");
            vec![target]
        }
        None => TARGETS.to_vec(),
    };
    let out = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../fuzz/corpus");
    for target in &targets {
        let dir = out.join(target);
        fs::create_dir_all(&dir)
            .unwrap_or_else(|error| panic!("cannot create {}: {error}", dir.display()));
    }
    let write = |path: PathBuf, bytes: &[u8]| {
        fs::write(&path, bytes)
            .unwrap_or_else(|error| panic!("cannot write {}: {error}", path.display()));
    };
    for case in &cases {
        let source = fs::read_to_string(case.join("case.su"))
            .unwrap_or_else(|error| panic!("cannot read {}: {error}", case.display()));
        let name = case
            .strip_prefix(corpus::root())
            .expect("under the corpus")
            .components()
            .map(|component| component.as_os_str().to_string_lossy())
            .collect::<Vec<_>>()
            .join("-");
        for target in &targets {
            let dir = out.join(target);
            if *target == "edit" {
                for (kind, seed) in edit_seeds(&source).iter().enumerate() {
                    write(dir.join(format!("{name}-{kind}")), seed);
                }
            } else {
                write(dir.join(&name), source.as_bytes());
            }
        }
    }
    println!(
        "seeded {} cases for {} target(s) into fuzz/corpus/",
        cases.len(),
        targets.len()
    );
}
