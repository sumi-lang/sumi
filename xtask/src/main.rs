//! Repository maintenance tasks, run as `cargo xtask <task>`.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

const USAGE: &str = "usage: cargo xtask fuzz-seed

  fuzz-seed         seed every fuzz target's corpus from tests/corpus";

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let args: Vec<&str> = args.iter().map(String::as_str).collect();
    let result = match args.as_slice() {
        ["fuzz-seed"] => fuzz_seed(),
        _ => Err(USAGE.to_owned()),
    };
    match result {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("error: {error}");
            ExitCode::FAILURE
        }
    }
}

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("xtask sits inside the workspace")
        .to_path_buf()
}

/// Every directory under `dir` that holds a `case.sumi`, recursively, in
/// path order; a directory that holds one is a case and is not descended
/// into.
fn cases(dir: &Path, out: &mut Vec<PathBuf>) -> Result<(), String> {
    let mut entries: Vec<PathBuf> = fs::read_dir(dir)
        .map_err(|error| format!("reading {}: {error}", dir.display()))?
        .map(|entry| entry.map(|entry| entry.path()))
        .collect::<Result<_, _>>()
        .map_err(|error| format!("reading {}: {error}", dir.display()))?;
    entries.retain(|path| path.is_dir());
    entries.sort();
    for path in entries {
        if path.join("case.sumi").is_file() {
            out.push(path);
        } else {
            cases(&path, out)?;
        }
    }
    Ok(())
}

/// Seed every fuzz target's corpus under `fuzz/corpus/` from the file-based
/// cases. `lex`, `parse`, `check`, and `run` read a case as it is. `edit` reads three header
/// bytes before the source — the edit kind, then the significant token it
/// lands on — so each case is written once per edit kind. The corpus
/// directories are untracked; a seed that adds no coverage over what is
/// already there is simply not kept.
fn fuzz_seed() -> Result<(), String> {
    let root = workspace_root();
    let corpus = root.join("tests/corpus");
    let mut found = Vec::new();
    cases(&corpus, &mut found)?;
    if found.is_empty() {
        return Err(format!("no cases under {}", corpus.display()));
    }
    let out = root.join("fuzz/corpus");
    for target in ["lex", "parse", "edit", "check", "run"] {
        fs::create_dir_all(out.join(target))
            .map_err(|error| format!("creating fuzz/corpus/{target}: {error}"))?;
    }
    for case in &found {
        let source = fs::read(case.join("case.sumi"))
            .map_err(|error| format!("reading {}: {error}", case.display()))?;
        let name = case
            .strip_prefix(&corpus)
            .expect("under the corpus")
            .components()
            .map(|component| component.as_os_str().to_string_lossy())
            .collect::<Vec<_>>()
            .join("-");
        let write = |path: PathBuf, bytes: &[u8]| {
            fs::write(&path, bytes).map_err(|error| format!("writing {}: {error}", path.display()))
        };
        write(out.join("lex").join(&name), &source)?;
        write(out.join("parse").join(&name), &source)?;
        write(out.join("check").join(&name), &source)?;
        write(out.join("run").join(&name), &source)?;
        for kind in 0u8..4 {
            let mut seed = vec![kind, 1, 0];
            seed.extend_from_slice(&source);
            write(out.join("edit").join(format!("{name}-{kind}")), &seed)?;
        }
    }
    println!("seeded {} cases into fuzz/corpus/", found.len());
    Ok(())
}
