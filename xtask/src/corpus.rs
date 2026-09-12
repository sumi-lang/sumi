//! The file-based corpus under `tests/corpus`, read by the tasks: every
//! case directory, and the diagnostics each case's snapshots show.

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

/// Every directory under `dir` that holds a `case.sumi`, recursively, in
/// path order; a directory that holds one is a case and is not descended
/// into.
pub fn cases(dir: &Path, out: &mut Vec<PathBuf>) -> Result<(), String> {
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

/// The corpus case that shows one diagnostic code.
#[derive(Debug)]
pub struct Example {
    /// The case directory, relative to the workspace root.
    pub case: String,
    pub source: String,
    /// The rendered diagnostics of that code, as the snapshot shows them.
    pub diagnostics: String,
}

/// The snapshot sections that render diagnostics, one per stage.
const SECTIONS: [(&str, &str); 2] = [
    ("frontend.snap", "== diagnostics =="),
    ("hir.snap", "== semantic diagnostics =="),
];

/// For every code some case shows, the case showing it among the fewest
/// other diagnostics, earliest in path order among equals: the one that
/// explains the code best.
pub fn examples(root: &Path) -> Result<BTreeMap<String, Example>, String> {
    let corpus = root.join("tests/corpus");
    let mut dirs = Vec::new();
    cases(&corpus, &mut dirs)?;
    let mut best: BTreeMap<String, (usize, Example)> = BTreeMap::new();
    for dir in dirs {
        let case = dir
            .strip_prefix(root)
            .expect("under the root")
            .to_string_lossy()
            .replace('\\', "/");
        for (file, header) in SECTIONS {
            let path = dir.join(file);
            let Ok(snapshot) = fs::read_to_string(&path) else {
                continue;
            };
            let blocks = blocks(&snapshot, header);
            let mut by_code: BTreeMap<&str, String> = BTreeMap::new();
            for block in &blocks {
                let code = block
                    .split_once('[')
                    .and_then(|(_, rest)| rest.split_once(']'))
                    .map(|(code, _)| code)
                    .ok_or_else(|| {
                        format!("{}: diagnostic without a code: {block}", path.display())
                    })?;
                by_code.entry(code).or_default().push_str(block);
            }
            for (code, diagnostics) in by_code {
                let better = best
                    .get(code)
                    .is_none_or(|(count, _)| blocks.len() < *count);
                if better {
                    let source = fs::read_to_string(dir.join("case.sumi"))
                        .map_err(|error| format!("reading {}: {error}", dir.display()))?;
                    best.insert(
                        code.to_owned(),
                        (
                            blocks.len(),
                            Example {
                                case: case.clone(),
                                source,
                                diagnostics,
                            },
                        ),
                    );
                }
            }
        }
    }
    Ok(best
        .into_iter()
        .map(|(code, (_, example))| (code, example))
        .collect())
}

/// The diagnostics of a snapshot section, each a header line and its
/// indented continuation lines, every line newline-terminated.
fn blocks(snapshot: &str, header: &str) -> Vec<String> {
    let mut blocks = Vec::new();
    let mut inside = false;
    for line in snapshot.lines() {
        if line == header {
            inside = true;
            continue;
        }
        if !inside {
            continue;
        }
        if line.starts_with("== ") || line.is_empty() {
            inside = false;
            continue;
        }
        if line.starts_with(' ') {
            let block: &mut String = blocks.last_mut().expect("a continuation follows a header");
            block.push_str(line);
        } else {
            blocks.push(line.to_owned());
        }
        blocks.last_mut().expect("pushed").push('\n');
    }
    blocks
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn blocks_take_one_section_with_continuations() {
        let snapshot = "== tree ==\nx\n\n== diagnostics ==\nerror[a/b] 1:1: m\n  at 1:2: n\nerror[a/c] 1:3: o\n\n== fixed ==\nerror[a/d] 1:1: not here\n";
        let found = blocks(snapshot, "== diagnostics ==");
        assert_eq!(
            found,
            ["error[a/b] 1:1: m\n  at 1:2: n\n", "error[a/c] 1:3: o\n"]
        );
        assert!(blocks(snapshot, "== semantic diagnostics ==").is_empty());
    }
}
