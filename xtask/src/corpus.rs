//! The file-based corpus under `tests/corpus`: every case directory.

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
