//! Shared file mechanics only; each integration test owns its stage's renderer.

use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Stage {
    Frontend,
    Hir,
    Eval,
}

impl Stage {
    fn filename(self) -> &'static str {
        match self {
            Self::Frontend => "frontend.snap",
            Self::Hir => "hir.snap",
            Self::Eval => "eval.snap",
        }
    }
    fn update(self) -> &'static str {
        match self {
            Self::Frontend => "UPDATE_FRONTEND",
            Self::Hir => "UPDATE_HIR",
            Self::Eval => "UPDATE_EVAL",
        }
    }
    /// The name a `stages` line spells; the frontend needs no selection.
    fn name(self) -> Option<&'static str> {
        match self {
            Self::Frontend => None,
            Self::Hir => Some("hir"),
            Self::Eval => Some("eval"),
        }
    }
}

/// Sorted leaf-case discovery, also used to find orphan products and metadata.
fn directories_holding(dir: &Path, file: &str, out: &mut Vec<PathBuf>) {
    let mut entries: Vec<_> = fs::read_dir(dir)
        .unwrap_or_else(|error| panic!("cannot read {}: {error}", dir.display()))
        .map(|entry| entry.expect("directory entry").path())
        .filter(|path| path.is_dir())
        .collect();
    entries.sort();
    for path in entries {
        if path.join(file).is_file() {
            out.push(path);
        } else {
            directories_holding(&path, file, out);
        }
    }
}

/// `stages` is deliberately a list of stage names, one per line, not a
/// general configuration language. Frontend coverage is unconditional.
/// Expected files never select a stage.
fn stage_selected(case: &Path, stage: Stage) -> Result<bool, String> {
    let Some(name) = stage.name() else {
        return Ok(true);
    };
    match fs::read_to_string(case.join("stages")) {
        Ok(text) => {
            let mut selected = false;
            for line in text.lines().map(str::trim).filter(|line| !line.is_empty()) {
                match line {
                    "hir" | "eval" => selected |= line == name,
                    other => {
                        return Err(format!(
                            "{}: stages lists `hir` and `eval`, one per line, not `{other}`",
                            case.display()
                        ));
                    }
                }
            }
            Ok(selected)
        }
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(false),
        Err(error) => Err(format!("{}: {error}", case.join("stages").display())),
    }
}

pub fn check(stage: Stage, snapshot: impl Fn(&str) -> String) {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/corpus");
    verify(
        &root,
        stage,
        std::env::var_os(stage.update()).is_some(),
        snapshot,
    )
    .unwrap_or_else(|error| panic!("{error}"));
}

/// Kept separate from environment lookup so coverage/update contracts are testable.
pub fn verify(
    root: &Path,
    stage: Stage,
    update: bool,
    snapshot: impl Fn(&str) -> String,
) -> Result<(), String> {
    let mut cases = Vec::new();
    directories_holding(root, "case.sumi", &mut cases);
    if cases.is_empty() {
        return Err(format!("no cases under {}", root.display()));
    }
    let mut failures = Vec::new();
    let mut selected = 0;
    for case in &cases {
        let path = case.join(stage.filename());
        if !stage_selected(case, stage)? {
            if path.exists() {
                failures.push(format!(
                    "{}: snapshot for an unselected stage",
                    path.display()
                ));
            }
            continue;
        }
        selected += 1;
        let source = fs::read_to_string(case.join("case.sumi")).expect("a case is UTF-8");
        let actual = snapshot(&source);
        let expected = match fs::read_to_string(&path) {
            Ok(text) => Some(text),
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => None,
            Err(error) => return Err(format!("{}: {error}", path.display())),
        };
        if expected.as_deref() == Some(actual.as_str()) {
            continue;
        }
        if update {
            fs::write(&path, &actual).expect("snapshots are writable");
        } else {
            failures.push(format!(
                "{} ({}):\n{}",
                path.strip_prefix(root).unwrap().display(),
                if expected.is_none() {
                    "missing snapshot"
                } else {
                    "snapshot differs"
                },
                diff(expected.as_deref().unwrap_or(""), &actual)
            ));
        }
    }
    for file in [stage.filename(), "stages"] {
        let mut products = Vec::new();
        directories_holding(root, file, &mut products);
        for directory in products {
            if !directory.join("case.sumi").is_file() {
                failures.push(format!(
                    "{}: {file} with no case beside it",
                    directory.display()
                ));
            }
        }
    }
    if selected == 0 {
        failures.push(format!("no cases selected for {}", stage.filename()));
    }
    if failures.is_empty() {
        return Ok(());
    }
    Err(format!(
        "{} failures across {selected} selected {} cases; run with {}=1 to update, then review the diff\n\n{}",
        failures.len(),
        stage.filename(),
        stage.update(),
        failures.join("\n")
    ))
}

/// A line diff with two context lines, shared rather than duplicating the
/// frontend runner's longest-common-subsequence implementation.
fn diff(expected: &str, actual: &str) -> String {
    let old: Vec<&str> = expected.lines().collect();
    let new: Vec<&str> = actual.lines().collect();
    let mut table = vec![vec![0usize; new.len() + 1]; old.len() + 1];
    for i in (0..old.len()).rev() {
        for j in (0..new.len()).rev() {
            table[i][j] = if old[i] == new[j] {
                table[i + 1][j + 1] + 1
            } else {
                table[i + 1][j].max(table[i][j + 1])
            };
        }
    }
    let mut lines: Vec<(char, &str)> = Vec::new();
    let (mut i, mut j) = (0, 0);
    while i < old.len() || j < new.len() {
        if i < old.len() && j < new.len() && old[i] == new[j] {
            lines.push((' ', old[i]));
            i += 1;
            j += 1;
        } else if j < new.len() && (i == old.len() || table[i][j + 1] >= table[i + 1][j]) {
            lines.push(('+', new[j]));
            j += 1;
        } else {
            lines.push(('-', old[i]));
            i += 1;
        }
    }
    let changed: Vec<usize> = lines
        .iter()
        .enumerate()
        .filter(|(_, (tag, _))| *tag != ' ')
        .map(|(index, _)| index)
        .collect();
    let mut out = String::new();
    let mut last_shown = None;
    for (index, (tag, line)) in lines.iter().enumerate() {
        if !changed.iter().any(|&change| change.abs_diff(index) <= 2) {
            continue;
        }
        if last_shown.is_some_and(|last: usize| last + 1 != index) {
            out.push_str("  ...\n");
        }
        writeln!(out, "  {tag} {line}").unwrap();
        last_shown = Some(index);
    }
    if out.is_empty() && expected != actual {
        out.push_str("  line-ending difference\n");
    }
    out
}

#[test]
fn selection_is_independent_of_snapshots_and_updates_are_stage_local() {
    let root = tempfile::tempdir().unwrap();
    let case = root.path().join("example");
    fs::create_dir(&case).unwrap();
    fs::write(case.join("case.sumi"), "source").unwrap();
    fs::write(case.join("stages"), "hir\n").unwrap();
    let render = |_: &str| "golden\n".to_owned();
    for stage in [Stage::Frontend, Stage::Hir] {
        assert!(
            verify(root.path(), stage, false, render)
                .unwrap_err()
                .contains("missing snapshot")
        );
    }
    assert!(
        verify(root.path(), Stage::Eval, false, render)
            .unwrap_err()
            .contains("no cases selected")
    );
    verify(root.path(), Stage::Frontend, true, render).unwrap();
    assert!(!case.join("hir.snap").exists());
    verify(root.path(), Stage::Hir, true, render).unwrap();
    for stage in [Stage::Frontend, Stage::Hir] {
        verify(root.path(), stage, false, render).unwrap();
    }
    fs::write(case.join("stages"), "hir\neval\n").unwrap();
    verify(root.path(), Stage::Hir, false, render).unwrap();
    assert!(
        verify(root.path(), Stage::Eval, false, render)
            .unwrap_err()
            .contains("missing snapshot")
    );
    verify(root.path(), Stage::Eval, true, render).unwrap();
    verify(root.path(), Stage::Eval, false, render).unwrap();
    fs::remove_file(case.join("eval.snap")).unwrap();
    fs::write(case.join("stages"), "hir\n").unwrap();
    fs::remove_file(case.join("hir.snap")).unwrap();
    assert!(
        verify(root.path(), Stage::Hir, false, render)
            .unwrap_err()
            .contains("missing snapshot")
    );
    verify(root.path(), Stage::Hir, true, render).unwrap();
    fs::remove_file(case.join("stages")).unwrap();
    assert!(
        verify(root.path(), Stage::Hir, false, render)
            .unwrap_err()
            .contains("unselected stage")
    );
    verify(root.path(), Stage::Frontend, false, render).unwrap();
}

#[test]
fn malformed_metadata_or_orphan_products_fail_even_in_update_mode() {
    let root = tempfile::tempdir().unwrap();
    let case = root.path().join("example");
    fs::create_dir(&case).unwrap();
    fs::write(case.join("case.sumi"), "source").unwrap();
    fs::write(case.join("stages"), "hri\n").unwrap();
    let render = |_: &str| "golden\n".to_owned();
    assert!(
        verify(root.path(), Stage::Hir, true, render)
            .unwrap_err()
            .contains("not `hri`")
    );
    fs::write(case.join("stages"), "hir\n").unwrap();
    let orphan = root.path().join("orphan");
    fs::create_dir(&orphan).unwrap();
    fs::write(orphan.join("hir.snap"), "old").unwrap();
    assert!(
        verify(root.path(), Stage::Hir, true, render)
            .unwrap_err()
            .contains("no case beside it")
    );
}

#[test]
fn diff_reports_content_and_line_ending_changes() {
    let changed = diff("same\nbefore\n", "same\nafter\n");
    assert!(changed.contains("- before"));
    assert!(changed.contains("+ after"));
    assert!(diff("same", "same\n").contains("line-ending difference"));
}
