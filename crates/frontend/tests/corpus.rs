//! The file-based corpus: every `tests/corpus/**/*.sumi` under the
//! workspace root, run through the frontend and compared with the `.snap`
//! beside it. A snapshot records the tree, with `!` on every node that
//! contains an error, the parser's evidence, the diagnostics, the source
//! after every fix, and the normalized source where it differs. Run with
//! `UPDATE_EXPECT=1` to rewrite the snapshots, then review the diff; a new
//! `.sumi` gets its first snapshot the same way.

use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};

use sumi_format::normalize;
use sumi_frontend::{
    Applicability, Diagnostic, FileId, Location, Place, Severity, TextEdit, parse_source,
};
use sumi_lexer::LexedFile;
use sumi_syntax::{
    NodeIdx, ParseAnchor, ParseEvidence, ParseExpected, ParseRecoveryKind, RawIdx, SyntaxTree,
    raw_boundary,
};
use sumi_text::{LineIndex, TextSize};

const UPDATE: &str = "UPDATE_EXPECT";

fn corpus_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/corpus")
}

/// Every file under `dir` with `extension`, recursively, in path order.
fn files(dir: &Path, extension: &str, out: &mut Vec<PathBuf>) {
    let mut entries: Vec<PathBuf> = fs::read_dir(dir)
        .unwrap_or_else(|error| panic!("cannot read {}: {error}", dir.display()))
        .map(|entry| entry.expect("directory entry").path())
        .collect();
    entries.sort();
    for path in entries {
        if path.is_dir() {
            files(&path, extension, out);
        } else if path.extension().is_some_and(|found| found == extension) {
            out.push(path);
        }
    }
}

#[test]
fn every_case_matches_its_snapshot() {
    let root = corpus_dir();
    let mut cases = Vec::new();
    files(&root, "sumi", &mut cases);
    assert!(!cases.is_empty(), "no cases under {}", root.display());
    let update = std::env::var_os(UPDATE).is_some();
    let relative = |path: &Path| {
        path.strip_prefix(&root)
            .expect("under the corpus")
            .display()
            .to_string()
    };

    let mut failures = Vec::new();
    for case in &cases {
        let source = fs::read_to_string(case).expect("a case is UTF-8");
        let actual = snapshot(&source);
        let snap = case.with_extension("snap");
        let expected = fs::read_to_string(&snap).ok();
        if expected.as_deref() == Some(actual.as_str()) {
            continue;
        }
        if update {
            fs::write(&snap, &actual).expect("snapshots are writable");
            continue;
        }
        failures.push(format!(
            "{}:\n{}",
            relative(case),
            diff(expected.as_deref().unwrap_or(""), &actual)
        ));
    }

    let mut snaps = Vec::new();
    files(&root, "snap", &mut snaps);
    for snap in snaps {
        if !snap.with_extension("sumi").exists() {
            failures.push(format!(
                "{}: a snapshot with no case beside it",
                relative(&snap)
            ));
        }
    }

    assert!(
        failures.is_empty(),
        "{} of {} corpus cases differ from their snapshots; run with {UPDATE}=1 to rewrite them, \
         then review the diff\n\n{}",
        failures.len(),
        cases.len(),
        failures.join("\n")
    );
}

/// The snapshot of one case.
fn snapshot(source: &str) -> String {
    let parsed = parse_source(FileId::new(0), source.into()).expect("corpus cases fit in u32");
    let lexed = parsed.lexed();
    let parse = parsed.parse();
    let index = LineIndex::new(source);
    let mut out = String::from("== tree ==\n");
    dump(parse.tree(), lexed, source, &mut out);

    if !parse.evidence().is_empty() {
        out.push_str("\n== evidence ==\n");
        for evidence in parse.evidence() {
            let at = raw_boundary(lexed, evidence_token(evidence)).to_u32();
            writeln!(out, "{} at {at}", evidence_name(evidence)).expect("writing to a string");
        }
    }

    if !parsed.diagnostics().is_empty() {
        out.push_str("\n== diagnostics ==\n");
        for diagnostic in parsed.diagnostics() {
            render(diagnostic, &index, source, &mut out);
        }
    }

    let mut edits: Vec<&TextEdit> = parsed
        .diagnostics()
        .iter()
        .filter_map(|diagnostic| diagnostic.fix.as_ref())
        .flat_map(|fix| fix.edits.iter())
        .collect();
    if !edits.is_empty() {
        // Every fix applies to the original source; where two of them
        // overlap, the later one is left out and the header says so.
        edits.sort_by_key(|edit| (edit.range().start(), edit.range().end()));
        let mut applied: Vec<&TextEdit> = Vec::new();
        let mut skipped = 0usize;
        for edit in edits {
            let overlaps = applied
                .last()
                .is_some_and(|previous| previous.range().end() > edit.range().start());
            if overlaps {
                skipped += 1;
            } else {
                applied.push(edit);
            }
        }
        let mut fixed = source.to_owned();
        for edit in applied.iter().rev() {
            let range = edit.range();
            fixed.replace_range(
                range.start().to_usize()..range.end().to_usize(),
                edit.replacement(),
            );
        }
        if skipped == 0 {
            out.push_str("\n== fixed ==\n");
        } else {
            writeln!(out, "\n== fixed ({skipped} overlapping edits skipped) ==")
                .expect("writing to a string");
        }
        push_text(&mut out, &fixed);
    }

    let normalized = normalize(source, lexed, parse);
    if normalized != source {
        out.push_str("\n== normalized ==\n");
        push_text(&mut out, &normalized);
    }
    out
}

/// Append `text` as a section body, ending on a line break.
fn push_text(out: &mut String, text: &str) {
    out.push_str(text);
    if !text.ends_with('\n') {
        out.push('\n');
    }
}

/// Assert the tree invariants and render one line per node: `Kind
/// start..end` byte ranges, indented by depth, `!` after the kind of a node
/// that contains an error, and the text of childless nodes appended.
fn dump(tree: &SyntaxTree, lexed: &LexedFile, source: &str, out: &mut String) {
    let mut visited = 0usize;
    render_node(tree, lexed, source, tree.root(), 0, out, &mut visited);
    assert_eq!(visited, tree.len(), "extents must partition the tree");
}

fn render_node(
    tree: &SyntaxTree,
    lexed: &LexedFile,
    source: &str,
    node: NodeIdx,
    depth: usize,
    out: &mut String,
    visited: &mut usize,
) {
    *visited += 1;
    let first = tree.first_token(node);
    let end = tree.end_token(node);
    assert!(first <= end, "node {node:?} has a backwards token range");

    let range = tree.byte_range(node, lexed);
    let (from, to) = (range.start().to_u32(), range.end().to_u32());
    let mark = if tree.has_error(node) { "!" } else { "" };
    write!(
        out,
        "{:indent$}{:?}{mark} {from}..{to}",
        "",
        tree.kind(node),
        indent = depth * 2
    )
    .expect("writing to a string");
    if tree.children(node).next().is_none() {
        write!(out, " {:?}", &source[from as usize..to as usize]).expect("writing to a string");
    }
    out.push('\n');

    // The tree yields children last first; the dump reads in source order.
    let mut children: Vec<NodeIdx> = tree.children(node).collect();
    children.reverse();
    let mut previous_end = first;
    for child in children {
        assert!(
            tree.first_token(child) >= previous_end,
            "children must be ordered and disjoint"
        );
        assert!(
            tree.end_token(child) <= end,
            "a child must stay inside its parent"
        );
        previous_end = tree.end_token(child);
        render_node(tree, lexed, source, child, depth + 1, out, visited);
    }
}

fn evidence_name(evidence: &ParseEvidence) -> String {
    match evidence {
        ParseEvidence::Recovery(recovery) => match recovery.kind {
            ParseRecoveryKind::Expected(expected) => match expected {
                ParseExpected::Item => "ExpectedItem".into(),
                ParseExpected::Statement => "ExpectedStatement".into(),
                ParseExpected::Expression => "ExpectedExpression".into(),
                ParseExpected::Name => "ExpectedName".into(),
                ParseExpected::Type => "ExpectedType".into(),
                ParseExpected::Token(kind) => format!("Expected({kind:?})"),
                ParseExpected::Closer { kind, .. } => format!("Expected({kind:?})"),
                ParseExpected::Boundary => "ExpectedBoundary".into(),
            },
            kind => format!("{kind:?}"),
        },
        ParseEvidence::Violation(violation) => format!("{:?}", violation.kind),
    }
}

fn evidence_token(evidence: &ParseEvidence) -> RawIdx {
    match evidence {
        ParseEvidence::Recovery(recovery) => match recovery.anchor {
            ParseAnchor::Gap(gap) => gap.trivia_end(),
            ParseAnchor::Tokens(range) => range.start(),
        },
        ParseEvidence::Violation(violation) => violation.range.start(),
    }
}

/// One diagnostic: its severity, code, place, and message on the first
/// line, then its labels, notes, and fix indented under it.
fn render(diagnostic: &Diagnostic, index: &LineIndex, source: &str, out: &mut String) {
    let severity = match diagnostic.severity {
        Severity::Error => "error",
        Severity::Warning => "warning",
        Severity::Info => "info",
        Severity::Hint => "hint",
    };
    writeln!(
        out,
        "{severity}[{}/{}] {}: {}",
        diagnostic.code.group().as_str(),
        diagnostic.code.name(),
        place(index, source, diagnostic.primary.location),
        diagnostic.message
    )
    .expect("writing to a string");
    if let Some(message) = &diagnostic.primary.message {
        writeln!(out, "  primary: {message}").expect("writing to a string");
    }
    for label in &diagnostic.secondary {
        write!(out, "  at {}", place(index, source, label.location)).expect("writing to a string");
        if let Some(message) = &label.message {
            write!(out, ": {message}").expect("writing to a string");
        }
        out.push('\n');
    }
    for note in &diagnostic.notes {
        writeln!(out, "  note: {note}").expect("writing to a string");
    }
    if let Some(fix) = &diagnostic.fix {
        let applicability = match fix.applicability {
            Applicability::Safe => "safe",
            Applicability::MaybeIncorrect => "maybe incorrect",
        };
        writeln!(out, "  fix ({applicability}): {}", fix.message).expect("writing to a string");
        for edit in &fix.edits {
            let range = edit.range();
            let location = if range.start() == range.end() {
                Location::point(FileId::new(0), range.start())
            } else {
                Location::range(sumi_frontend::Span::new(FileId::new(0), range))
            };
            writeln!(
                out,
                "    {} -> {:?}",
                place(index, source, location),
                edit.replacement()
            )
            .expect("writing to a string");
        }
    }
}

/// A location as `line:col`, one-based with byte columns; a range as
/// `start..end` followed by its text.
fn place(index: &LineIndex, source: &str, location: Location) -> String {
    let at = |offset: TextSize| {
        let position = index.line_col(offset);
        format!("{}:{}", position.line + 1, position.col + 1)
    };
    match location.place {
        Place::Point(offset) => at(offset),
        Place::Range(range) => format!(
            "{}..{} {:?}",
            at(range.start()),
            at(range.end()),
            range.text(source)
        ),
    }
}

/// A line diff of `expected` against `actual`, with two lines of context.
fn diff(expected: &str, actual: &str) -> String {
    let old: Vec<&str> = expected.lines().collect();
    let new: Vec<&str> = actual.lines().collect();
    // Longest common subsequence by dynamic programming: snapshots are
    // short enough that the table is cheap.
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
        let near = changed.iter().any(|&change| change.abs_diff(index) <= 2);
        if !near {
            continue;
        }
        if last_shown.is_some_and(|last: usize| last + 1 != index) {
            out.push_str("  ...\n");
        }
        writeln!(out, "  {tag} {line}").expect("writing to a string");
        last_shown = Some(index);
    }
    out
}
