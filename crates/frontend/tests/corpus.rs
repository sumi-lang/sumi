//! The file-based corpus: every directory under `tests/corpus` at the
//! workspace root that holds a `case.sumi`, run through the frontend and
//! compared with the `frontend.snap` beside it. A snapshot records the
//! tree, with `!` on every node that contains an error, the parser's
//! evidence, the diagnostics, the source after every fix, its header
//! naming any diagnostic that survives them, and the formatted source
//! where it differs, its header counting the items left as written and
//! naming any violation that survives formatting. A case that selects
//! `hir` leaves the tree out: `hir.snap` anchors the graph the checker
//! built by span, not every parse-tree node, so a case whose parse is the
//! point does not select `hir`. Run with `UPDATE_FRONTEND=1` to rewrite
//! the snapshots, then review the diff; a new case gets its first
//! snapshot the same way.

use std::fmt::Write as _;

use sumi_format::format;
use sumi_frontend::{Diagnostic, parse_source};
use sumi_lexer::LexedFile;
use sumi_syntax::{NodeIdx, ParseAnchor, ParseEvidence, ParseRecoveryKind, RawIdx, SyntaxTree};
use sumi_test::corpus;
use sumi_text::{LineIndex, TextEdit, TextRange, TextSize};

#[test]
fn every_case_matches_its_snapshot() {
    corpus::check(corpus::Stage::Frontend, snapshot);
}

/// The snapshot of one case.
fn snapshot(source: &str, stages: &[corpus::Stage]) -> String {
    let parsed = parse_source(source.into()).expect("corpus cases fit in u32");
    let lexed = parsed.lexed();
    let parse = parsed.parse();
    let index = LineIndex::new(source);
    let mut out = String::new();
    if stages.contains(&corpus::Stage::Hir) {
        out.push_str("tree: see hir.snap\n");
    } else {
        section(&mut out, "tree");
        dump(parse.tree(), lexed, source, &mut out);
    }

    if !parse.evidence().is_empty() {
        section(&mut out, "evidence");
        for evidence in parse.evidence() {
            let at = lexed.boundary(evidence_token(evidence)).to_u32();
            writeln!(out, "{} at {at}", evidence_name(evidence)).expect("writing to a string");
        }
    }

    if !parsed.diagnostics().is_empty() {
        section(&mut out, "diagnostics");
        for diagnostic in parsed.diagnostics() {
            render(diagnostic, &index, source, &mut out);
        }
    }

    let mut edits: Vec<&TextEdit> = parsed
        .diagnostics()
        .iter()
        .filter_map(|diagnostic| diagnostic.fix.as_ref())
        .map(|fix| &fix.edit)
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
        let fixed = sumi_text::apply(source, applied);
        // A fix that leaves a diagnostic standing, or that only makes the
        // next fix possible, says so in the header.
        let reparsed = parse_source(fixed.as_str().into()).expect("fixed cases fit in u32");
        let mut remaining: Vec<String> = reparsed
            .diagnostics()
            .iter()
            .map(|diagnostic| diagnostic.code.to_string())
            .collect();
        remaining.sort();
        remaining.dedup();
        let mut notes = Vec::new();
        if skipped > 0 {
            notes.push(format!("{skipped} overlapping edits skipped"));
        }
        if !remaining.is_empty() {
            let verb = if remaining.len() == 1 {
                "remains"
            } else {
                "remain"
            };
            notes.push(format!("{} {verb}", remaining.join(", ")));
        }
        section(&mut out, &titled("fixed", &notes));
        push_text(&mut out, &fixed);
    }

    match format(source, lexed, parse) {
        Ok(formatted) if formatted.text != source => {
            // Formatting leaves an item as written when its rep would
            // change, and cannot fix a chained comparison; the header says.
            let reparsed =
                parse_source(formatted.text.as_str().into()).expect("formatted cases fit in u32");
            let mut remaining: Vec<String> = reparsed
                .parse()
                .evidence()
                .iter()
                .filter_map(|evidence| match evidence {
                    ParseEvidence::Violation(violation) => Some(format!("{:?}", violation.kind)),
                    ParseEvidence::Recovery(_) => None,
                })
                .collect();
            remaining.sort();
            remaining.dedup();
            let mut notes = Vec::new();
            if formatted.reverted > 0 {
                let noun = if formatted.reverted == 1 {
                    "item"
                } else {
                    "items"
                };
                notes.push(format!("{} {noun} left as written", formatted.reverted));
            }
            if !remaining.is_empty() {
                let verb = if remaining.len() == 1 {
                    "remains"
                } else {
                    "remain"
                };
                notes.push(format!("{} {verb}", remaining.join(", ")));
            }
            section(&mut out, &titled("formatted", &notes));
            push_text(&mut out, &formatted.text);
        }
        Ok(_) => {}
        Err(defect) => {
            section(&mut out, "formatted (defect)");
            push_text(&mut out, &defect.rejected);
        }
    }
    out
}

/// A section header, separated from the section before it by a blank line.
fn section(out: &mut String, title: &str) {
    if !out.is_empty() {
        out.push('\n');
    }
    writeln!(out, "== {title} ==").expect("writing to a string");
}

/// A section title with its notes in parentheses, if it has any.
fn titled(title: &str, notes: &[String]) -> String {
    if notes.is_empty() {
        title.to_owned()
    } else {
        format!("{title} ({})", notes.join("; "))
    }
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
        write!(out, " {:?}", range.text(source)).expect("writing to a string");
    }
    out.push('\n');

    let mut previous_end = first;
    for child in tree.children(node) {
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
            ParseRecoveryKind::Token(kind) | ParseRecoveryKind::Closer { kind, .. } => {
                format!("Expected({kind:?})")
            }
            kind @ (ParseRecoveryKind::Item
            | ParseRecoveryKind::Statement
            | ParseRecoveryKind::Expression
            | ParseRecoveryKind::Name
            | ParseRecoveryKind::Type
            | ParseRecoveryKind::Body
            | ParseRecoveryKind::Boundary) => format!("Expected{kind:?}"),
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

/// One diagnostic: its code, place, and message on the first line, then
/// its labels and fix indented under it.
fn render(diagnostic: &Diagnostic, index: &LineIndex, source: &str, out: &mut String) {
    writeln!(
        out,
        "error[{}] {}: {}",
        diagnostic.code,
        place(index, source, diagnostic.primary),
        diagnostic.message
    )
    .expect("writing to a string");
    for label in &diagnostic.labels {
        writeln!(
            out,
            "  at {}: {}",
            place(index, source, label.range),
            label.message
        )
        .expect("writing to a string");
    }
    if let Some(fix) = &diagnostic.fix {
        writeln!(out, "  fix: {}", fix.message).expect("writing to a string");
        writeln!(
            out,
            "    {} -> {:?}",
            place(index, source, fix.edit.range()),
            fix.edit.replacement()
        )
        .expect("writing to a string");
    }
}

/// A range as `start..end` followed by its text, each end `line:col`,
/// one-based with byte columns; an empty range as its one position.
fn place(index: &LineIndex, source: &str, range: TextRange) -> String {
    let at = |offset: TextSize| {
        let position = index.line_col(offset);
        format!("{}:{}", position.line + 1, position.col + 1)
    };
    if range.start() == range.end() {
        at(range.start())
    } else {
        format!(
            "{}..{} {:?}",
            at(range.start()),
            at(range.end()),
            range.text(source)
        )
    }
}
