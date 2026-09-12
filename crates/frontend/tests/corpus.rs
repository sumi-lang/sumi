//! The file-based corpus: every directory under `tests/corpus` at the
//! workspace root that holds a `case.sumi`, run through the frontend and
//! compared with the `frontend.snap` beside it. A snapshot records the
//! tree, with `!` on every node that contains an error, the parser's
//! evidence, the diagnostics, the source after every fix, its header
//! naming any diagnostic that survives them, and the formatted source
//! where it differs, its header counting the items left as written and
//! naming any violation that survives formatting. Run with `UPDATE_FRONTEND=1` to
//! rewrite the snapshots, then review the diff; a new case gets its first
//! snapshot the same way.

use std::fmt::Write as _;

#[path = "../../../tests/support/corpus.rs"]
mod corpus;

use sumi_format::format;
use sumi_frontend::{Applicability, Diagnostic, FileId, Location, Place, TextEdit, parse_source};
use sumi_lexer::LexedFile;
use sumi_syntax::{
    NodeIdx, ParseAnchor, ParseEvidence, ParseExpected, ParseRecoveryKind, RawIdx, SyntaxTree,
};
use sumi_text::{LineIndex, TextSize};

#[test]
fn every_case_matches_its_snapshot() {
    corpus::check(corpus::Stage::Frontend, snapshot);
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
            let at = lexed.boundary(evidence_token(evidence)).to_u32();
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
        // A fix that leaves a diagnostic standing, or that only makes the
        // next fix possible, says so in the header.
        let reparsed =
            parse_source(FileId::new(0), fixed.as_str().into()).expect("fixed cases fit in u32");
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
        if notes.is_empty() {
            out.push_str("\n== fixed ==\n");
        } else {
            writeln!(out, "\n== fixed ({}) ==", notes.join("; ")).expect("writing to a string");
        }
        push_text(&mut out, &fixed);
    }

    match format(source, lexed, parse) {
        Ok(formatted) if formatted.text != source => {
            // Formatting leaves an item as written when its rep would
            // change, and cannot fix a chained comparison; the header says.
            let reparsed = parse_source(FileId::new(0), formatted.text.as_str().into())
                .expect("formatted cases fit in u32");
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
            if notes.is_empty() {
                out.push_str("\n== formatted ==\n");
            } else {
                writeln!(out, "\n== formatted ({}) ==", notes.join("; "))
                    .expect("writing to a string");
            }
            push_text(&mut out, &formatted.text);
        }
        Ok(_) => {}
        Err(defect) => {
            out.push_str("\n== formatted (defect) ==\n");
            push_text(&mut out, &defect.rejected);
        }
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
                ParseExpected::Body => "ExpectedBody".into(),
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
    writeln!(
        out,
        "{}[{}] {}: {}",
        diagnostic.severity.as_str(),
        diagnostic.code,
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
