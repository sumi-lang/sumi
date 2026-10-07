//! Every corpus case run through the frontend and the formatter and compared with its
//! `frontend.snap`.

use std::fmt::Write as _;

use sumi_format::format;
use sumi_frontend::parse_source;
use sumi_lexer::LexedFile;
use sumi_syntax::{NodeIdx, ParseAnchor, ParseEvidence, RawIdx, SyntaxTree};
use sumi_test::{check, corpus, evidence_name};
use sumi_text::{LineIndex, TextEdit};

#[test]
fn every_case_matches_its_snapshot() {
    corpus::check(corpus::Stage::Frontend, snapshot);
}

fn snapshot(source: &str, stages: &[corpus::Stage]) -> String {
    let parsed = parse_source(source.into()).expect("corpus cases fit in u32");
    let lexed = parsed.lexed();
    let parse = parsed.parse();
    let index = LineIndex::new(source);
    let mut out = String::new();
    // A hir case keeps its tree only where the parser recovered: hir.snap anchors the graph by
    // range, so a case whose parse is the point does not select hir.
    let has_tree = !stages.contains(&corpus::Stage::Hir) || !parse.evidence().is_empty();
    if !has_tree {
        out.push_str("tree: omitted\n");
    } else {
        section(&mut out, "tree");
        check::tree(parse.tree(), lexed);
        render_node(
            parse.tree(),
            lexed,
            source,
            &index,
            parse.tree().root(),
            0,
            &mut out,
        );
    }

    if !parse.evidence().is_empty() {
        section(&mut out, "evidence");
        for evidence in parse.evidence() {
            let at = index.display_offset(lexed.boundary(evidence_token(evidence)));
            writeln!(out, "{} at {at}", evidence_name(evidence)).expect("writing to a string");
        }
    }

    if !parsed.diagnostics().is_empty() {
        section(&mut out, "diagnostics");
        for diagnostic in parsed.diagnostics() {
            corpus::diagnostic(diagnostic, &index, source, &mut out);
        }
    }

    let mut edits: Vec<&TextEdit> = parsed
        .diagnostics()
        .iter()
        .filter_map(|diagnostic| diagnostic.fix.as_ref())
        .map(|fix| &fix.edit)
        .collect();
    if !edits.is_empty() {
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

fn section(out: &mut String, title: &str) {
    if !out.is_empty() {
        out.push('\n');
    }
    writeln!(out, "== {title} ==").expect("writing to a string");
}

fn titled(title: &str, notes: &[String]) -> String {
    if notes.is_empty() {
        title.to_owned()
    } else {
        format!("{title} ({})", notes.join("; "))
    }
}

fn push_text(out: &mut String, text: &str) {
    out.push_str(text);
    if !text.ends_with('\n') {
        out.push('\n');
    }
}

fn render_node(
    tree: &SyntaxTree,
    lexed: &LexedFile,
    source: &str,
    index: &LineIndex<'_>,
    node: NodeIdx,
    depth: usize,
    out: &mut String,
) {
    let range = tree.byte_range(node, lexed);
    let mark = if tree.has_error(node) { "!" } else { "" };
    write!(
        out,
        "{:indent$}{:?}{mark} {}",
        "",
        tree.kind(node),
        index.display_range(range),
        indent = depth * 2
    )
    .expect("writing to a string");
    if tree.children(node).next().is_none() {
        write!(out, " {:?}", range.text(source)).expect("writing to a string");
    }
    out.push('\n');

    for child in tree.children(node) {
        render_node(tree, lexed, source, index, child, depth + 1, out);
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
