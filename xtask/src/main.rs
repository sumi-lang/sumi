//! Repository maintenance tasks, run as `cargo xtask <task>`.
//!
//! `codegen` regenerates the files derived from `sumi.grammar` and
//! `sumi.diagnostics`; with `--check` it fails instead when any of them
//! would change, which is how CI keeps the checked-in copies honest. The task depends on none of the
//! workspace crates, so it runs while they do not compile — which a
//! grammar change in progress makes likely.

mod codegen;
mod corpus;
mod diagnostics;
mod grammar;

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

const USAGE: &str = "usage: cargo xtask <codegen [--check] | fuzz-seed>

  codegen           regenerate the files derived from sumi.grammar and
                    sumi.diagnostics
  codegen --check   fail if any of them would change
  fuzz-seed         seed every fuzz target's corpus from tests/corpus";

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let args: Vec<&str> = args.iter().map(String::as_str).collect();
    let result = match args.as_slice() {
        ["codegen"] => codegen(false),
        ["codegen", "--check"] => codegen(true),
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

/// Where each diagnostic group's constants are generated.
const GROUP_HOMES: [(&str, &str); 2] = [
    ("syntax", "crates/frontend/src/generated/codes.rs"),
    ("semantic", "crates/hir/src/generated/codes.rs"),
];

/// The generated files, as `(path, content)`.
fn generated(
    grammar: &grammar::Grammar,
    registry: &diagnostics::Registry,
    examples: &BTreeMap<String, corpus::Example>,
) -> Result<Vec<(&'static str, String)>, String> {
    let mut files = vec![
        (
            "crates/lexer/src/generated/mod.rs",
            codegen::rustfmt(&codegen::lexer_kind(grammar))?,
        ),
        (
            "crates/syntax/src/generated/mod.rs",
            codegen::rustfmt(&codegen::syntax_kind(grammar))?,
        ),
        (
            "crates/syntax/src/generated/ast.rs",
            codegen::rustfmt(&codegen::ast(grammar))?,
        ),
        (
            "docs/reference/generated/grammar.md",
            codegen::reference(grammar),
        ),
        ("fuzz/sumi.dict", codegen::dictionary(grammar)),
        (
            "crates/test/src/generated/mod.rs",
            codegen::rustfmt(&codegen::coverage(grammar))?,
        ),
    ];
    for group in &registry.groups {
        let (_, path) = GROUP_HOMES
            .iter()
            .find(|(name, _)| *name == group.name)
            .ok_or_else(|| format!("group {} has no home in GROUP_HOMES", group.name))?;
        files.push((path, codegen::rustfmt(&codegen::codes(group))?));
    }
    for (name, _) in GROUP_HOMES {
        if registry.group(name).is_none() {
            return Err(format!("sumi.diagnostics declares no group {name}"));
        }
    }
    files.push((
        "docs/reference/generated/diagnostics.md",
        codegen::catalogue(registry, examples),
    ));
    Ok(files)
}

fn codegen(check: bool) -> Result<(), String> {
    let root = workspace_root();
    let source = fs::read_to_string(root.join("sumi.grammar"))
        .map_err(|error| format!("reading sumi.grammar: {error}"))?;
    let grammar = grammar::Grammar::parse(&source)?;
    let source = fs::read_to_string(root.join("sumi.diagnostics"))
        .map_err(|error| format!("reading sumi.diagnostics: {error}"))?;
    let registry = diagnostics::Registry::parse(&source)?;
    let examples = corpus::examples(&root)?;
    let mut drifted = Vec::new();
    for (path, content) in generated(&grammar, &registry, &examples)? {
        let target = root.join(path);
        if fs::read_to_string(&target).is_ok_and(|existing| existing == content) {
            continue;
        }
        drifted.push(path);
        if check {
            continue;
        }
        if let Some(parent) = target.parent() {
            fs::create_dir_all(parent)
                .map_err(|error| format!("creating {}: {error}", parent.display()))?;
        }
        fs::write(&target, content).map_err(|error| format!("writing {path}: {error}"))?;
        println!("wrote {path}");
    }
    if check && !drifted.is_empty() {
        return Err(format!(
            "{} would change; run `cargo xtask codegen` and commit the result",
            drifted.join(", ")
        ));
    }
    if drifted.is_empty() {
        println!("generated files are up to date");
    }
    Ok(())
}

/// Seed every fuzz target's corpus under `fuzz/corpus/` from the file-based
/// cases. `lex`, `parse`, and `check` read a case as it is. `edit` reads three header
/// bytes before the source — the edit kind, then the significant token it
/// lands on — so each case is written once per edit kind. The corpus
/// directories are untracked; a seed that adds no coverage over what is
/// already there is simply not kept.
fn fuzz_seed() -> Result<(), String> {
    let root = workspace_root();
    let corpus = root.join("tests/corpus");
    let mut cases = Vec::new();
    corpus::cases(&corpus, &mut cases)?;
    if cases.is_empty() {
        return Err(format!("no cases under {}", corpus.display()));
    }
    let out = root.join("fuzz/corpus");
    for target in ["lex", "parse", "edit", "check"] {
        fs::create_dir_all(out.join(target))
            .map_err(|error| format!("creating fuzz/corpus/{target}: {error}"))?;
    }
    for case in &cases {
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
        for kind in 0u8..4 {
            let mut seed = vec![kind, 1, 0];
            seed.extend_from_slice(&source);
            write(out.join("edit").join(format!("{name}-{kind}")), &seed)?;
        }
    }
    println!("seeded {} cases into fuzz/corpus/", cases.len());
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The repository grammar parses, validates, and renders; `--check` in
    /// CI proves the rendered files are the committed ones.
    #[test]
    fn repository_grammar_renders() {
        let source = fs::read_to_string(workspace_root().join("sumi.grammar")).unwrap();
        let grammar = grammar::Grammar::parse(&source).unwrap();
        assert!(codegen::lexer_kind(&grammar).contains("pub enum SyntaxKind"));
        assert!(codegen::syntax_kind(&grammar).contains("pub enum NodeKind"));
        assert!(codegen::ast(&grammar).contains("pub trait AstNode"));
        assert!(codegen::reference(&grammar).contains("## Syntax nodes"));
        assert!(codegen::coverage(&grammar).contains("pub const WITNESSES"));
        let dictionary = codegen::dictionary(&grammar);
        assert!(dictionary.contains("FnKw=\"fn\""));
        assert!(dictionary.contains("\n\"//\"\n"), "{dictionary}");
    }

    /// The repository registry parses, every group has a home, and the
    /// chapter renders with an example per code the corpus shows.
    #[test]
    fn repository_registry_renders() {
        let root = workspace_root();
        let source = fs::read_to_string(root.join("sumi.diagnostics")).unwrap();
        let registry = diagnostics::Registry::parse(&source).unwrap();
        for (name, _) in GROUP_HOMES {
            let group = registry.group(name).unwrap();
            assert!(codegen::codes(group).contains("pub const ALL"));
        }
        let examples = corpus::examples(&root).unwrap();
        let chapter = codegen::catalogue(&registry, &examples);
        assert!(chapter.contains("### `syntax/expected-token`"));
        assert!(chapter.contains("```sumi\n"));
    }
}
