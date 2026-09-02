//! Repository maintenance tasks, run as `cargo xtask <task>`.
//!
//! `codegen` regenerates the files derived from `sumi.grammar`; with
//! `--check` it fails instead when any of them would change, which is how CI
//! keeps the checked-in copies honest.

mod codegen;
mod grammar;

use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

const USAGE: &str = "usage: cargo xtask codegen [--check]

  codegen           regenerate the files derived from sumi.grammar
  codegen --check   fail if any of them would change";

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let args: Vec<&str> = args.iter().map(String::as_str).collect();
    let result = match args.as_slice() {
        ["codegen"] => codegen(false),
        ["codegen", "--check"] => codegen(true),
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

/// The files derived from the grammar, as `(path, content)`.
fn generated(grammar: &grammar::Grammar) -> Result<[(&'static str, String); 3], String> {
    Ok([
        (
            "crates/lexer/src/generated/mod.rs",
            codegen::rustfmt(&codegen::lexer_kind(grammar))?,
        ),
        (
            "crates/syntax/src/generated/mod.rs",
            codegen::rustfmt(&codegen::syntax_kind(grammar))?,
        ),
        (
            "docs/reference/generated/grammar.md",
            codegen::reference(grammar),
        ),
    ])
}

fn codegen(check: bool) -> Result<(), String> {
    let root = workspace_root();
    let source = fs::read_to_string(root.join("sumi.grammar"))
        .map_err(|error| format!("reading sumi.grammar: {error}"))?;
    let grammar = grammar::Grammar::parse(&source)?;
    let mut drifted = Vec::new();
    for (path, content) in generated(&grammar)? {
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
        assert!(codegen::reference(&grammar).contains("## Syntax nodes"));
    }
}
