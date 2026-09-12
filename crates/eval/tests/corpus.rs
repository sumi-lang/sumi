//! Evaluation goldens selected by an `eval` line in `stages`: every
//! parameterless function of an accepted case, run to its value or trap,
//! with the machine's step count and deepest call nesting as the witnesses
//! of what running it costs. Update with
//! `UPDATE_EVAL=1 cargo test -p sumi-eval --test corpus`.

use std::fmt::Write as _;

use sumi_eval::{Machine, Program};
use sumi_frontend::{FileId, parse_source};
use sumi_hir::analyze;

#[path = "../../../tests/support/corpus.rs"]
mod corpus;

#[test]
fn selected_cases_match_their_snapshots() {
    corpus::check(corpus::Stage::Eval, snapshot);
}

fn snapshot(source: &str) -> String {
    let analysis = analyze(parse_source(FileId::new(0), source.into()).unwrap());
    let Some(program) = Program::new(&analysis) else {
        return "file: rejected (see hir.snap); nothing runs\n".to_owned();
    };
    let mut out = "file: accepted\n".to_owned();
    for (id, function) in program.functions() {
        let name = analysis.text(function.name().expect("a valid file names its functions"));
        if !program.signature(id).params.is_empty() {
            writeln!(out, "fn {name}: takes arguments, not run").unwrap();
            continue;
        }
        let mut machine = Machine::new(program, id, &[]);
        let outcome = loop {
            if let Some(outcome) = machine.step() {
                break outcome;
            }
        };
        match outcome {
            Ok(value) => write!(out, "fn {name} = {value}").unwrap(),
            Err(trap) => {
                let range = trap.origin.range();
                write!(
                    out,
                    "fn {name} traps [{}] at `{}` @{}..{}",
                    trap.kind.code(),
                    &source[range.start().to_usize()..range.end().to_usize()],
                    range.start().to_u32(),
                    range.end().to_u32(),
                )
                .unwrap();
            }
        }
        writeln!(
            out,
            " (steps {}, depth {})",
            machine.steps(),
            machine.max_depth()
        )
        .unwrap();
    }
    out
}

#[test]
fn rendering_is_deterministic() {
    let source = "fn f() -> int = g(1)\nfn g(x: int) -> int = x + 1";
    assert_eq!(snapshot(source), snapshot(source));
}
