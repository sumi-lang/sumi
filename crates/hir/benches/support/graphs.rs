use crate::infer::{Inference, Term};
use sumi_hir::Ty;

pub const SIZES: [usize; 4] = [8, 128, 1024, 8192];
pub const SHAPES: [&str; 11] = [
    "chain-forward",
    "chain-reverse",
    "grounded-cycle",
    "unresolved-cycle",
    "conflict-cycle",
    "fan-out",
    "fan-in",
    "equalities",
    "constant-imports",
    "mixed-imports",
    "scattered-fanout",
];

pub struct Graph {
    pub context: Inference,
    terms: Vec<Term>,
}

pub fn build(shape: &str, size: usize) -> Graph {
    let mut context = Inference::default();
    let mut terms: Vec<_> = (0..size).map(|_| context.fresh()).collect();
    if shape == "chain-reverse" {
        terms.reverse();
    }
    match shape {
        "scattered-fanout" => {
            let providers = size.div_ceil(32);
            for &term in &terms[..providers] {
                context.equal(term, Ty::Int.into());
            }
            for i in 0..size {
                // Interleave providers' edges and scatter destinations. The
                // odd multiplier permutes our power-of-two benchmark sizes.
                let call = context.import(terms[i % providers]);
                context.equal(terms[(i * 4051) % size], call);
            }
        }
        "constant-imports" | "mixed-imports" => {
            for (i, &term) in terms.iter().enumerate() {
                let provider = if shape == "mixed-imports" && i % 2 == 1 {
                    terms[i - 1]
                } else {
                    Ty::Int.into()
                };
                let call = context.import(provider);
                context.equal(term, call);
            }
        }
        "fan-out" => {
            context.equal(terms[0], Ty::Int.into());
            for &term in &terms[1..] {
                let call = context.import(terms[0]);
                context.equal(term, call);
            }
        }
        "fan-in" => {
            for &term in &terms[1..] {
                context.equal(term, Ty::Int.into());
                let call = context.import(term);
                context.equal(terms[0], call);
            }
        }
        "equalities" => {
            // Balanced unions exercise rank/path compression, not just stars.
            let mut stride = 1;
            while stride < size {
                for i in (0..size).step_by(stride * 2) {
                    if i + stride < size {
                        context.equal(terms[i], terms[i + stride]);
                    }
                }
                stride *= 2;
            }
            context.equal(terms[0], Ty::Int.into());
        }
        _ => {
            assert!(SHAPES.contains(&shape));
            for i in 0..size - 1 {
                let call = context.import(terms[i + 1]);
                context.equal(terms[i], call);
            }
            if shape.ends_with("cycle") {
                let call = context.import(terms[0]);
                context.equal(terms[size - 1], call);
            }
            if shape != "unresolved-cycle" {
                context.equal(terms[size - 1], Ty::Int.into());
            }
            if shape == "conflict-cycle" {
                context.equal(terms[0], Ty::Bool.into());
            }
        }
    }
    Graph { context, terms }
}

pub fn validate(shape: &str, graph: &Graph) {
    for &term in &graph.terms {
        match shape {
            "unresolved-cycle" => {
                assert_eq!(graph.context.resolve(term), None);
                assert!(!graph.context.conflicted(term));
            }
            "conflict-cycle" => assert!(graph.context.conflicted(term)),
            _ => assert_eq!(graph.context.resolve(term), Some(Ty::Int)),
        }
    }
}
