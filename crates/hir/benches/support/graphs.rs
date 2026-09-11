use crate::solver::Var;
use crate::typing::{Expected, Typing};
use sumi_hir::Ty;
use sumi_text::{FileId, Span, TextRange, TextSize};

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

/// Every claim of a benchmark graph is made at the same place: provenance
/// costs the same wherever it points.
const HERE: Span = Span::new(
    FileId::new(0),
    TextRange::new(TextSize::new(0), TextSize::new(1)),
);

pub struct Graph {
    pub context: Typing,
    terms: Vec<Var>,
}

/// Every term is `int`, unless the shape leaves it unresolved or conflicted.
fn int(context: &mut Typing, term: Var) {
    context.expect(term, Expected::Ty(Ty::Int), HERE);
}

fn equal(context: &mut Typing, term: Var, other: Var) {
    context.expect(term, Expected::Class(other), HERE);
}

pub fn build(shape: &str, size: usize) -> Graph {
    let mut context = Typing::new(FileId::new(0));
    let mut terms: Vec<_> = (0..size).map(|_| context.fresh()).collect();
    if shape == "chain-reverse" {
        terms.reverse();
    }
    match shape {
        "scattered-fanout" => {
            let providers = size.div_ceil(32);
            for &term in &terms[..providers] {
                int(&mut context, term);
            }
            for i in 0..size {
                // Interleave providers' edges and scatter destinations. The
                // odd multiplier permutes our power-of-two benchmark sizes.
                let call = context.call(terms[i % providers], HERE);
                equal(&mut context, terms[(i * 4051) % size], call);
            }
        }
        "constant-imports" | "mixed-imports" => {
            for (i, &term) in terms.iter().enumerate() {
                let call = if shape == "mixed-imports" && i % 2 == 1 {
                    context.call(terms[i - 1], HERE)
                } else {
                    context.known(Ty::Int, HERE)
                };
                equal(&mut context, term, call);
            }
        }
        "fan-out" => {
            int(&mut context, terms[0]);
            for &term in &terms[1..] {
                let call = context.call(terms[0], HERE);
                equal(&mut context, term, call);
            }
        }
        "fan-in" => {
            for &term in &terms[1..] {
                int(&mut context, term);
                let call = context.call(term, HERE);
                equal(&mut context, terms[0], call);
            }
        }
        "equalities" => {
            // Balanced unions exercise rank/path compression, not just stars.
            let mut stride = 1;
            while stride < size {
                for i in (0..size).step_by(stride * 2) {
                    if i + stride < size {
                        equal(&mut context, terms[i], terms[i + stride]);
                    }
                }
                stride *= 2;
            }
            int(&mut context, terms[0]);
        }
        _ => {
            assert!(SHAPES.contains(&shape));
            for i in 0..size - 1 {
                let call = context.call(terms[i + 1], HERE);
                equal(&mut context, terms[i], call);
            }
            if shape.ends_with("cycle") {
                let call = context.call(terms[0], HERE);
                equal(&mut context, terms[size - 1], call);
            }
            if shape != "unresolved-cycle" {
                int(&mut context, terms[size - 1]);
            }
            if shape == "conflict-cycle" {
                context.expect(terms[0], Expected::Ty(Ty::Bool), HERE);
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
                assert!(!graph.context.evidence(term).is_conflict());
            }
            "conflict-cycle" => assert!(graph.context.evidence(term).is_conflict()),
            _ => assert_eq!(graph.context.resolve(term), Some(Ty::Int)),
        }
    }
}
