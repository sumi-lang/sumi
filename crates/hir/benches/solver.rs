use criterion::{BatchSize, BenchmarkId, Criterion, Throughput, criterion_group, criterion_main};
use sumi_hir::Ty;

// Compile the actual private solver, without exporting a benchmark-only API.
#[path = "support/graphs.rs"]
mod graphs;
#[allow(dead_code)]
#[path = "../src/solver.rs"]
mod solver;
#[allow(dead_code)]
#[path = "../src/typing.rs"]
mod typing;

fn solver(c: &mut Criterion) {
    for phase in ["solve", "replay-context", "build-solve-replay"] {
        let mut group = c.benchmark_group(format!("solver/{phase}"));
        for shape in graphs::SHAPES {
            for size in graphs::SIZES {
                let mut witness = graphs::build(shape, size);
                witness.context.solve();
                graphs::validate(shape, &witness);
                group.throughput(Throughput::Elements(size as u64));
                group.bench_function(BenchmarkId::new(shape, size), |b| match phase {
                    "solve" => b.iter_batched(
                        || graphs::build(shape, size),
                        |mut graph| {
                            graph.context.solve();
                            graph
                        },
                        BatchSize::LargeInput,
                    ),
                    "replay-context" => {
                        b.iter_batched(|| (), |()| witness.context.replay(), BatchSize::LargeInput)
                    }
                    _ => b.iter_batched(
                        || (),
                        |()| {
                            let mut graph = graphs::build(shape, size);
                            graph.context.solve();
                            let replay = graph.context.replay();
                            (graph, replay)
                        },
                        BatchSize::LargeInput,
                    ),
                });
            }
        }
        group.finish();
    }
}

criterion_group!(benches, solver);
criterion_main!(benches);
