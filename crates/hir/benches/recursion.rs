use criterion::{BatchSize, BenchmarkId, Criterion, criterion_group, criterion_main};
use sumi_frontend::parse_source;
use sumi_hir::analyze;

#[path = "support/recursion.rs"]
mod recursion;

fn recursion(c: &mut Criterion) {
    let mut group = c.benchmark_group("recursion");
    for &(shape, sizes) in recursion::CASES {
        for &size in sizes {
            group.bench_function(BenchmarkId::new(shape, size), |b| {
                recursion::checked(shape, size);
                let parsed = parse_source(recursion::source(shape, size).into()).unwrap();
                b.iter_batched(|| parsed.clone(), analyze, BatchSize::LargeInput);
            });
        }
    }
    group.finish();
}

criterion_group!(benches, recursion);
criterion_main!(benches);
