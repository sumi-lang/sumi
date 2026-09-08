use criterion::{BatchSize, BenchmarkId, Criterion, Throughput, criterion_group, criterion_main};
use sumi_hir::analyze;

#[path = "support/programs.rs"]
mod programs;

fn analysis(c: &mut Criterion) {
    let mut group = c.benchmark_group("hir/analyze");
    for shape in programs::SHAPES {
        for size in programs::SIZES {
            group.throughput(Throughput::Elements(size as u64));
            group.bench_function(BenchmarkId::new(shape, size), |b| {
                let source = programs::source(shape, size);
                let parsed = programs::parse(&source);
                programs::validate(shape, size, &analyze(parsed.clone()));
                b.iter_batched(|| parsed.clone(), analyze, BatchSize::LargeInput);
            });
        }
    }
    group.finish();
}

criterion_group!(benches, analysis);
criterion_main!(benches);
