use criterion::{
    BatchSize, BenchmarkId, Criterion, Throughput, black_box, criterion_group, criterion_main,
};
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

// Include lexing, parsing, diagnostics, source ownership, and semantic checking
// so moving work between the parser and typed consumers cannot hide its cost.
fn check_source(c: &mut Criterion) {
    let mut group = c.benchmark_group("hir/check-source");
    for shape in programs::SHAPES {
        for size in programs::SIZES {
            let source = programs::source(shape, size);
            programs::validate(shape, size, &analyze(programs::parse(&source)));
            group.throughput(Throughput::Bytes(source.len() as u64));
            group.bench_function(BenchmarkId::new(shape, size), |b| {
                b.iter_with_large_drop(|| analyze(programs::parse(black_box(&source))));
            });
        }
    }
    group.finish();
}

criterion_group!(benches, analysis, check_source);
criterion_main!(benches);
