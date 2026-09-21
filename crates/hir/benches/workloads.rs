use criterion::{BatchSize, Criterion, black_box, criterion_group, criterion_main};
use sumi_hir::analyze;

#[path = "support/workloads.rs"]
mod workloads;

fn workloads(c: &mut Criterion) {
    for &(name, source, expected) in workloads::CASES {
        let parsed = workloads::parse(source);
        let analysis = analyze(parsed.clone());
        workloads::validate(&analysis, expected);
        let mut group = c.benchmark_group(name);
        group.bench_function("parse", |b| {
            b.iter(|| workloads::parse(black_box(source)));
        });
        group.bench_function("analyze", |b| {
            b.iter_batched(|| parsed.clone(), analyze, BatchSize::SmallInput);
        });
        group.bench_function("check", |b| {
            b.iter(|| analyze(workloads::parse(black_box(source))));
        });
        let program = analysis.program().unwrap();
        let main = program.function_named("main").unwrap();
        group.bench_function("execute", |b| {
            b.iter(|| program.evaluate(black_box(main), &[]));
        });
        group.finish();
    }
}

criterion_group!(benches, workloads);
criterion_main!(benches);
