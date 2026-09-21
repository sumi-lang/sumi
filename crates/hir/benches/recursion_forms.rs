use criterion::{BatchSize, Criterion, black_box, criterion_group, criterion_main};
use sumi_frontend::parse_source;
use sumi_hir::analyze;

#[path = "support/recursion_forms.rs"]
mod forms;

fn recursion_forms(c: &mut Criterion) {
    for &shape in forms::SHAPES {
        for &size in forms::SIZES {
            let source = forms::source(shape, size);
            let analysis = analyze(parse_source(source.clone().into()).unwrap());
            forms::validate(shape, size, &analysis);
            let mut group = c.benchmark_group(format!("forms/{shape}/{size}"));
            group.bench_function("execute", |b| b.iter(|| forms::evaluate(&analysis)));
            group.bench_function("check", |b| {
                b.iter_with_large_drop(|| {
                    analyze(parse_source(black_box(source.clone()).into()).unwrap())
                });
            });
            group.bench_function("check-execute", |b| {
                b.iter_batched(
                    || source.clone(),
                    |source| {
                        let analysis = analyze(parse_source(source.into()).unwrap());
                        let value = forms::evaluate(&analysis);
                        (analysis, value)
                    },
                    BatchSize::LargeInput,
                );
            });
        }
    }
}

criterion_group!(benches, recursion_forms);
criterion_main!(benches);
