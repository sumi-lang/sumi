use criterion::{BatchSize, Criterion, black_box, criterion_group, criterion_main};
use sumi_frontend::parse_source;
use sumi_hir::{Value, analyze};

#[path = "support/entry.rs"]
mod entry;

fn entry(c: &mut Criterion) {
    for &shape in entry::SHAPES {
        for &width in entry::WIDTHS {
            let source = entry::source(shape, width);
            let analysis = analyze(parse_source(source.clone().into()).unwrap());
            entry::validate(shape, &analysis);
            let program = analysis.program().unwrap();
            let function = program.function_named("entry").unwrap();
            let mut group = c.benchmark_group(format!("entry/{shape}/{width}"));
            group.bench_function("evaluate", |b| {
                b.iter(|| program.evaluate(black_box(function), black_box(&[Value::Bool(true)])));
            });
            group.bench_function("check-evaluate", |b| {
                b.iter_batched(
                    || source.clone(),
                    |source| {
                        let analysis = analyze(parse_source(source.into()).unwrap());
                        let program = analysis.program().unwrap();
                        let value = program.evaluate(
                            program.function_named("entry").unwrap(),
                            &[Value::Bool(true)],
                        );
                        (analysis, value)
                    },
                    BatchSize::LargeInput,
                );
            });
        }
    }
}

criterion_group!(benches, entry);
criterion_main!(benches);
