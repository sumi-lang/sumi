use criterion::{BenchmarkId, Criterion, black_box, criterion_group, criterion_main};
use sumi_frontend::parse_source;
use sumi_hir::{Value, analyze};

#[path = "support/deep.rs"]
mod deep;

fn deep(c: &mut Criterion) {
    let mut group = c.benchmark_group("deep");
    for &shape in deep::SHAPES {
        for &depth in deep::SIZES {
            group.bench_function(BenchmarkId::new(shape, depth), |b| {
                let source = deep::source(shape, depth);
                let analysis = analyze(parse_source(source.into()).unwrap());
                assert!(analysis.is_valid(), "{:?}", analysis.diagnostics());
                let program = analysis.program().unwrap();
                let main = program.function_named("main").unwrap();
                assert_eq!(
                    program.evaluate(main, &[]),
                    Value::Int((depth as i64 + 7).into())
                );
                b.iter(|| program.evaluate(black_box(main), &[]));
            });
        }
    }
}

criterion_group!(benches, deep);
criterion_main!(benches);
