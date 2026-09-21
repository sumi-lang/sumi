use criterion::{BatchSize, Criterion, criterion_group, criterion_main};
use sumi_frontend::parse_source;
use sumi_hir::analyze;

#[path = "support/slots.rs"]
mod slots;
#[path = "support/workloads.rs"]
mod workloads;

fn slots(c: &mut Criterion) {
    for &shape in slots::SHAPES {
        for &(width, depth) in slots::SIZES {
            let mut group = c.benchmark_group(format!("slots/{shape}/{width}-{depth}"));
            let parsed = parse_source(slots::source(shape, width, depth).into()).unwrap();
            let analysis = analyze(parsed.clone());
            slots::validate(&analysis, width, depth);
            group.bench_function("warm", |b| b.iter(|| slots::evaluate(&analysis)));
            group.bench_function("cold", |b| {
                b.iter_batched(
                    || analyze(parsed.clone()),
                    |analysis| {
                        let value = slots::evaluate(&analysis);
                        (analysis, value)
                    },
                    BatchSize::LargeInput,
                )
            });
        }
    }
    for &(name, source, expected) in workloads::CASES {
        let parsed = workloads::parse(source);
        workloads::validate(&analyze(parsed.clone()), expected);
        c.bench_function(&format!("one-shot/{name}"), |b| {
            b.iter_batched(
                || analyze(parsed.clone()),
                |analysis| {
                    let value = slots::evaluate(&analysis);
                    (analysis, value)
                },
                BatchSize::LargeInput,
            )
        });
    }
}

criterion_group!(benches, slots);
criterion_main!(benches);
