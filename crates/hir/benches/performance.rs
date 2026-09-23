use std::fmt::Write;

use criterion::{BatchSize, BenchmarkId, Criterion, black_box, criterion_group, criterion_main};
use sumi_frontend::parse_source;
use sumi_hir::{Value, analyze};

#[path = "support/deep.rs"]
mod deep;
#[path = "support/programs.rs"]
mod programs;
#[path = "support/slots.rs"]
mod slots;
#[path = "support/workloads.rs"]
mod workloads;

fn analyze_case(c: &mut Criterion, shape: &str, size: usize) {
    let source = programs::source(shape, size);
    let parsed = programs::parse(&source);
    programs::validate(shape, size, &analyze(parsed.clone()));
    let mut group = c.benchmark_group("hir/analyze");
    group.bench_function(BenchmarkId::new(shape, size), |b| {
        b.iter_batched(|| parsed.clone(), analyze, BatchSize::LargeInput);
    });
    group.finish();
}

fn workload(c: &mut Criterion, name: &str) {
    let &(_, source, expected) = workloads::CASES
        .iter()
        .find(|(candidate, _, _)| *candidate == name)
        .expect("every benchmark names a workload in the table");
    let analysis = analyze(workloads::parse(source));
    workloads::validate(&analysis, expected);
    let program = analysis.program().unwrap();
    let main = program.function_named("main").unwrap();
    let mut group = c.benchmark_group("graph/execute");
    group.bench_function(name, |b| {
        b.iter(|| program.machine(black_box(main), &[]).run());
    });
    group.finish();
}

fn tail_recursion(c: &mut Criterion) {
    let depth = 100_000;
    let analysis = analyze(parse_source(deep::source("tail", depth).into()).unwrap());
    assert!(analysis.is_valid(), "{:?}", analysis.diagnostics());
    let program = analysis.program().unwrap();
    let main = program.function_named("main").unwrap();
    assert_eq!(
        program.machine(main, &[]).run(),
        Ok(Value::Int((depth as i64 + 7).into()))
    );
    let mut group = c.benchmark_group("graph/execute");
    group.bench_function("tail-recursion-100000", |b| {
        b.iter(|| program.machine(black_box(main), &[]).run());
    });
    group.finish();
}

fn suspended_frames(c: &mut Criterion) {
    let (width, depth) = (2048, 64);
    let analysis = analyze(parse_source(slots::source("non-tail", width, depth).into()).unwrap());
    slots::validate(&analysis, width, depth);
    let program = analysis.program().unwrap();
    let main = program.function_named("main").unwrap();
    let mut group = c.benchmark_group("graph/execute");
    group.bench_function("suspended-frames-2048x64", |b| {
        b.iter(|| program.machine(black_box(main), &[]).run());
    });
    group.finish();
}

fn singleton_entry(c: &mut Criterion) {
    let width = 8192;
    let mut source = String::from("fn entry(b: bool) -> int {\n");
    for i in 0..width {
        writeln!(source, "let x{i} = {i}").unwrap();
    }
    source.push_str("7\n}\nfn main() -> int = entry(true)");
    let analysis = analyze(parse_source(source.into()).unwrap());
    assert!(analysis.is_valid(), "{:?}", analysis.diagnostics());
    let program = analysis.program().unwrap();
    let entry = program.function_named("entry").unwrap();
    assert_eq!(
        program.evaluate(entry, &[Value::Bool(true)]),
        Value::Int(7.into())
    );
    let mut group = c.benchmark_group("hir/evaluate");
    group.bench_function("singleton-entry-8192", |b| {
        b.iter(|| program.evaluate(black_box(entry), black_box(&[Value::Bool(true)])));
    });
    group.finish();
}

fn timing(c: &mut Criterion) {
    analyze_case(c, "inferred-reverse", 8192);
    analyze_case(c, "unresolved-cycle", 8192);
    analyze_case(c, "branches", 1024);
    analyze_case(c, "nested-mutation", 1024);
    analyze_case(c, "caller-guards", 1024);
    analyze_case(c, "caller-arithmetic-guards", 1024);
    workload(c, "fibonacci");
    tail_recursion(c);
    suspended_frames(c);
    singleton_entry(c);
    workload(c, "big-int");
}

fn memory(c: &mut Criterion) {
    analyze_case(c, "nested-mutation", 1024);
    suspended_frames(c);
    singleton_entry(c);
    workload(c, "big-int");
}

fn benchmarks(c: &mut Criterion) {
    match std::env::var("SUMI_BENCH_SET").as_deref() {
        Ok("memory") => memory(c),
        Ok("timing") | Err(_) => timing(c),
        Ok(value) => panic!("unknown SUMI_BENCH_SET {value:?}"),
    }
}

criterion_group!(benches, benchmarks);
criterion_main!(benches);
