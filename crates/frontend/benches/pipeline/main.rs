use std::sync::OnceLock;

use criterion::{BatchSize, Criterion, Throughput, black_box, criterion_group, criterion_main};
use sumi_format::{Formatted, format};
use sumi_frontend::parse_source;
use sumi_lexer::lex;
use sumi_syntax::{ParserInput, parse};
use sumi_test::bench;

const KIB: usize = 1024;
const MEDIUM_VALID: &str = "medium-valid";

fn corpora() -> &'static [(&'static str, String); 3] {
    static CORPORA: OnceLock<[(&str, String); 3]> = OnceLock::new();
    CORPORA.get_or_init(|| {
        let medium = bench::generate(64 * KIB, 0xBEEF);
        let malformed = bench::damage(&medium, 7, 128);
        let corpora = [
            (MEDIUM_VALID, medium, true),
            ("large-valid", bench::generate(512 * KIB, 0xDECAF), true),
            ("medium-malformed", malformed, false),
        ];
        corpora.map(|(name, source, valid)| {
            let parsed = parse_source(source.clone().into_boxed_str())
                .expect("benchmark corpus fits in Sumi's source coordinate space");
            assert_eq!(
                parsed.diagnostics().is_empty(),
                valid,
                "benchmark corpus validity changed for {name}: {:?}",
                parsed.diagnostics().first()
            );
            (name, source)
        })
    })
}

fn corpus(name: &str) -> &'static str {
    &corpora()
        .iter()
        .find(|(candidate, _)| *candidate == name)
        .expect("every benchmark names a corpus in the table")
        .1
}

fn frontend(c: &mut Criterion, name: &str) {
    let source = corpus(name);
    let mut group = c.benchmark_group("frontend");
    group.throughput(Throughput::Bytes(source.len() as u64));
    group.bench_function(name, |b| {
        b.iter_batched(
            || source.to_owned().into_boxed_str(),
            |source| {
                parse_source(source)
                    .expect("benchmark corpus fits in Sumi's source coordinate space")
            },
            BatchSize::LargeInput,
        );
    });
    group.finish();
}

fn valid_pipeline(c: &mut Criterion) {
    let source = corpus(MEDIUM_VALID);
    let lexed = lex(source).expect("benchmark corpus fits in Sumi's source coordinate space");
    let input = ParserInput::new(&lexed);
    let mut group = c.benchmark_group("pipeline/medium-valid");
    group.throughput(Throughput::Bytes(source.len() as u64));
    group.bench_function("lex", |b| {
        b.iter_with_large_drop(|| {
            lex(black_box(source)).expect("benchmark corpus fits in Sumi's source coordinate space")
        });
    });
    group.bench_function("parse", |b| {
        b.iter_batched(|| input.clone(), parse, BatchSize::LargeInput);
    });
    group.finish();
}

fn formatting(c: &mut Criterion) {
    let source = corpus(MEDIUM_VALID);
    format_source(c, "format/medium-valid", source);
    let formatted = parse_and_format(source).text;
    assert!(
        parse_and_format(&formatted).edits.is_empty(),
        "formatting is idempotent on the benchmark corpus"
    );
    format_source(c, "format/medium-formatted", &formatted);
}

fn parse_and_format(source: &str) -> Formatted {
    let lexed = lex(source).expect("benchmark corpus fits in Sumi's source coordinate space");
    format(source, &lexed, &parse(ParserInput::new(&lexed))).expect("the corpus formats")
}

fn format_source(c: &mut Criterion, group: &str, source: &str) {
    let lexed = lex(source).expect("benchmark corpus fits in Sumi's source coordinate space");
    let parsed = parse(ParserInput::new(&lexed));
    let mut group = c.benchmark_group(group);
    group.throughput(Throughput::Bytes(source.len() as u64));
    group.bench_function("format", |b| {
        b.iter_with_large_drop(|| format(black_box(source), &lexed, &parsed));
    });
    group.finish();
}

fn excessive_nesting(c: &mut Criterion) {
    let depth = 4096;
    let mut source = String::from("fn nested() -> int = ");
    source.extend(std::iter::repeat_n('(', depth));
    source.push('1');
    source.extend(std::iter::repeat_n(')', depth));
    let parsed = parse_source(source.clone().into_boxed_str()).unwrap();
    assert!(!parsed.diagnostics().is_empty());

    let mut group = c.benchmark_group("frontend/adversarial");
    group.throughput(Throughput::Bytes(source.len() as u64));
    group.bench_function("excessive-nesting", |b| {
        b.iter_batched(
            || source.clone().into_boxed_str(),
            |source| parse_source(source).unwrap(),
            BatchSize::LargeInput,
        );
    });
    group.finish();
}

fn timing(c: &mut Criterion) {
    frontend(c, "large-valid");
    frontend(c, "medium-malformed");
    valid_pipeline(c);
    formatting(c);
    excessive_nesting(c);
}

fn memory(c: &mut Criterion) {
    frontend(c, "large-valid");
    formatting(c);
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
