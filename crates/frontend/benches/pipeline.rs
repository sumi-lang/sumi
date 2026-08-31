use criterion::{
    BatchSize, BenchmarkId, Criterion, Throughput, black_box, criterion_group, criterion_main,
};
use sumi_frontend::parse_source;
use sumi_lexer::lex;
use sumi_syntax::{ParserInput, cook, parse};

const KIB: usize = 1024;

const SMALL_VALID: &str = r#"fn transform(value: int, limit: int) -> int {
  let doubled = value * 2
  let adjusted = if doubled > limit {
    doubled - limit
  } else {
    blend(doubled, limit)
  }
  return adjusted
}
"#;

const VALID_ITEM: &str = r##"// Exercise declarations, trivia, literals, precedence, calls, and branches.
fn transform(value: int, limit: int) -> int {
  let doubled = value * 2
  let adjusted = if doubled > limit {
    doubled - limit
  } else {
    blend(
      doubled + 16,
      limit,
    )
  }
  _ = record(adjusted, "value", r#"raw"#, 'λ')
  return adjusted
}
"##;

const MALFORMED_ITEM: &str = r#"fn broken(value int, limit: int {
  let doubled value * 2
  let adjusted = if doubled > {
    doubled - limit;
  else {
    blend(doubled,, limit)
  }
  return adjusted €
}
"#;

fn repeated_corpus(fragment: &str, minimum_len: usize) -> String {
    fragment.repeat(minimum_len.div_ceil(fragment.len()))
}

fn bench_pipeline_phases(c: &mut Criterion) {
    let source = repeated_corpus(VALID_ITEM, 64 * KIB);
    let lexed = lex(&source).expect("benchmark corpus fits in Sumi's source coordinate space");
    let cooked = cook(&source, &lexed);
    let input = ParserInput::new(&cooked);

    let parsed = parse_source(source.clone().into_boxed_str())
        .expect("benchmark corpus fits in Sumi's source coordinate space");
    assert!(
        parsed.diagnostics().is_empty(),
        "valid benchmark corpus must remain valid: {:?}",
        parsed.diagnostics().first()
    );

    let mut group = c.benchmark_group("pipeline-phases/medium-valid");
    group.throughput(Throughput::Bytes(source.len() as u64));
    group.bench_function("lex", |b| {
        b.iter_with_large_drop(|| {
            lex(black_box(source.as_str()))
                .expect("benchmark corpus fits in Sumi's source coordinate space")
        });
    });
    group.bench_function("cook", |b| {
        b.iter_with_large_drop(|| cook(black_box(source.as_str()), black_box(&lexed)));
    });
    group.bench_function("parser-input", |b| {
        b.iter_with_large_drop(|| ParserInput::new(black_box(&cooked)));
    });
    group.bench_function("parse", |b| {
        b.iter_with_large_drop(|| parse(black_box(&input)));
    });
    group.finish();
}

fn bench_frontend(c: &mut Criterion) {
    let corpora = [
        ("small-valid", SMALL_VALID.to_owned(), true),
        ("medium-valid", repeated_corpus(VALID_ITEM, 64 * KIB), true),
        ("large-valid", repeated_corpus(VALID_ITEM, 512 * KIB), true),
        (
            "medium-malformed",
            repeated_corpus(MALFORMED_ITEM, 64 * KIB),
            false,
        ),
    ];

    for (name, source, valid) in &corpora {
        let parsed = parse_source(source.clone().into_boxed_str())
            .expect("benchmark corpus fits in Sumi's source coordinate space");
        assert_eq!(
            parsed.diagnostics().is_empty(),
            *valid,
            "benchmark corpus validity changed for {name}: {:?}",
            parsed.diagnostics().first()
        );
    }

    let mut group = c.benchmark_group("frontend");
    for (name, source, _) in &corpora {
        group.throughput(Throughput::Bytes(source.len() as u64));
        group.bench_with_input(BenchmarkId::from_parameter(name), source, |b, source| {
            b.iter_batched(
                || source.clone().into_boxed_str(),
                |source| {
                    parse_source(source)
                        .expect("benchmark corpus fits in Sumi's source coordinate space")
                },
                BatchSize::LargeInput,
            );
        });
    }
    group.finish();
}

criterion_group!(benches, bench_pipeline_phases, bench_frontend);
criterion_main!(benches);
