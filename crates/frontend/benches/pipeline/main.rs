use criterion::{
    BatchSize, BenchmarkId, Criterion, Throughput, black_box, criterion_group, criterion_main,
};
use sumi_format::{normalize, reprint};
use sumi_frontend::parse_source;
use sumi_lexer::lex;
use sumi_syntax::{MAX_DEPTH, ParseEvidence, ParserInput, parse};
use sumi_test::corpus;
use sumi_text::{LineIndex, TextSize};

const KIB: usize = 1024;

const SMALL_VALID: &str = r#"fn transform(value: int, limit: int) -> int {
  let mut doubled = value * 2
  doubled = doubled + 1
  let adjusted = if doubled > limit {
    doubled - limit
  } else {
    blend(doubled, limit)
  }
  return adjusted
}
"#;

// The seeds and damage parameters define the benchmark corpora; see the
// baseline note in `corpus.rs` before touching them.
const MEDIUM_SEED: u64 = 0xBEEF;
const LARGE_SEED: u64 = 0xDECAF;
const DAMAGE_SEED: u64 = 7;
const DAMAGE_STRIDE: usize = 600;

// Nesting depths for the adversarial ladder, pinned so the benchmark names
// stay stable. The first three rungs must parse clean under [`MAX_DEPTH`];
// the last must trip the depth guard and recover past thousands of
// unconsumed closers.
const NESTED_RUNGS: [(usize, bool); 4] = [(4, true), (32, true), (224, true), (4096, false)];

// The positional query batches: unrelated draws, unlike a stride, so
// lookups cannot ride the branch predictor.
const QUERY_SEED: u64 = 0xC0FFEE;
const QUERY_BATCH: usize = 1024;

/// The corpus module keeps its generator private; the query batches only
/// need a pinned stream of bounded draws.
struct Lcg(u64);

impl Lcg {
    fn below(&mut self, n: u32) -> u32 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        ((self.0 >> 33) as u32) % n
    }
}

fn bench_pipeline_phases(c: &mut Criterion) {
    bench_phases(
        c,
        "medium-valid",
        &corpus::generate(64 * KIB, MEDIUM_SEED),
        true,
    );
    bench_phases(
        c,
        "medium-malformed",
        &corpus::corrupt(
            &corpus::generate(64 * KIB, MEDIUM_SEED),
            DAMAGE_SEED,
            DAMAGE_STRIDE,
        ),
        false,
    );
}

fn bench_phases(c: &mut Criterion, corpus_name: &str, source: &str, valid: bool) {
    let lexed = lex(source).expect("benchmark corpus fits in Sumi's source coordinate space");
    let input = ParserInput::new(&lexed);

    let parsed = parse_source(source.to_owned().into_boxed_str())
        .expect("benchmark corpus fits in Sumi's source coordinate space");
    assert_eq!(
        parsed.diagnostics().is_empty(),
        valid,
        "benchmark corpus validity changed for {corpus_name}: {:?}",
        parsed.diagnostics().first()
    );

    let mut group = c.benchmark_group(format!("pipeline-phases/{corpus_name}"));
    group.throughput(Throughput::Bytes(source.len() as u64));
    // This ID measured the old scan plus cook stages together, so it remains
    // the comparable history for the now-unified operation.
    group.bench_function("lex+cook", |b| {
        b.iter_with_large_drop(|| {
            lex(black_box(source)).expect("benchmark corpus fits in Sumi's source coordinate space")
        });
    });
    group.bench_function("parser-input", |b| {
        b.iter_with_large_drop(|| ParserInput::new(black_box(&lexed)));
    });
    group.bench_function("parse", |b| {
        b.iter_with_large_drop(|| parse(black_box(&input)));
    });
    group.finish();
}

fn bench_frontend(c: &mut Criterion) {
    let corpora = [
        ("small-valid", SMALL_VALID.to_owned(), true),
        (
            "medium-valid",
            corpus::generate(64 * KIB, MEDIUM_SEED),
            true,
        ),
        ("large-valid", corpus::generate(512 * KIB, LARGE_SEED), true),
        (
            "medium-malformed",
            corpus::corrupt(
                &corpus::generate(64 * KIB, MEDIUM_SEED),
                DAMAGE_SEED,
                DAMAGE_STRIDE,
            ),
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

/// Functions whose bodies each return one expression nested `depth` groups
/// deep, repeated until the file reaches `total` bytes. Group pairing, Pratt
/// recursion, and the depth guard all scale with nesting, which the
/// realistic corpora keep shallow.
fn nested_groups(total: usize, depth: usize) -> String {
    let mut source = String::with_capacity(total + 64 + 2 * depth);
    let mut index = 0;
    while source.len() < total {
        source.push_str("fn nest");
        source.push_str(&index.to_string());
        source.push_str("() -> int {\n  return ");
        for _ in 0..depth {
            source.push('(');
        }
        source.push('1');
        for _ in 0..depth {
            source.push(')');
        }
        source.push_str("\n}\n");
        index += 1;
    }
    source
}

fn bench_adversarial(c: &mut Criterion) {
    let mut group = c.benchmark_group("adversarial/nested-groups");
    for (depth, valid) in NESTED_RUNGS {
        let source = nested_groups(64 * KIB, depth);
        let parsed = parse_source(source.clone().into_boxed_str())
            .expect("benchmark corpus fits in Sumi's source coordinate space");
        assert_eq!(
            parsed.diagnostics().is_empty(),
            valid,
            "nesting depth {depth} landed on the wrong side of MAX_DEPTH ({MAX_DEPTH}): {:?}",
            parsed.diagnostics().first()
        );
        group.throughput(Throughput::Bytes(source.len() as u64));
        group.bench_with_input(BenchmarkId::from_parameter(depth), &source, |b, source| {
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

fn bench_queries(c: &mut Criterion) {
    let source = corpus::generate(64 * KIB, MEDIUM_SEED);
    let lexed = lex(&source).expect("benchmark corpus fits in Sumi's source coordinate space");
    let input = ParserInput::new(&lexed);
    let parsed = parse(&input);
    let tree = parsed.tree();
    let index = LineIndex::new(&source);

    let mut rng = Lcg(QUERY_SEED);
    let offsets: Vec<TextSize> = (0..QUERY_BATCH)
        .map(|_| TextSize::new(rng.below(source.len() as u32)))
        .collect();
    let tokens: Vec<u32> = (0..QUERY_BATCH)
        .map(|_| rng.below(lexed.len() as u32))
        .collect();

    let mut group = c.benchmark_group("queries/medium-valid");
    group.throughput(Throughput::Bytes(source.len() as u64));
    group.bench_function("line-index", |b| {
        b.iter_with_large_drop(|| LineIndex::new(black_box(&source)));
    });
    group.bench_function("parents", |b| {
        b.iter_with_large_drop(|| black_box(tree).parents());
    });

    group.throughput(Throughput::Elements(QUERY_BATCH as u64));
    group.bench_function("line-col", |b| {
        b.iter(|| {
            black_box(&offsets)
                .iter()
                .map(|&offset| u64::from(index.line_col(offset).line))
                .sum::<u64>()
        });
    });
    group.bench_function("token-at", |b| {
        b.iter(|| {
            black_box(&offsets)
                .iter()
                .map(|&offset| {
                    lexed
                        .token_at(offset)
                        .expect("query offsets lie below the source length")
                })
                .sum::<usize>()
        });
    });
    group.bench_function("covering", |b| {
        b.iter(|| {
            black_box(&tokens)
                .iter()
                .map(|&token| tree.covering(token))
                .sum::<usize>()
        });
    });
    group.bench_function("covering-chain", |b| {
        b.iter(|| {
            black_box(&tokens)
                .iter()
                .map(|&token| tree.covering_chain(token).count())
                .sum::<usize>()
        });
    });
    group.finish();
}

fn bench_format(c: &mut Criterion) {
    let source = corpus::generate(64 * KIB, MEDIUM_SEED);
    let lexed = lex(&source).expect("benchmark corpus fits in Sumi's source coordinate space");
    let parsed = parse(&ParserInput::new(&lexed));
    assert_eq!(
        reprint(parsed.tree(), &lexed, &source),
        source,
        "the tree must reprint its corpus byte for byte"
    );

    // The valid corpus spaces every binary operator; gluing two of them
    // degrades layout without touching structure. Neither pattern occurs
    // in the string literals the generator emits.
    let glued = source.replace(" + ", "+").replace(" * ", "*");
    let glued_lexed = lex(&glued).expect("benchmark corpus fits in Sumi's source coordinate space");
    let glued_parse = parse(&ParserInput::new(&glued_lexed));
    let violations = glued_parse
        .evidence()
        .iter()
        .filter(|evidence| matches!(evidence, ParseEvidence::Violation(_)))
        .count();
    assert!(
        violations > 500,
        "the glued corpus must be violation-rich, found {violations}"
    );

    let mut group = c.benchmark_group("format/medium-valid");
    group.throughput(Throughput::Bytes(source.len() as u64));
    group.bench_function("reprint", |b| {
        b.iter_with_large_drop(|| reprint(black_box(parsed.tree()), &lexed, &source));
    });
    group.finish();

    let mut group = c.benchmark_group("format/medium-glued");
    group.throughput(Throughput::Bytes(glued.len() as u64));
    group.bench_function("normalize", |b| {
        b.iter_with_large_drop(|| normalize(black_box(&glued), &glued_lexed, &glued_parse));
    });
    group.finish();
}

criterion_group!(
    benches,
    bench_pipeline_phases,
    bench_frontend,
    bench_adversarial,
    bench_queries,
    bench_format
);
criterion_main!(benches);
