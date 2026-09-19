//! The recovery scorecard: seeded, count-based measurements of recovery
//! quality, so `cargo run --release -p sumi-scorecard` reproduces the
//! committed `recovery-scorecard.txt` byte for byte, which CI checks. It
//! is a leaf package of its own, not an `xtask` command, so that `xtask`,
//! which seeds the fuzzer, depends on no workspace crate.
//!
//! Part A makes one edit per (program, edit) pair drawn from the recovery
//! properties' generator, per edit kind crossed with whether a delimiter
//! changes, and holds every untouched top-level item to surviving with
//! its span and shape: preservation 1.0. Part B inserts an opener or
//! deletes a closer in a clean corpus and counts the significant tokens
//! whose partner or boundary changed, which stays within the bracket
//! nesting around the edit, and the untouched items disturbed, which is
//! 0. Part C deletes one quote of a string literal, an edit inside a
//! token, and measures how far the literal then reaches: its line at
//! most, and no item disturbed.

use std::collections::HashSet;

use sumi_lexer::LexedFile;
use sumi_syntax::{
    NodeIdx, NodeKind, ParseEvidence, ParserInput, RawIdx, SigIdx, SyntaxKind, is_bracket,
};
use sumi_test::corpus::{self, Rng};
use sumi_test::{Edit, EditSpan, Front, INSERTS, Programs, apply, changes_delimiter, front};

/// Measured (program, edit) pairs per Part A class.
const CLASS_TARGET: usize = 10_000;
/// Samples per class drawn from one program, to spread classes over many
/// programs instead of exhausting one.
const PER_PROGRAM: usize = 2;

fn mean_f64(values: &[f64]) -> f64 {
    values.iter().sum::<f64>() / values.len().max(1) as f64
}

fn mean_u64(values: &[u64]) -> f64 {
    values.iter().sum::<u64>() as f64 / values.len().max(1) as f64
}

/// Nearest-rank percentile of an unsorted sample; `q` in (0, 1].
fn percentile_u64(values: &[u64], q: f64) -> u64 {
    let mut sorted = values.to_vec();
    sorted.sort_unstable();
    sorted[((q * sorted.len() as f64).ceil() as usize).clamp(1, sorted.len()) - 1]
}

fn percentile_f64(values: &[f64], q: f64) -> f64 {
    let mut sorted = values.to_vec();
    sorted.sort_by(|a, b| a.partial_cmp(b).expect("rates are never NaN"));
    sorted[((q * sorted.len() as f64).ceil() as usize).clamp(1, sorted.len()) - 1]
}

/// The number of diagnostics the frontend reports for `source`.
fn diagnostics(source: &str, front: &Front) -> u64 {
    sumi_frontend::diagnostics(source, &front.lexed, &front.parse).len() as u64
}

fn sig(index: usize) -> SigIdx {
    SigIdx::new(u32::try_from(index).expect("significant positions fit in u32"))
}

/// The first significant index whose raw token index is `>= raw`.
fn significant_at(input: &ParserInput, raw: RawIdx) -> usize {
    let (mut low, mut high) = (0, input.len());
    while low < high {
        let mid = (low + high) / 2;
        if input.token(sig(mid)) < raw {
            low = mid + 1;
        } else {
            high = mid;
        }
    }
    low
}

/// The number of significant tokens whose raw index lies in `[start, end)`.
fn significant_in(input: &ParserInput, start: RawIdx, end: RawIdx) -> u64 {
    (significant_at(input, end) - significant_at(input, start)) as u64
}

/// The top-level `FnItem` nodes of a parse.
fn items(front: &Front) -> Vec<NodeIdx> {
    let tree = front.parse.tree();
    tree.children(tree.root())
        .filter(|&node| tree.kind(node) == NodeKind::FnItem)
        .collect()
}

/// Item survival across one edit: of the original top-level items covering
/// none of the touched raw tokens, how many appear in the edited parse with
/// identical span and shape.
fn preservation(
    source: &str,
    original: &Front,
    touched: &[RawIdx],
    impact: EditSpan,
    edited: &str,
    after: &Front,
) -> (usize, usize) {
    let survivors: HashSet<_> = items(after)
        .into_iter()
        .map(|node| (after.node_span(node), after.shape(edited, node)))
        .collect();

    let tree = original.parse.tree();
    let (mut untouched, mut preserved) = (0, 0);
    for item in items(original) {
        if touched
            .iter()
            .any(|&token| tree.first_token(item) <= token && token < tree.end_token(item))
        {
            continue;
        }
        untouched += 1;
        let shape = original.shape(source, item);
        let span = impact.map(original.node_span(item));
        if survivors.contains(&(span, shape)) {
            preserved += 1;
        }
    }
    (untouched, preserved)
}

// --- Part A: the scorecard. ---

#[derive(Default)]
struct ClassStats {
    /// Preservation rate per edit with at least one untouched item.
    rates: Vec<f64>,
    /// Edits with no untouched item to guard.
    unguarded: usize,
    diags: Vec<u64>,
    skipped: Vec<u64>,
    evidence: Vec<u64>,
}

impl ClassStats {
    fn edits(&self) -> usize {
        self.diags.len()
    }

    fn record(
        &mut self,
        source: &str,
        original: &Front,
        spans: &[(usize, usize)],
        index: usize,
        edit: Edit,
    ) {
        let (edited, touched, _moved, impact) = apply(source, spans, index, edit);
        let touched: Vec<RawIdx> = touched
            .iter()
            .map(|&index| original.input().token(sig(index)))
            .collect();
        let after = front(&edited);

        let (untouched, preserved) =
            preservation(source, original, &touched, impact, &edited, &after);
        if untouched > 0 {
            self.rates.push(preserved as f64 / untouched as f64);
        } else {
            self.unguarded += 1;
        }

        self.diags.push(diagnostics(&edited, &after));

        let mut skipped = 0;
        for evidence in after.parse.evidence() {
            if let ParseEvidence::Recovery(recovery) = evidence {
                for range in &recovery.skipped {
                    skipped += significant_in(after.input(), range.start(), range.end());
                }
            }
        }
        self.skipped.push(skipped);
        self.evidence.push(after.parse.evidence().len() as u64);
    }
}

const KIND_NAMES: [&str; 4] = ["delete", "duplicate", "swap", "insert"];
const CLASS_NAMES: [&str; 2] = ["delimiter", "non-delim"];

fn scorecard() {
    let mut rng = Rng::new(0x5C0E_CA4D);
    let mut programs = Programs::new(0xED17_ED17);
    // stats[kind][0] is the delimiter class, stats[kind][1] the rest.
    let mut stats: [[ClassStats; 2]; 4] = Default::default();
    let mut generated = 0usize;
    // The insert pools: brackets, and the rest.
    let (delimiter_inserts, non_delimiter_inserts): (Vec<&str>, Vec<&str>) =
        INSERTS.iter().partition(|&&text| {
            SyntaxKind::ALL
                .iter()
                .any(|&kind| is_bracket(kind) && kind.text() == Some(text))
        });

    while stats
        .iter()
        .flatten()
        .any(|class| class.edits() < CLASS_TARGET)
    {
        let source = programs.next().expect("the program stream is endless");
        generated += 1;
        let original = front(&source);
        let len = original.input().len();
        if len < 2 {
            continue;
        }
        let spans = original.spans();

        let delimiter: Vec<usize> = (0..len)
            .filter(|&index| original.input().get(sig(index)).is_some_and(is_bracket))
            .collect();
        let non_delimiter: Vec<usize> = (0..len)
            .filter(|&index| !original.input().get(sig(index)).is_some_and(is_bracket))
            .collect();
        let swap_delimiter: Vec<usize> = (0..len)
            .filter(|&index| changes_delimiter(original.input(), index, Edit::Swap))
            .collect();
        let swap_non_delimiter: Vec<usize> = (0..len)
            .filter(|&index| !changes_delimiter(original.input(), index, Edit::Swap))
            .collect();
        let all: Vec<usize> = (0..len).collect();

        for (kind, classes) in stats.iter_mut().enumerate() {
            for (class, class_stats) in classes.iter_mut().enumerate() {
                let candidates = match (kind, class) {
                    (0 | 1, 0) => &delimiter,
                    (0 | 1, 1) => &non_delimiter,
                    (2, 0) => &swap_delimiter,
                    (2, 1) => &swap_non_delimiter,
                    (3, _) => &all,
                    _ => unreachable!(),
                };
                for _ in 0..PER_PROGRAM {
                    if candidates.is_empty() || class_stats.edits() >= CLASS_TARGET {
                        break;
                    }
                    let index = candidates[rng.below(candidates.len())];
                    let edit = match kind {
                        0 => Edit::Delete,
                        1 => Edit::Duplicate,
                        2 => Edit::Swap,
                        _ => Edit::Insert(rng.pick(if class == 0 {
                            &delimiter_inserts
                        } else {
                            &non_delimiter_inserts
                        })),
                    };
                    class_stats.record(&source, &original, &spans, index, edit);
                }
            }
        }
    }

    println!("== Part A: recovery scorecard ==");
    println!(
        "{} programs generated; {} measured pairs per class; preservation is",
        generated, CLASS_TARGET
    );
    println!("over untouched top-level items (edits guarding none are counted apart).");
    println!();
    println!(
        "{:<22} {:>6} {:>8}  {:>9} {:>9} {:>9}",
        "class", "edits", "guarded", "pres_mean", "pres_p95", "pres_min"
    );
    for kind in 0..4 {
        for class in 0..2 {
            let s = &stats[kind][class];
            let min = s.rates.iter().copied().fold(f64::INFINITY, f64::min);
            println!(
                "{:<22} {:>6} {:>8}  {:>9.5} {:>9.5} {:>9.5}",
                format!("{}/{}", KIND_NAMES[kind], CLASS_NAMES[class]),
                s.edits(),
                s.rates.len(),
                mean_f64(&s.rates),
                percentile_f64(&s.rates, 0.95),
                min,
            );
        }
    }
    println!();
    println!(
        "{:<22} {:>10} {:>9}  {:>12} {:>11}  {:>13} {:>12}",
        "class",
        "diags_mean",
        "diags_p95",
        "skipped_mean",
        "skipped_p95",
        "evidence_mean",
        "evidence_p95"
    );
    for kind in 0..4 {
        for class in 0..2 {
            let s = &stats[kind][class];
            println!(
                "{:<22} {:>10.3} {:>9}  {:>12.3} {:>11}  {:>13.3} {:>12}",
                format!("{}/{}", KIND_NAMES[kind], CLASS_NAMES[class]),
                mean_u64(&s.diags),
                percentile_u64(&s.diags, 0.95),
                mean_u64(&s.skipped),
                percentile_u64(&s.skipped, 0.95),
                mean_u64(&s.evidence),
                percentile_u64(&s.evidence, 0.95),
            );
        }
    }
}

// --- Part B: delimiter-breaking churn. ---

struct ChurnSample {
    partner_changed: u64,
    boundary_changed: u64,
    any_changed: u64,
    untouched_disturbed: u64,
}

/// Stream-fact churn across one insert-opener or delete-closer edit.
/// `None` when the edit merged or split neighbouring tokens, leaving no
/// one-to-one alignment to compare against.
fn churn(
    source: &str,
    before: &Front,
    spans: &[(usize, usize)],
    index: usize,
    edit: Edit,
) -> Option<ChurnSample> {
    let (edited, touched, _moved, impact) = apply(source, spans, index, edit);
    let touched: Vec<RawIdx> = touched
        .iter()
        .map(|&index| before.input().token(sig(index)))
        .collect();
    let after = front(&edited);

    let len = before.input().len();
    let expected = match edit {
        Edit::Insert(_) => len + 1,
        Edit::Delete => len - 1,
        _ => unreachable!("part B edits only insert openers or delete closers"),
    };
    if after.input().len() != expected {
        return None;
    }
    // The edited stream shifted by one at the edit point; the deleted token
    // itself has no image.
    let map = |i: usize| -> Option<usize> {
        match edit {
            Edit::Insert(_) => Some(if i < index { i } else { i + 1 }),
            Edit::Delete if i == index => None,
            Edit::Delete => Some(if i < index { i } else { i - 1 }),
            _ => unreachable!(),
        }
    };

    let (mut partner_changed, mut boundary_changed, mut any_changed) = (0, 0, 0);
    for i in (0..len).filter(|&i| map(i).is_some()) {
        let j = map(i).expect("filtered to mapped tokens");
        let boundary =
            before.input().boundary_before(sig(i)) != after.input().boundary_before(sig(j));
        // A partner that was deleted counts as changed outright.
        let partner = match before.input().partner(sig(i)) {
            None => after.input().partner(sig(j)).is_some(),
            Some(p) => match map(p.to_usize()) {
                None => true,
                Some(q) => after.input().partner(sig(j)) != Some(sig(q)),
            },
        };
        partner_changed += u64::from(partner);
        boundary_changed += u64::from(boundary);
        any_changed += u64::from(partner || boundary);
    }

    let (untouched, preserved) = preservation(source, before, &touched, impact, &edited, &after);
    Some(ChurnSample {
        partner_changed,
        boundary_changed,
        any_changed,
        untouched_disturbed: (untouched - preserved) as u64,
    })
}

fn churn_base(name: &str, source: &str, edits_per_kind: usize, rng: &mut Rng) {
    let before = front(source);
    let spans = before.spans();
    let len = before.input().len();
    let closers = |kind: SyntaxKind| -> Vec<usize> {
        (0..len)
            .filter(|&index| before.input().get(sig(index)) == Some(kind))
            .collect()
    };
    let rbraces = closers(SyntaxKind::RBrace);
    let rparens = closers(SyntaxKind::RParen);

    println!(
        "{name}: {len} significant tokens, {} top-level items",
        items(&before).len()
    );
    let kinds: [(&str, Edit, &[usize]); 4] = [
        ("insert {", Edit::Insert("{"), &[]),
        ("insert (", Edit::Insert("("), &[]),
        ("delete }", Edit::Delete, &rbraces),
        ("delete )", Edit::Delete, &rparens),
    ];
    for (label, edit, candidates) in kinds {
        let mut samples: Vec<ChurnSample> = Vec::new();
        let mut unaligned = 0usize;
        for _ in 0..edits_per_kind {
            let index = if candidates.is_empty() {
                rng.below(len)
            } else {
                candidates[rng.below(candidates.len())]
            };
            match churn(source, &before, &spans, index, edit) {
                Some(sample) => samples.push(sample),
                None => unaligned += 1,
            }
        }
        let stat = |select: fn(&ChurnSample) -> u64| -> (u64, u64, u64) {
            let values: Vec<u64> = samples.iter().map(select).collect();
            (
                percentile_u64(&values, 0.50),
                percentile_u64(&values, 0.95),
                *values.iter().max().expect("every kind takes samples"),
            )
        };
        let partner = stat(|s| s.partner_changed);
        let boundary = stat(|s| s.boundary_changed);
        let any = stat(|s| s.any_changed);
        let items = stat(|s| s.untouched_disturbed);
        println!(
            "  {label:<9} n={:<4} unaligned={unaligned:<3} partner p50/p95/max {}/{}/{}  \
             boundary {}/{}/{}  any {}/{}/{}  items_disturbed {}/{}/{}",
            samples.len(),
            partner.0,
            partner.1,
            partner.2,
            boundary.0,
            boundary.1,
            boundary.2,
            any.0,
            any.1,
            any.2,
            items.0,
            items.1,
            items.2,
        );
    }
}

// --- Part C: one quote deleted from a string literal, the one literal
// form with delimiters. ---

fn is_string(lexed: &LexedFile, index: RawIdx) -> bool {
    lexed.kind(index) == SyntaxKind::StringLiteral
}

struct LiteralSample {
    /// Bytes of the longest literal token left where the edited one stood:
    /// how far the stray delimiter reaches.
    spread: u64,
    diags: u64,
    untouched_disturbed: u64,
}

/// The string literal at `token` with its opening quote deleted, or its
/// closing one.
fn literal_edit(source: &str, before: &Front, token: RawIdx, opener: bool) -> LiteralSample {
    let range = before.lexed.range(token);
    let (start, end) = (range.start().to_usize(), range.end().to_usize());
    let cut = if opener { start } else { end - 1 };
    let edited = format!("{}{}", &source[..cut], &source[cut + 1..]);
    let impact = EditSpan::new(cut, cut + 1, cut);
    let index = significant_at(before.input(), token);
    let touched: Vec<RawIdx> = (index.saturating_sub(2)
        ..=(index + 2).min(before.input().len() - 1))
        .map(|index| before.input().token(sig(index)))
        .collect();
    let after = front(&edited);

    let (untouched, preserved) = preservation(source, before, &touched, impact, &edited, &after);
    // Where the token stood, in the edited source.
    let stood = start..end - 1;
    let spread = after
        .lexed
        .indices()
        .filter(|&index| is_string(&after.lexed, index))
        .map(|index| after.lexed.range(index))
        .filter(|range| {
            range.start().to_usize() < stood.end && range.end().to_usize() > stood.start
        })
        .map(|range| (range.end().to_usize() - range.start().to_usize()) as u64)
        .max()
        .unwrap_or(0);
    LiteralSample {
        spread,
        diags: diagnostics(&edited, &after),
        untouched_disturbed: (untouched - preserved) as u64,
    }
}

fn literal_edits(name: &str, source: &str, edits_per_class: usize, rng: &mut Rng) {
    let before = front(source);
    assert_eq!(
        diagnostics(source, &before),
        0,
        "the literal corpus must be valid"
    );
    let literals: Vec<RawIdx> = before
        .lexed
        .indices()
        .filter(|&index| is_string(&before.lexed, index))
        .collect();
    println!(
        "{name}: {} bytes, {} literals, {} top-level items",
        source.len(),
        literals.len(),
        items(&before).len()
    );
    for (label, opener) in [("delete \" closer", false), ("delete \" opener", true)] {
        let samples: Vec<LiteralSample> = (0..edits_per_class)
            .map(|_| {
                let token = literals[rng.below(literals.len())];
                literal_edit(source, &before, token, opener)
            })
            .collect();
        let stat = |select: fn(&LiteralSample) -> u64| -> (u64, u64, u64) {
            let values: Vec<u64> = samples.iter().map(select).collect();
            (
                percentile_u64(&values, 0.50),
                percentile_u64(&values, 0.95),
                *values.iter().max().expect("every class takes samples"),
            )
        };
        let spread = stat(|s| s.spread);
        let diags = stat(|s| s.diags);
        let items = stat(|s| s.untouched_disturbed);
        println!(
            "  {:<18} n={:<4} spread p50/p95/max {}/{}/{}  diags {}/{}/{}  items_disturbed {}/{}/{}",
            label,
            samples.len(),
            spread.0,
            spread.1,
            spread.2,
            diags.0,
            diags.1,
            diags.2,
            items.0,
            items.1,
            items.2,
        );
    }
}

fn main() {
    println!("recovery-scorecard");
    println!();
    scorecard();
    println!();
    println!("== Part B: delimiter-breaking churn over clean corpora ==");
    println!("churn = original significant tokens (edit site excluded) whose partner()");
    println!("or boundary_before() changed; items_disturbed = untouched top-level items");
    println!("that no longer survive with identical span and shape.");
    println!();
    let mut rng = Rng::new(0xB4A5_E0B5);
    let clean_8k = corpus::generate(8 * 1024, 0xC0FFEE);
    let clean_64k = corpus::generate(64 * 1024, 0xBEEF);
    let clean_1m = corpus::generate(1024 * 1024, 0xDECAF);
    churn_base("clean_8k", &clean_8k, 200, &mut rng);
    churn_base("clean_64k", &clean_64k, 200, &mut rng);
    churn_base("clean_1m", &clean_1m, 50, &mut rng);
    println!();
    println!("== Part C: one delimiter deleted inside a literal ==");
    println!("spread = bytes of the longest literal token left where the edited one stood: how");
    println!("far the stray delimiter reaches: a literal reaches the end of its line at most.");
    println!();
    let mut rng = Rng::new(0x11E4_A15E);
    literal_edits("clean_64k", &clean_64k, 200, &mut rng);
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Two items; the significant tokens of the first are indices 0..18,
    /// with `g(a)`'s callee at 13 and the body's `}` at 17.
    const BASE: &str =
        "fn f() {\n    let a = (1 + 2)\n    g(a)\n}\n\nfn g(x: Int) {\n    return x\n}\n";

    /// Hand-checked churn for an unmatched `{` inserted mid-body: the
    /// body's `{` loses its partner and its `}` re-pairs with the insert
    /// (2 partner changes), the insert absorbs the line break before the
    /// callee (1 boundary change), and the untouched second item survives.
    /// The expectations hold with the pairing reset on or off: the second
    /// item's boundary resets a stack that is already reduced to the one
    /// unmatched opener.
    #[test]
    fn churn_counts_an_inserted_opener_by_hand() {
        let before = front(BASE);
        assert_eq!(before.input().len(), 29);
        assert_eq!(before.input().get(sig(13)), Some(SyntaxKind::Ident));
        let sample = churn(BASE, &before, &before.spans(), 13, Edit::Insert("{"))
            .expect("a punctuation insert never merges tokens");
        assert_eq!(sample.partner_changed, 2);
        assert_eq!(sample.boundary_changed, 1);
        assert_eq!(sample.any_changed, 3);
        assert_eq!(sample.untouched_disturbed, 0);
    }

    /// Hand-checked churn for the body's `}` deleted: only its `{` loses a
    /// partner. The second item sits within two significant tokens of the
    /// edit, so no item is untouched and none can count as disturbed.
    #[test]
    fn churn_counts_a_deleted_closer_by_hand() {
        let before = front(BASE);
        assert_eq!(before.input().get(sig(17)), Some(SyntaxKind::RBrace));
        let sample = churn(BASE, &before, &before.spans(), 17, Edit::Delete)
            .expect("deleting this spaced closer merges no tokens");
        assert_eq!(sample.partner_changed, 1);
        assert_eq!(sample.boundary_changed, 0);
        assert_eq!(sample.any_changed, 1);
        assert_eq!(sample.untouched_disturbed, 0);
    }
}
