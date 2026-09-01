//! Recovery scorecard and delimiter-churn telemetry.
//!
//! Everything here is seeded, so the numbers are exactly reproducible and
//! the committed `recovery-scorecard.txt` beside this crate is a reference,
//! not a sample.
//!
//! Part A scores recovery quality over seeded (program, edit) pairs drawn
//! from the same generator the recovery property tests use, per edit class:
//! delete/duplicate/swap/insert crossed with delimiter/non-delimiter. Per
//! edit it measures the untouched-item preservation rate (top-level items
//! not covering the edit's ±2 significant tokens that survive with
//! identical span and shape), diagnostics for the edited file, significant
//! tokens inside recovery-skipped ranges, and evidence entries.
//!
//! Part B breaks one delimiter in a clean corpus — an unmatched opener
//! inserted, or a closer deleted — and counts how far the stream facts
//! churn: significant tokens whose `partner()` or `boundary_before()`
//! changed against the pre-edit stream (edit site excluded), and untouched
//! top-level items disturbed. This quantifies the "unclosed brace re-pairs
//! the whole file" risk.

use std::collections::HashSet;

use sumi_syntax::{NodeKind, ParseEvidence, ParserInput, SyntaxKind, is_bracket};
use sumi_test::{Edit, EditSpan, Front, Programs, apply, changes_delimiter, corpus, front};

/// Measured (program, edit) pairs per Part A class.
const CLASS_TARGET: usize = 10_000;
/// Samples per class drawn from one program, to spread classes over many
/// programs instead of exhausting one.
const PER_PROGRAM: usize = 2;

/// Same LCG as the corpus generator, private to this harness.
struct Lcg(u64);

impl Lcg {
    fn new(seed: u64) -> Self {
        Self(seed ^ 0x9E37_79B9_7F4A_7C15)
    }

    fn below(&mut self, n: usize) -> usize {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        ((self.0 >> 33) as usize) % n
    }

    fn pick<'a, T: ?Sized>(&mut self, items: &'a [&'a T]) -> &'a T {
        items[self.below(items.len())]
    }
}

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

/// The first significant index whose raw token index is `>= raw`.
fn significant_at(input: &ParserInput, raw: u32) -> usize {
    let (mut low, mut high) = (0, input.len());
    while low < high {
        let mid = (low + high) / 2;
        if input.token(mid) < raw {
            low = mid + 1;
        } else {
            high = mid;
        }
    }
    low
}

/// The number of significant tokens whose raw index lies in `[start, end)`.
fn significant_in(input: &ParserInput, start: u32, end: u32) -> u64 {
    (significant_at(input, end) - significant_at(input, start)) as u64
}

/// The top-level `FnItem` nodes of a parse.
fn items(front: &Front) -> Vec<usize> {
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
    touched: &[u32],
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
        let touched: Vec<u32> = touched
            .iter()
            .map(|&index| original.input.token(index))
            .collect();
        let after = front(&edited);

        let (untouched, preserved) =
            preservation(source, original, &touched, impact, &edited, &after);
        if untouched > 0 {
            self.rates.push(preserved as f64 / untouched as f64);
        } else {
            self.unguarded += 1;
        }

        let parsed =
            sumi_frontend::parse_source(edited.as_str().into()).expect("edited sources fit in u32");
        self.diags.push(parsed.diagnostics().len() as u64);

        let mut skipped = 0;
        for evidence in after.parse.evidence() {
            if let ParseEvidence::Recovery(recovery) = evidence {
                for range in &recovery.skipped {
                    skipped += significant_in(&after.input, range.start(), range.end());
                }
            }
        }
        self.skipped.push(skipped);
        self.evidence.push(after.parse.evidence().len() as u64);
    }
}

const DELIMITER_INSERTS: &[&str] = &["(", ")", "{", "}"];
const NON_DELIMITER_INSERTS: &[&str] = &[",", "=", "fn", "let", "else", "x", "0", "+", "-"];

const KIND_NAMES: [&str; 4] = ["delete", "duplicate", "swap", "insert"];
const CLASS_NAMES: [&str; 2] = ["delimiter", "non-delim"];

fn scorecard() {
    let mut rng = Lcg::new(0x5C0E_CA4D);
    let mut programs = Programs::new(0xED17_ED17);
    // stats[kind][0] is the delimiter class, stats[kind][1] the rest.
    let mut stats: [[ClassStats; 2]; 4] = Default::default();
    let mut generated = 0usize;

    while stats
        .iter()
        .flatten()
        .any(|class| class.edits() < CLASS_TARGET)
    {
        let source = programs.next().expect("the program stream is endless");
        generated += 1;
        let original = front(&source);
        let len = original.input.len();
        if len < 2 {
            continue;
        }
        let spans = original.spans();

        let delimiter: Vec<usize> = (0..len)
            .filter(|&index| original.input.get(index).is_some_and(is_bracket))
            .collect();
        let non_delimiter: Vec<usize> = (0..len)
            .filter(|&index| !original.input.get(index).is_some_and(is_bracket))
            .collect();
        let swap_delimiter: Vec<usize> = (0..len)
            .filter(|&index| changes_delimiter(&original.input, index, Edit::Swap))
            .collect();
        let swap_non_delimiter: Vec<usize> = (0..len)
            .filter(|&index| !changes_delimiter(&original.input, index, Edit::Swap))
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
                            DELIMITER_INSERTS
                        } else {
                            NON_DELIMITER_INSERTS
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
    let touched: Vec<u32> = touched
        .iter()
        .map(|&index| before.input.token(index))
        .collect();
    let after = front(&edited);

    let len = before.input.len();
    let expected = match edit {
        Edit::Insert(_) => len + 1,
        Edit::Delete => len - 1,
        _ => unreachable!("part B edits only insert openers or delete closers"),
    };
    if after.input.len() != expected {
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
        let boundary = before.input.boundary_before(i) != after.input.boundary_before(j);
        // A partner that was deleted counts as changed outright.
        let partner = match before.input.partner(i) {
            None => after.input.partner(j).is_some(),
            Some(p) => match map(p) {
                None => true,
                Some(q) => after.input.partner(j) != Some(q),
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

fn churn_base(name: &str, source: &str, edits_per_kind: usize, rng: &mut Lcg) {
    let before = front(source);
    let spans = before.spans();
    let len = before.input.len();
    let closers = |kind: SyntaxKind| -> Vec<usize> {
        (0..len)
            .filter(|&index| before.input.get(index) == Some(kind))
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
    let mut rng = Lcg::new(0xB4A5_E0B5);
    let clean_8k = corpus::generate(8 * 1024, 0xC0FFEE);
    let clean_64k = corpus::generate(64 * 1024, 0xBEEF);
    let clean_1m = corpus::generate(1024 * 1024, 0xDECAF);
    churn_base("clean_8k", &clean_8k, 200, &mut rng);
    churn_base("clean_64k", &clean_64k, 200, &mut rng);
    churn_base("clean_1m", &clean_1m, 50, &mut rng);
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
        assert_eq!(before.input.len(), 29);
        assert_eq!(before.input.get(13), Some(SyntaxKind::Ident));
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
        assert_eq!(before.input.get(17), Some(SyntaxKind::RBrace));
        let sample = churn(BASE, &before, &before.spans(), 17, Edit::Delete)
            .expect("deleting this spaced closer merges no tokens");
        assert_eq!(sample.partner_changed, 1);
        assert_eq!(sample.boundary_changed, 0);
        assert_eq!(sample.any_changed, 1);
        assert_eq!(sample.untouched_disturbed, 0);
    }
}
