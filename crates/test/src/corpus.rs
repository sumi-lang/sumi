//! Corpora for benchmarks and the scorecard: generated programs one after
//! another to a size, clean or with one edit in every stride of tokens.

use crate::{Edit, INSERTS, Programs, apply, front};

/// A seeded stream of bounded draws, for a harness that selects outside a
/// proptest runner.
pub struct Rng(u64);

impl Rng {
    pub fn new(seed: u64) -> Self {
        Self(seed ^ 0x9E37_79B9_7F4A_7C15)
    }

    pub fn below(&mut self, n: usize) -> usize {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        ((self.0 >> 33) as usize) % n
    }

    pub fn pick<'a, T: ?Sized>(&mut self, items: &'a [&'a T]) -> &'a T {
        items[self.below(items.len())]
    }
}

/// At least `bytes` of well-formed source: the programs [`Programs`] draws
/// from `seed`, one after another.
pub fn generate(bytes: usize, seed: u64) -> String {
    let mut source = String::with_capacity(bytes + 1024);
    for program in Programs::new(seed) {
        source.push_str(&program);
        source.push('\n');
        if source.len() >= bytes {
            break;
        }
    }
    source
}

/// `source` with one edit from the recovery properties' pool in every
/// `stride` significant tokens.
pub fn damage(source: &str, seed: u64, stride: usize) -> String {
    assert!(
        stride >= 2,
        "an edit needs a token to land on and a neighbour"
    );
    let spans = front(source).spans();
    let mut rng = Rng::new(seed);
    let mut damaged = source.to_owned();
    // Later edits first: the original's spans still locate every earlier
    // token, and a swap reaches one token to the right.
    let mut end = spans.len();
    while end > stride {
        let index = end - stride + rng.below(stride - 1);
        let edit = match rng.below(4) {
            0 => Edit::Delete,
            1 => Edit::Duplicate,
            2 => Edit::Swap,
            _ => Edit::Insert(rng.pick(INSERTS)),
        };
        damaged = apply(&damaged, &spans, index, edit).0;
        end = index - 1;
    }
    damaged
}
