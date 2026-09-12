//! A lattice-join solver: union-find classes, a join-semilattice payload on
//! each class, and directed flow between classes with a transfer function on
//! every edge. In dataflow terms, a monotone framework whose nodes are
//! equivalence classes.
//!
//! The solver knows nothing about types. An instance chooses the [`Lattice`]:
//! what the evidence on a class is, how two pieces of it combine, and how
//! evidence changes when it crosses a flow. Scalar type inference in `typing`
//! carries the set of types claimed for a class with where each claim came
//! from; an integer-range analysis would carry an interval, an effect
//! analysis a set of effects, and a tuple of lattices carries all of them at
//! once through the same code.
//!
//! Three constraint forms feed it. [`equal`](Solver::equal) merges two
//! classes and joins their evidence, and because join is commutative,
//! associative, and idempotent the order of arrival is invisible in the
//! result. [`known`](Solver::known) opens a class with a fact, what it is
//! known to be on its own account; [`expect`](Solver::expect) joins into a
//! class what one use of it demands, and only facts survive a
//! [`replay`](Solver::replay). [`flow`](Solver::flow) lets evidence
//! pass from one class to another and never back: the consumer learns
//! everything the provider knows, transformed by the edge, and the provider
//! is unaffected by what its consumers demand, which keeps blame on the
//! consumer's side. Equalities and evidence are applied as they arrive; flows
//! are settled by [`solve`](Solver::solve), a worklist over the flow graph.
//!
//! A conflict is a lattice element like any other. The solver never retracts
//! evidence or stops at the first disagreement, so when an instance reads a
//! class it sees every claim made about it, and the classes around a
//! conflicted one are untouched.

use std::collections::VecDeque;
use std::num::NonZeroUsize;

/// The evidence a solver carries on each class: a join-semilattice with a
/// transfer function for flows.
///
/// `join` must be commutative, associative, and idempotent, with `bottom` as
/// its identity; those laws are what make the solved evidence independent of
/// the order constraints arrive in. `transfer` must be monotone. Every
/// ascending chain must be finite, or [`Solver::solve`] need not terminate: a
/// class may only grow a bounded number of times.
pub trait Lattice: Clone + Eq {
    /// What a flow edge carries: how evidence changes crossing it.
    type Edge;

    /// No evidence: the identity of `join`.
    fn bottom() -> Self;

    /// Join `other` into `self`, reporting whether `self` grew.
    fn join(&mut self, other: &Self) -> bool;

    /// The evidence a consumer receives when `self` crosses `edge`.
    fn transfer(&self, edge: &Self::Edge) -> Self;
}

/// Two lattices side by side: evidence of both kinds on one class, joined
/// componentwise and transferred by a pair of edges. Tuples nest, so any
/// number of analyses share one solver.
impl<A: Lattice, B: Lattice> Lattice for (A, B) {
    type Edge = (A::Edge, B::Edge);

    fn bottom() -> Self {
        (A::bottom(), B::bottom())
    }

    fn join(&mut self, other: &Self) -> bool {
        let a = self.0.join(&other.0);
        let b = self.1.join(&other.1);
        a | b
    }

    fn transfer(&self, edge: &Self::Edge) -> Self {
        (self.0.transfer(&edge.0), self.1.transfer(&edge.1))
    }
}

/// A member of some class: what the solver hands out and takes back.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Var(u32);

impl Var {
    fn index(self) -> usize {
        self.0 as usize
    }
}

pub struct Solver<L: Lattice> {
    parent: Vec<u32>,
    size: Vec<u32>,
    /// Meaningful at roots only.
    evidence: Vec<L>,
    facts: Vec<(Var, L)>,
    /// `(provider, consumer)` edges and what they carry, settled by `solve`.
    flows: Vec<(Var, Var, L::Edge)>,
}

impl<L: Lattice> Default for Solver<L> {
    fn default() -> Self {
        Self::with_capacity(0, 0)
    }
}

impl<L: Lattice> Solver<L> {
    /// A solver with room for `classes` classes and as many facts, and for
    /// `flows` flows, before any vector grows. Only a guide.
    pub fn with_capacity(classes: usize, flows: usize) -> Self {
        Self {
            parent: Vec::with_capacity(classes),
            size: Vec::with_capacity(classes),
            evidence: Vec::with_capacity(classes),
            facts: Vec::with_capacity(classes),
            flows: Vec::with_capacity(flows),
        }
    }

    fn with_classes(n: usize) -> Self {
        Self {
            parent: (0..n as u32).collect(),
            size: vec![1; n],
            evidence: vec![L::bottom(); n],
            facts: Vec::new(),
            flows: Vec::new(),
        }
    }

    pub fn fresh(&mut self) -> Var {
        self.open(L::bottom())
    }

    fn open(&mut self, evidence: L) -> Var {
        let id = u32::try_from(self.parent.len()).expect("class count fits u32");
        self.parent.push(id);
        self.size.push(1);
        self.evidence.push(evidence);
        Var(id)
    }

    fn root(&self, mut id: usize) -> usize {
        while self.parent[id] as usize != id {
            id = self.parent[id] as usize;
        }
        id
    }

    fn compress(&mut self, mut id: usize) -> usize {
        let root = self.root(id);
        while self.parent[id] as usize != id {
            let next = self.parent[id] as usize;
            self.parent[id] = root as u32;
            id = next;
        }
        root
    }

    /// The evidence on `var`'s class.
    pub fn evidence(&self, var: Var) -> &L {
        &self.evidence[self.root(var.index())]
    }

    /// Join evidence one use of `var` demands into its class. Not remembered
    /// by a replay, which re-applies expectations one at a time.
    pub fn expect(&mut self, var: Var, evidence: &L) {
        let root = self.compress(var.index());
        self.evidence[root].join(evidence);
    }

    /// A fresh class known to carry `evidence` on its own account: an
    /// annotation, or a literal. A fact; it survives a replay.
    pub fn known(&mut self, evidence: L) -> Var {
        let var = self.open(evidence.clone());
        self.facts.push((var, evidence));
        var
    }

    /// Merge the classes of `a` and `b`, joining their evidence.
    pub fn equal(&mut self, a: Var, b: Var) {
        let (mut a, mut b) = (self.compress(a.index()), self.compress(b.index()));
        if a == b {
            return;
        }
        if self.size[a] < self.size[b] {
            std::mem::swap(&mut a, &mut b);
        }
        self.parent[b] = a as u32;
        self.size[a] += self.size[b];
        let absorbed = std::mem::replace(&mut self.evidence[b], L::bottom());
        self.evidence[a].join(&absorbed);
    }

    /// Let everything `provider`'s class learns reach `consumer`'s class
    /// through `edge`, and nothing travel back. Settled by `solve`.
    pub fn flow(&mut self, provider: Var, consumer: Var, edge: L::Edge) {
        self.flows.push((provider, consumer, edge));
    }

    /// A fresh class that `provider` flows into through `edge`.
    pub fn import(&mut self, provider: Var, edge: L::Edge) -> Var {
        let consumer = self.fresh();
        self.flow(provider, consumer, edge);
        consumer
    }

    /// Settle every flow: propagate evidence along the flow graph until no
    /// class changes. Call once every equality is in; a flow between classes
    /// unioned afterwards is not revisited. A class is visited once for each
    /// time it grows while not already waiting, and a visit scans its
    /// outgoing flows, so the work is bounded by the flows times the height
    /// of the lattice.
    pub fn solve(&mut self) {
        let n = self.parent.len();
        for id in 0..n {
            self.compress(id);
        }
        // Adjacency by provider root as one-based links, so `None` is compact.
        // Prepending in reverse keeps each provider's consumers in order.
        let mut outgoing = vec![None; n];
        let mut edges = Vec::with_capacity(self.flows.len());
        for (index, (provider, consumer, _)) in self.flows.iter().enumerate().rev() {
            let provider = self.root(provider.index());
            let consumer = self.root(consumer.index());
            edges.push((consumer, index, outgoing[provider]));
            outgoing[provider] = NonZeroUsize::new(edges.len());
        }
        // A class waits in the queue at most once however often it grows
        // before its turn: a join can improve evidence in ways no transfer
        // passes on, and every visit rescans every outgoing flow. Only a
        // provider with something to deliver is worth a visit.
        let bottom = L::bottom();
        let mut queued = vec![false; n];
        let mut queue = VecDeque::new();
        for id in 0..n {
            if outgoing[id].is_some() && self.evidence[id] != bottom {
                queued[id] = true;
                queue.push_back(id);
            }
        }
        while let Some(provider) = queue.pop_front() {
            queued[provider] = false;
            let evidence = self.evidence[provider].clone();
            let mut edge = outgoing[provider];
            while let Some(index) = edge {
                let (consumer, flow, next) = edges[index.get() - 1];
                edge = next;
                let delivered = evidence.transfer(&self.flows[flow].2);
                if self.evidence[consumer].join(&delivered) && !queued[consumer] {
                    queued[consumer] = true;
                    queue.push_back(consumer);
                }
            }
        }
    }

    /// A solver over the same classes as singletons again, carrying only the
    /// facts and what `export` lets each settled flow deliver to its consumer.
    /// Replaying expectations one at a time on it attributes a disagreement
    /// to the expectation that first raised it, with the flows final rather
    /// than provisional.
    pub fn replay(&self, export: impl Fn(&L, &L::Edge) -> Option<L>) -> Self {
        let mut replay = Self::with_classes(self.parent.len());
        for (var, evidence) in &self.facts {
            replay.expect(*var, evidence);
        }
        for (provider, consumer, edge) in &self.flows {
            if let Some(evidence) = export(self.evidence(*provider), edge) {
                replay.expect(*consumer, &evidence);
            }
        }
        replay
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A set of up to eight claims, joined by union: the shape scalar type
    /// inference uses, and an effect set alike.
    #[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
    struct Set(u8);

    impl Lattice for Set {
        type Edge = ();

        fn bottom() -> Self {
            Self(0)
        }

        fn join(&mut self, other: &Self) -> bool {
            let before = self.0;
            self.0 |= other.0;
            before != self.0
        }

        fn transfer(&self, (): &()) -> Self {
            *self
        }
    }

    /// An integer range, joined by intersection: more evidence is a narrower
    /// band, and an empty band is the conflict. Crossing a flow shifts the
    /// band by the edge's offset, as a `+ k` would.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    struct Interval {
        lo: i64,
        hi: i64,
    }

    impl Interval {
        fn new(lo: i64, hi: i64) -> Self {
            Self { lo, hi }
        }

        fn is_empty(self) -> bool {
            self.lo > self.hi
        }
    }

    impl Lattice for Interval {
        type Edge = i64;

        fn bottom() -> Self {
            Self::new(i64::MIN, i64::MAX)
        }

        fn join(&mut self, other: &Self) -> bool {
            let before = *self;
            self.lo = self.lo.max(other.lo);
            self.hi = self.hi.min(other.hi);
            before != *self
        }

        fn transfer(&self, offset: &i64) -> Self {
            Self::new(
                self.lo.saturating_add(*offset),
                self.hi.saturating_add(*offset),
            )
        }
    }

    #[test]
    fn equalities_join_and_flows_deliver() {
        let mut solver = Solver::<Set>::default();
        let a = solver.fresh();
        let b = solver.fresh();
        let c = solver.import(b, ());
        solver.expect(a, &Set(1));
        solver.equal(a, b);
        solver.expect(b, &Set(2));
        solver.solve();
        assert_eq!(*solver.evidence(a), Set(3));
        assert_eq!(*solver.evidence(b), Set(3));
        assert_eq!(*solver.evidence(c), Set(3));
    }

    #[test]
    fn flows_never_carry_evidence_back() {
        let mut solver = Solver::<Set>::default();
        let provider = solver.fresh();
        let consumer = solver.import(provider, ());
        solver.expect(consumer, &Set(1));
        solver.solve();
        assert_eq!(*solver.evidence(provider), Set::bottom());
        assert_eq!(*solver.evidence(consumer), Set(1));
    }

    #[test]
    fn intervals_narrow_transfer_and_empty_out() {
        let mut solver = Solver::<Interval>::default();
        let x = solver.known(Interval::new(0, 10));
        let y = solver.import(x, 100);
        solver.expect(x, &Interval::new(5, 20));
        solver.expect(y, &Interval::new(130, 140));
        solver.solve();
        assert_eq!(*solver.evidence(x), Interval::new(5, 10));
        assert!(solver.evidence(y).is_empty());
        let replay =
            solver.replay(|band, offset| (!band.is_empty()).then(|| band.transfer(offset)));
        assert_eq!(*replay.evidence(x), Interval::new(0, 10));
        assert_eq!(*replay.evidence(y), Interval::new(105, 110));
    }

    #[test]
    fn products_join_and_transfer_componentwise() {
        let mut solver = Solver::<(Set, Interval)>::default();
        let a = solver.fresh();
        let b = solver.fresh();
        let c = solver.import(a, ((), 1));
        solver.expect(a, &(Set(1), Interval::new(0, 100)));
        solver.expect(b, &(Set(4), Interval::new(50, 200)));
        solver.equal(a, b);
        solver.solve();
        assert_eq!(*solver.evidence(a), (Set(5), Interval::new(50, 100)));
        assert_eq!(*solver.evidence(c), (Set(5), Interval::new(51, 101)));
    }

    #[test]
    fn replay_keeps_facts_and_exported_flows_only() {
        let mut solver = Solver::<Set>::default();
        let known = solver.known(Set(1));
        let demanded = solver.fresh();
        solver.expect(demanded, &Set(2));
        let conflicted = solver.fresh();
        solver.expect(conflicted, &Set(1));
        solver.expect(conflicted, &Set(2));
        let from_conflict = solver.import(conflicted, ());
        let from_known = solver.import(known, ());
        solver.solve();
        let replay = solver.replay(|set, ()| (set.0.count_ones() == 1).then_some(*set));
        assert_eq!(*replay.evidence(known), Set(1));
        assert_eq!(*replay.evidence(demanded), Set::bottom());
        assert_eq!(*replay.evidence(conflicted), Set::bottom());
        assert_eq!(*replay.evidence(from_conflict), Set::bottom());
        assert_eq!(*replay.evidence(from_known), Set(1));
    }

    /// One constraint over eight pre-made classes: an equality, an
    /// expectation, an equality with a known class, or a flow.
    fn constraint() -> impl proptest::strategy::Strategy<Value = (u8, usize, usize)> {
        (0u8..4, 0usize..8, 0usize..8)
    }

    fn apply(solver: &mut Solver<Set>, vars: &[Var], (kind, a, b): (u8, usize, usize)) {
        match kind {
            0 => solver.equal(vars[a], vars[b]),
            1 => solver.expect(vars[a], &Set(1 << (b % 3))),
            2 => {
                let known = solver.known(Set(1 << (b % 3)));
                solver.equal(vars[a], known);
            }
            _ => solver.flow(vars[a], vars[b], ()),
        }
    }

    proptest::proptest! {
        /// The three lattice laws promise that arrival order is invisible;
        /// this checks the solver keeps that promise, union-by-size choices
        /// and all.
        #[test]
        fn evidence_is_independent_of_arrival_order(
            constraints in proptest::collection::vec(constraint(), 0..64),
            seed in proptest::num::u64::ANY,
        ) {
            let mut ordered = Solver::<Set>::default();
            let vars: Vec<_> = (0..8).map(|_| ordered.fresh()).collect();
            for &c in &constraints {
                apply(&mut ordered, &vars, c);
            }
            ordered.solve();
            let mut permuted = constraints.clone();
            let mut state = seed;
            for i in (1..permuted.len()).rev() {
                state = state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                permuted.swap(i, ((state >> 33) as usize) % (i + 1));
            }
            let mut shuffled = Solver::<Set>::default();
            let shuffled_vars: Vec<_> = (0..8).map(|_| shuffled.fresh()).collect();
            for &c in &permuted {
                apply(&mut shuffled, &shuffled_vars, c);
            }
            shuffled.solve();
            for (&a, &b) in vars.iter().zip(&shuffled_vars) {
                proptest::prop_assert_eq!(ordered.evidence(a), shuffled.evidence(b));
            }
        }

        /// The worklist agrees with a naive fixed point that has no adjacency
        /// structure and rescans every flow until nothing changes.
        #[test]
        fn worklist_matches_full_scan(
            constraints in proptest::collection::vec(constraint(), 0..128),
        ) {
            let mut solver = Solver::<Set>::default();
            let vars: Vec<_> = (0..8).map(|_| solver.fresh()).collect();
            for &c in &constraints {
                apply(&mut solver, &vars, c);
            }
            let mut expected = solver.evidence.clone();
            loop {
                let mut changed = false;
                for &(provider, consumer, ()) in &solver.flows {
                    let evidence = expected[solver.root(provider.index())];
                    changed |= expected[solver.root(consumer.index())].join(&evidence);
                }
                if !changed {
                    break;
                }
            }
            solver.solve();
            for &var in &vars {
                proptest::prop_assert_eq!(*solver.evidence(var), expected[solver.root(var.index())]);
            }
        }
    }
}
