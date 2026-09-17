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
//! consumer's side. [`derive`](Solver::derive) is a flow with two providers,
//! for evidence that is a function of two classes, an operator's result of
//! its operands. Equalities and evidence are applied as they arrive; flows
//! are settled by [`solve`](Solver::solve), a worklist over the flow graph.
//!
//! A transfer may consult a context the instance supplies to `solve`: what
//! is true of the whole program and fixed before any flow settles, such as
//! the constants an interval analysis rounds to. It is also told whether
//! its flow closes a cycle of the flow graph, which is where a lattice
//! without finite ascending chains of its own must widen: the solver finds
//! the cycles, and the lattice decides what to do on them.
//!
//! A conflict is a lattice element like any other. The solver never retracts
//! evidence or stops at the first disagreement, so when an instance reads a
//! class it sees every claim made about it, and the classes around a
//! conflicted one are untouched.

use std::collections::VecDeque;
use std::num::{NonZeroU32, NonZeroUsize};

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
    /// What every transfer may consult, fixed for the whole solve.
    type Context;

    /// No evidence: the identity of `join`.
    fn bottom() -> Self;

    /// Join `other` into `self`, reporting whether `self` grew.
    fn join(&mut self, other: &Self) -> bool;

    /// The evidence a consumer receives when `self`, and for a two-provider
    /// edge `other`, cross `edge`. `cyclic` says the flow lies on a cycle of
    /// the flow graph, so the evidence delivered here may come back.
    ///
    /// Nothing comes of nothing: when every provider holds `bottom`, so
    /// does the result. The solver counts on it and never visits a class
    /// with no evidence.
    fn transfer(
        &self,
        edge: &Self::Edge,
        other: Option<&Self>,
        cyclic: bool,
        cx: &Self::Context,
    ) -> Self;
}

/// Two lattices side by side: evidence of both kinds on one class, joined
/// componentwise and transferred by a pair of edges. Tuples nest, so any
/// number of analyses share one solver.
impl<A: Lattice, B: Lattice> Lattice for (A, B) {
    type Edge = (A::Edge, B::Edge);
    type Context = (A::Context, B::Context);

    fn bottom() -> Self {
        (A::bottom(), B::bottom())
    }

    fn join(&mut self, other: &Self) -> bool {
        let a = self.0.join(&other.0);
        let b = self.1.join(&other.1);
        a | b
    }

    fn transfer(
        &self,
        edge: &Self::Edge,
        other: Option<&Self>,
        cyclic: bool,
        cx: &Self::Context,
    ) -> Self {
        (
            self.0
                .transfer(&edge.0, other.map(|other| &other.0), cyclic, &cx.0),
            self.1
                .transfer(&edge.1, other.map(|other| &other.1), cyclic, &cx.1),
        )
    }
}

/// A member of some class: what the solver hands out and takes back. One
/// past its index, so an `Option<Var>` is one word.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Var(NonZeroU32);

impl Var {
    fn new(index: usize) -> Self {
        let past = u32::try_from(index + 1).expect("class count fits u32");
        Self(NonZeroU32::new(past).expect("one past an index"))
    }

    fn index(self) -> usize {
        self.0.get() as usize - 1
    }
}

/// The flows into each class, in compressed sparse rows by class, and the
/// fact that opened each class, one past its index or zero: what a walk
/// back from a class to what fed it reads, built by [`Solver::backwards`].
pub struct Backwards {
    start: Vec<u32>,
    flows: Vec<u32>,
    facts: Vec<u32>,
}

/// One flow: what `consumer` learns from `first`, and from `second` when
/// the edge has two providers, through `edge`.
struct Flow<E> {
    first: Var,
    second: Option<Var>,
    consumer: Var,
    edge: E,
}

pub struct Solver<L: Lattice> {
    parent: Vec<u32>,
    size: Vec<u32>,
    /// Meaningful at roots only.
    evidence: Vec<L>,
    facts: Vec<(Var, L)>,
    /// Settled by `solve`.
    flows: Vec<Flow<L::Edge>>,
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
        let var = Var::new(self.parent.len());
        let id = u32::try_from(self.parent.len()).expect("class count fits u32");
        self.parent.push(id);
        self.size.push(1);
        self.evidence.push(evidence);
        var
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
        self.flows.push(Flow {
            first: provider,
            second: None,
            consumer,
            edge,
        });
    }

    /// Let `consumer`'s class learn the transfer of `first`'s and
    /// `second`'s evidence through `edge`, recomputed whenever either grows.
    pub fn derive(&mut self, first: Var, second: Var, consumer: Var, edge: L::Edge) {
        self.flows.push(Flow {
            first,
            second: Some(second),
            consumer,
            edge,
        });
    }

    /// The class `var` is a member of, as its representative.
    pub fn find(&self, var: Var) -> Var {
        Var::new(self.root(var.index()))
    }

    /// The flow graph read backwards, once every equality and flow is in.
    pub fn backwards(&self) -> Backwards {
        let n = self.parent.len();
        // The rows are counted one slot to the right and filled with the
        // cursor one slot to the right, so no second copy of the row
        // starts is needed.
        let mut start = vec![0u32; n + 2];
        for flow in &self.flows {
            start[self.root(flow.consumer.index()) + 2] += 1;
        }
        for i in 0..=n {
            start[i + 1] += start[i];
        }
        let mut flows = vec![0u32; self.flows.len()];
        for (index, flow) in self.flows.iter().enumerate() {
            let slot = &mut start[self.root(flow.consumer.index()) + 1];
            flows[*slot as usize] = index as u32;
            *slot += 1;
        }
        let mut facts = vec![0u32; n];
        for (index, (fact, _)) in self.facts.iter().enumerate().rev() {
            facts[self.root(fact.index())] = index as u32 + 1;
        }
        Backwards {
            start,
            flows,
            facts,
        }
    }

    /// The evidence a fact opened `var`'s class with, if one did: the first
    /// fact of the class, when equalities merged several.
    pub fn fact(&self, backwards: &Backwards, var: Var) -> Option<&L> {
        let index = backwards.facts[self.root(var.index())].checked_sub(1)?;
        Some(&self.facts[index as usize].1)
    }

    /// Every flow into `var`'s class: its providers and its edge.
    pub fn incoming<'a>(
        &'a self,
        backwards: &'a Backwards,
        var: Var,
    ) -> impl Iterator<Item = (Var, Option<Var>, &'a L::Edge)> + 'a {
        let root = self.root(var.index());
        backwards.flows[backwards.start[root] as usize..backwards.start[root + 1] as usize]
            .iter()
            .map(|&index| {
                let flow = &self.flows[index as usize];
                (flow.first, flow.second, &flow.edge)
            })
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
    pub fn solve(&mut self, cx: &L::Context) {
        let n = self.parent.len();
        for id in 0..n {
            self.compress(id);
        }
        if self.flows.is_empty() {
            return;
        }
        // Adjacency by provider root as one-based links, so `None` is compact.
        // Prepending in reverse keeps each provider's consumers in order. A
        // two-provider flow is listed under both, since either can grow.
        let mut outgoing = vec![None; n];
        let mut edges = Vec::with_capacity(self.flows.len());
        let mut arcs = Vec::with_capacity(edges.capacity());
        for (index, flow) in self.flows.iter().enumerate().rev() {
            for provider in std::iter::once(flow.first).chain(flow.second) {
                let provider = self.root(provider.index());
                edges.push((index, outgoing[provider]));
                outgoing[provider] = NonZeroUsize::new(edges.len());
                arcs.push((provider, self.root(flow.consumer.index())));
            }
        }
        // A flow closes a cycle when a provider and the consumer share a
        // strongly connected component of the flow graph.
        let component = components(n, &arcs);
        let cyclic: Vec<bool> = self
            .flows
            .iter()
            .map(|flow| {
                let consumer = component[self.root(flow.consumer.index())];
                std::iter::once(flow.first)
                    .chain(flow.second)
                    .any(|provider| component[self.root(provider.index())] == consumer)
            })
            .collect();
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
            let mut edge = outgoing[provider];
            while let Some(index) = edge {
                let (index, next) = edges[index.get() - 1];
                edge = next;
                let flow = &self.flows[index];
                let consumer = self.root(flow.consumer.index());
                let delivered = {
                    let first = &self.evidence[self.root(flow.first.index())];
                    let second = flow
                        .second
                        .map(|second| &self.evidence[self.root(second.index())]);
                    first.transfer(&flow.edge, second, cyclic[index], cx)
                };
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
    /// than provisional. `export` sees the provider's settled evidence, the
    /// second provider's for a two-provider flow, and the edge.
    pub fn replay(&self, export: impl Fn(&L, Option<&L>, &L::Edge) -> Option<L>) -> Self {
        let mut replay = Self::with_classes(self.parent.len());
        for (var, evidence) in &self.facts {
            replay.expect(*var, evidence);
        }
        for flow in &self.flows {
            let second = flow.second.map(|second| self.evidence(second));
            if let Some(evidence) = export(self.evidence(flow.first), second, &flow.edge) {
                replay.expect(flow.consumer, &evidence);
            }
        }
        replay
    }
}

/// The strongly connected component of each of `n` nodes under `arcs`.
/// Components are numbered in reverse topological order: a component
/// completes before any that reaches it. Pearce's one-array variant of
/// Tarjan's algorithm, on an explicit stack: a node's slot holds its visit
/// index while it is open, then the number of its component.
pub(crate) fn components(n: usize, arcs: &[(usize, usize)]) -> Vec<u32> {
    // Adjacency in compressed sparse rows: a few allocations however many
    // nodes, since a solve calls this once over every class. The rows are
    // counted one slot to the right and filled with the cursor one slot to
    // the right, so no second copy of the row starts is needed.
    let mut start = vec![0; n + 2];
    for &(from, _) in arcs {
        start[from + 2] += 1;
    }
    for i in 0..=n {
        start[i + 1] += start[i];
    }
    let mut targets = vec![0; arcs.len()];
    for &(from, to) in arcs {
        targets[start[from + 1]] = to;
        start[from + 1] += 1;
    }
    let adjacent = |node: usize| &targets[start[node]..start[node + 1]];
    // Visit indices count up from one; component numbers count down from
    // `n - 1`, and since every completed node gives an index back, a
    // component number is always above every open index.
    let mut slot = vec![0u32; n];
    let mut index = 1u32;
    let mut component = u32::try_from(n)
        .expect("class count fits u32")
        .wrapping_sub(1);
    let mut open = Vec::new();
    let mut work: Vec<(usize, usize, bool)> = Vec::new();
    for root in 0..n {
        if slot[root] != 0 {
            continue;
        }
        slot[root] = index;
        index += 1;
        work.push((root, 0, true));
        while let Some(&mut (node, ref mut position, ref mut is_root)) = work.last_mut() {
            if let Some(&next) = adjacent(node).get(*position) {
                *position += 1;
                if slot[next] == 0 {
                    slot[next] = index;
                    index += 1;
                    work.push((next, 0, true));
                } else if slot[next] < slot[node] {
                    slot[node] = slot[next];
                    *is_root = false;
                }
                continue;
            }
            let (node, _, is_root) = work.pop().expect("the frame just read");
            if is_root {
                index -= 1;
                while let Some(&member) = open.last()
                    && slot[node] <= slot[member]
                {
                    open.pop();
                    slot[member] = component;
                    index -= 1;
                }
                slot[node] = component;
                component = component.wrapping_sub(1);
            } else {
                open.push(node);
            }
            if let Some(&mut (parent, _, ref mut parent_is_root)) = work.last_mut()
                && slot[node] < slot[parent]
            {
                slot[parent] = slot[node];
                *parent_is_root = false;
            }
        }
    }
    // Numbered from zero in completion order.
    let last = u32::try_from(n)
        .expect("class count fits u32")
        .wrapping_sub(1);
    for slot in &mut slot {
        *slot = last - *slot;
    }
    slot
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
        type Context = ();

        fn bottom() -> Self {
            Self(0)
        }

        fn join(&mut self, other: &Self) -> bool {
            let before = self.0;
            self.0 |= other.0;
            before != self.0
        }

        /// A flow delivers the set; a derive delivers the union of both.
        fn transfer(&self, (): &(), other: Option<&Self>, _: bool, (): &()) -> Self {
            Self(self.0 | other.map_or(0, |other| other.0))
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
        type Context = ();

        fn bottom() -> Self {
            Self::new(i64::MIN, i64::MAX)
        }

        fn join(&mut self, other: &Self) -> bool {
            let before = *self;
            self.lo = self.lo.max(other.lo);
            self.hi = self.hi.min(other.hi);
            before != *self
        }

        fn transfer(&self, offset: &i64, _: Option<&Self>, _: bool, (): &()) -> Self {
            Self::new(
                self.lo.saturating_add(*offset),
                self.hi.saturating_add(*offset),
            )
        }
    }

    #[test]
    fn a_flow_is_seven_words() {
        assert_eq!(size_of::<Option<Var>>(), 4);
        assert_eq!(
            size_of::<Flow<(crate::typing::Edge, crate::ranges::RangeEdge)>>(),
            28
        );
    }

    #[test]
    fn components_follow_the_arcs() {
        // 0 -> 1 -> 2 -> 0 is a cycle; 3 hangs off it; 4 is alone.
        let component = components(5, &[(0, 1), (1, 2), (2, 0), (1, 3), (4, 4)]);
        assert_eq!(component[0], component[1]);
        assert_eq!(component[1], component[2]);
        assert_ne!(component[0], component[3]);
        assert_ne!(component[0], component[4]);
        // The callee completes first.
        assert!(component[3] < component[0]);
    }

    /// A lattice that reports which flows the solver called cyclic.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    struct Seen {
        set: u8,
        cyclic: bool,
    }

    impl Lattice for Seen {
        type Edge = ();
        type Context = ();

        fn bottom() -> Self {
            Self {
                set: 0,
                cyclic: false,
            }
        }

        fn join(&mut self, other: &Self) -> bool {
            let before = *self;
            self.set |= other.set;
            self.cyclic |= other.cyclic;
            before != *self
        }

        /// Nothing comes of nothing: an empty set is not marked.
        fn transfer(&self, (): &(), _: Option<&Self>, cyclic: bool, (): &()) -> Self {
            Self {
                set: self.set,
                cyclic: self.cyclic | (cyclic && self.set != 0),
            }
        }
    }

    #[test]
    fn flows_on_a_cycle_are_told_so() {
        let mut solver = Solver::<Seen>::default();
        let a = solver.known(Seen {
            set: 1,
            cyclic: false,
        });
        let b = solver.import(a, ());
        let c = solver.import(b, ());
        solver.flow(c, b, ());
        let d = solver.import(c, ());
        solver.solve(&());
        assert!(!solver.evidence(a).cyclic);
        assert!(solver.evidence(b).cyclic && solver.evidence(c).cyclic);
        // `d` is downstream of the cycle: its own flow is not on it, but the
        // evidence it receives was marked on the way.
        assert_eq!(solver.evidence(d).set, 1);
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
        solver.solve(&());
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
        solver.solve(&());
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
        solver.solve(&());
        assert_eq!(*solver.evidence(x), Interval::new(5, 10));
        assert!(solver.evidence(y).is_empty());
        let replay = solver.replay(|band, _, offset| {
            (!band.is_empty()).then(|| band.transfer(offset, None, false, &()))
        });
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
        solver.solve(&((), ()));
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
        solver.solve(&());
        let replay = solver.replay(|set, _, ()| (set.0.count_ones() == 1).then_some(*set));
        assert_eq!(*replay.evidence(known), Set(1));
        assert_eq!(*replay.evidence(demanded), Set::bottom());
        assert_eq!(*replay.evidence(conflicted), Set::bottom());
        assert_eq!(*replay.evidence(from_conflict), Set::bottom());
        assert_eq!(*replay.evidence(from_known), Set(1));
    }

    /// One constraint over eight pre-made classes: an equality, an
    /// expectation, an equality with a known class, a flow, or a derive
    /// into the class after the second.
    fn constraint() -> impl proptest::strategy::Strategy<Value = (u8, usize, usize)> {
        (0u8..5, 0usize..8, 0usize..8)
    }

    fn apply(solver: &mut Solver<Set>, vars: &[Var], (kind, a, b): (u8, usize, usize)) {
        match kind {
            0 => solver.equal(vars[a], vars[b]),
            1 => solver.expect(vars[a], &Set(1 << (b % 3))),
            2 => {
                let known = solver.known(Set(1 << (b % 3)));
                solver.equal(vars[a], known);
            }
            3 => solver.flow(vars[a], vars[b], ()),
            _ => solver.derive(vars[a], vars[b], vars[(b + 1) % 8], ()),
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
            ordered.solve(&());
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
            shuffled.solve(&());
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
                for flow in &solver.flows {
                    let first = expected[solver.root(flow.first.index())];
                    let second = flow.second.map(|second| expected[solver.root(second.index())]);
                    let evidence = first.transfer(&(), second.as_ref(), false, &());
                    changed |= expected[solver.root(flow.consumer.index())].join(&evidence);
                }
                if !changed {
                    break;
                }
            }
            solver.solve(&());
            for &var in &vars {
                proptest::prop_assert_eq!(*solver.evidence(var), expected[solver.root(var.index())]);
            }
        }
    }
}
