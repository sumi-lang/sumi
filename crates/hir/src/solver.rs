//! A monotone solver over directed flows. Growing value cycles widen and narrow before their
//! evidence reaches downstream dependency components.

use std::collections::VecDeque;

use sumi_graph::NodeId;

use crate::dependency::Rows;

mod schedule;
use schedule::{Growth, Schedule};

/// `join` is commutative, associative, and idempotent with identity `bottom`; `transfer` and
/// `combine` are monotone; ascending chains are finite, or `solve` may not end.
pub(crate) trait Lattice: Clone + Eq {
    /// An edge from one provider.
    type Edge;
    /// An edge from two providers.
    type Pair;
    /// An edge from any number of providers, each crossing it alike.
    type Many;
    type Context;

    /// Whether a flow can widen, so classes settle one strongly connected component at a time,
    /// providers first. A lattice whose chains are short converges as fast on one worklist over
    /// every flow and skips finding the components.
    const WIDENS: bool = true;

    fn bottom() -> Self;

    /// Whether `self` grew.
    fn join(&mut self, other: &Self) -> bool;

    /// What the provider's evidence can do crossing `edge`.
    fn carries(edge: &Self::Edge) -> Carry;

    /// What the first provider's evidence, then the second's, can do crossing `pair`.
    fn carries_pair(pair: &Self::Pair) -> [Carry; 2];

    /// What each provider's evidence can do crossing `many`.
    fn carries_many(many: &Self::Many) -> Carry;

    /// `cyclic`: the flow is on a cycle that can grow, so a lattice with infinite chains widens
    /// here. When the provider is `bottom` the result is `bottom`.
    fn transfer(&self, edge: &Self::Edge, cyclic: bool, cx: &Self::Context) -> Self;

    /// Whether `transfer` over `edge` reads `cyclic`; when it doesn't, a cyclic delivery is exact.
    fn widens(edge: &Self::Edge) -> bool {
        let _ = edge;
        true
    }

    /// Whether `combine` over `pair` reads `cyclic`.
    fn widens_pair(pair: &Self::Pair) -> bool {
        let _ = pair;
        true
    }

    /// `transfer` from two providers, `self` the first; when both are `bottom` the result is
    /// `bottom`.
    fn combine(&self, pair: &Self::Pair, other: &Self, cyclic: bool, cx: &Self::Context) -> Self;

    /// `transfer` from `self` and `others` in order; it reads `cyclic`.
    fn combine_many<'a>(
        &'a self,
        many: &Self::Many,
        others: impl Iterator<Item = &'a Self>,
        cyclic: bool,
        cx: &Self::Context,
    ) -> Self;

    /// `exact`: the class recomputed with no flow cyclic, from what it held before its component
    /// was taken and its inward flows. True if changed.
    fn narrow(&mut self, exact: &Self) -> bool;
}

/// What a provider's evidence can do crossing an edge, least first.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Carry {
    /// Nothing of the provider's, or only something finite, such as a boolean.
    Nothing,
    /// A copy, a narrowing, or a gate: never more than the provider holds.
    Passes,
    Grows,
}

/// A cycle descends one pass at a time, so two counters bounding each other could descend a pass
/// per step; every prefix of a descent is sound.
const NARROWING_PASSES: usize = 8;

struct Flow<L: Lattice> {
    consumer: NodeId,
    first: NodeId,
    shape: Shape<L>,
}

enum Shape<L: Lattice> {
    Edge(L::Edge),
    Pair { second: NodeId, pair: L::Pair },
    Many { others: u32, many: L::Many },
}

struct Flows<'g, L: Lattice> {
    entries: Vec<Flow<L>>,
    others: Vec<&'g [NodeId]>,
}

impl<L: Lattice> Flow<L> {
    #[inline(always)]
    fn providers<'a>(
        &'a self,
        lists: &'a [&[NodeId]],
    ) -> impl Iterator<Item = (Carry, NodeId)> + 'a {
        let (first, second, others, of_others) = match &self.shape {
            Shape::Edge(edge) => (L::carries(edge), None, &[][..], Carry::Nothing),
            Shape::Pair { second, pair } => {
                let [first, of_second] = L::carries_pair(pair);
                (first, Some((of_second, *second)), &[][..], Carry::Nothing)
            }
            Shape::Many { others, many } => {
                let carry = L::carries_many(many);
                (carry, None, lists[*others as usize], carry)
            }
        };
        std::iter::once((first, self.first))
            .chain(second)
            .chain(others.iter().map(move |&other| (of_others, other)))
    }

    fn carry_from(&self, provider: usize) -> Carry {
        match &self.shape {
            Shape::Edge(edge) => L::carries(edge),
            Shape::Pair { second, pair } => {
                let [first, last] = L::carries_pair(pair);
                let first = if self.first.index() == provider {
                    first
                } else {
                    Carry::Nothing
                };
                let last = if second.index() == provider {
                    last
                } else {
                    Carry::Nothing
                };
                first.max(last)
            }
            Shape::Many { many, .. } => L::carries_many(many),
        }
    }

    fn widens(&self) -> bool {
        match &self.shape {
            Shape::Edge(edge) => L::widens(edge),
            Shape::Pair { pair, .. } => L::widens_pair(pair),
            Shape::Many { .. } => true,
        }
    }
}

pub(crate) struct Builder<'g, L: Lattice> {
    initial: Vec<L>,
    flows: Flows<'g, L>,
}

impl<'g, L: Lattice> Builder<'g, L> {
    /// Class `i` is graph node `i`; operand slices belong to that graph.
    pub fn with_classes(n: usize) -> Self {
        Self {
            initial: vec![L::bottom(); n],
            flows: Flows {
                entries: Vec::with_capacity(n),
                others: Vec::new(),
            },
        }
    }

    pub fn expect(&mut self, node: NodeId, evidence: &L) {
        self.initial[node.index()].join(evidence);
    }

    pub fn class_mut(&mut self, node: NodeId) -> &mut L {
        &mut self.initial[node.index()]
    }

    pub fn flow(&mut self, provider: NodeId, consumer: NodeId, edge: L::Edge) {
        self.flows.entries.push(Flow {
            consumer,
            first: provider,
            shape: Shape::Edge(edge),
        });
    }

    pub fn derive(&mut self, first: NodeId, second: NodeId, consumer: NodeId, pair: L::Pair) {
        self.flows.entries.push(Flow {
            consumer,
            first,
            shape: Shape::Pair { second, pair },
        });
    }

    pub fn derive_many(
        &mut self,
        first: NodeId,
        others: &'g [NodeId],
        consumer: NodeId,
        many: L::Many,
    ) {
        let list = u32::try_from(self.flows.others.len()).expect("flow count fits u32");
        self.flows.others.push(others);
        self.flows.entries.push(Flow {
            consumer,
            first,
            shape: Shape::Many { others: list, many },
        });
    }

    fn freeze(self) -> (Solver<'g, L>, Vec<L>) {
        let outgoing = Rows::new(self.initial.len(), || {
            self.flows
                .entries
                .iter()
                .enumerate()
                .flat_map(|(index, flow)| {
                    flow.providers(&self.flows.others)
                        .map(move |(_, provider)| (provider.index(), index as u32))
                })
        });
        let schedule = L::WIDENS.then(|| Schedule::new(&self.flows, &outgoing));
        (
            Solver {
                flows: self.flows,
                outgoing,
                schedule,
            },
            self.initial,
        )
    }

    pub fn solve(self, cx: &L::Context) -> Vec<L> {
        if self.flows.entries.is_empty() {
            return self.initial;
        }
        let (solver, mut evidence) = self.freeze();
        solver.solve(&mut evidence, &mut Workspace::default(), cx);
        evidence
    }
}

struct Solver<'g, L: Lattice> {
    flows: Flows<'g, L>,
    outgoing: Rows,
    schedule: Option<Schedule>,
}

impl<L: Lattice> Solver<'_, L> {
    fn solve(&self, evidence: &mut [L], workspace: &mut Workspace<L>, cx: &L::Context) {
        let mut run = Run {
            flows: &self.flows,
            evidence,
            cx,
        };
        let Some(schedule) = &self.schedule else {
            run.ascend(
                &self.outgoing,
                0..self.outgoing.len() as u32,
                |_| true,
                &[],
                &mut workspace.work,
            );
            return;
        };
        let components = &schedule.components;
        let cyclic = schedule
            .growth
            .as_ref()
            .map_or(&[][..], |growth| &growth.flows);
        for component in (0..components.count()).rev() {
            let members = components.members(component);
            let inside = |node: usize| components.of[node] as usize == component;
            if schedule.cyclic[component] {
                if let Some(growth) = schedule
                    .growth
                    .as_ref()
                    .filter(|growth| members.iter().any(|&member| growth.nodes[member as usize]))
                {
                    workspace.external.clear();
                    workspace.external.extend(
                        members
                            .iter()
                            .map(|&node| run.evidence[node as usize].clone()),
                    );
                    run.ascend(
                        &self.outgoing,
                        members.iter().copied(),
                        inside,
                        cyclic,
                        &mut workspace.work,
                    );
                    run.narrow(growth, members, &workspace.external);
                }
                run.ascend(
                    &self.outgoing,
                    members.iter().copied(),
                    inside,
                    cyclic,
                    &mut workspace.work,
                );
            }
            for &member in members {
                let member = member as usize;
                let outgoing = self.outgoing.get(member);
                if outgoing.is_empty() || run.evidence[member] == L::bottom() {
                    continue;
                }
                for &index in outgoing {
                    let index = index as usize;
                    if !schedule.cyclic[component]
                        || !inside(self.flows.entries[index].consumer.index())
                    {
                        run.deliver(index, false);
                    }
                }
            }
        }
    }
}

struct Run<'a, 'g, L: Lattice> {
    flows: &'a Flows<'g, L>,
    evidence: &'a mut [L],
    cx: &'a L::Context,
}

impl<L: Lattice> Run<'_, '_, L> {
    fn delivery(&self, index: usize, cyclic: bool) -> L {
        let flow = &self.flows.entries[index];
        let first = &self.evidence[flow.first.index()];
        match &flow.shape {
            Shape::Edge(edge) => first.transfer(edge, cyclic, self.cx),
            Shape::Pair { second, pair } => {
                first.combine(pair, &self.evidence[second.index()], cyclic, self.cx)
            }
            Shape::Many { others, many } => {
                let others = self.flows.others[*others as usize]
                    .iter()
                    .map(|other| &self.evidence[other.index()]);
                first.combine_many(many, others, cyclic, self.cx)
            }
        }
    }

    // An exact delivery already held by the consumer must not widen a merely passing value.
    fn deliver(&mut self, index: usize, cyclic: bool) -> bool {
        let flow = &self.flows.entries[index];
        let consumer = flow.consumer.index();
        let exact = self.delivery(index, false);
        if !cyclic || !flow.widens() {
            return self.evidence[consumer].join(&exact);
        }
        let mut probe = self.evidence[consumer].clone();
        if !probe.join(&exact) {
            return false;
        }
        let rounded = self.delivery(index, true);
        self.evidence[consumer].join(&rounded)
    }

    fn ascend(
        &mut self,
        outgoing: &Rows,
        members: impl IntoIterator<Item = u32>,
        accepts: impl Fn(usize) -> bool,
        cyclic: &[bool],
        work: &mut Worklist,
    ) {
        work.queued.resize(self.evidence.len(), false);
        let bottom = L::bottom();
        for member in members {
            let member = member as usize;
            if !outgoing.get(member).is_empty() && self.evidence[member] != bottom {
                work.push(member);
            }
        }
        while let Some(provider) = work.pop() {
            for &index in outgoing.get(provider) {
                let index = index as usize;
                let consumer = self.flows.entries[index].consumer.index();
                if accepts(consumer)
                    && self.deliver(index, cyclic.get(index).copied().unwrap_or(false))
                {
                    work.push(consumer);
                }
            }
        }
    }

    fn narrow(&mut self, growth: &Growth, members: &[u32], external: &[L]) {
        for _ in 0..NARROWING_PASSES {
            let mut changed = false;
            for (&member, outside) in members.iter().zip(external) {
                let member = member as usize;
                if !growth.nodes[member] {
                    continue;
                }
                let mut exact = outside.clone();
                for &index in growth.incoming.get(member) {
                    exact.join(&self.delivery(index as usize, false));
                }
                changed |= self.evidence[member].narrow(&exact);
            }
            if !changed {
                break;
            }
        }
        // Copy cycles retain stale evidence under descent; restarting them makes ascent exact.
        for (&member, outside) in members.iter().zip(external) {
            let member = member as usize;
            if !growth.nodes[member] {
                self.evidence[member] = outside.clone();
            }
        }
    }
}

struct Workspace<L> {
    work: Worklist,
    external: Vec<L>,
}

impl<L> Default for Workspace<L> {
    fn default() -> Self {
        Self {
            work: Worklist::default(),
            external: Vec::new(),
        }
    }
}

#[derive(Default)]
struct Worklist {
    queued: Vec<bool>,
    pending: VecDeque<usize>,
}

impl Worklist {
    fn push(&mut self, node: usize) {
        if !self.queued[node] {
            self.queued[node] = true;
            self.pending.push_back(node);
        }
    }

    fn pop(&mut self) -> Option<usize> {
        let node = self.pending.pop_front()?;
        self.queued[node] = false;
        Some(node)
    }
}

#[cfg(test)]
mod tests {
    use std::convert::Infallible;

    use super::*;

    #[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
    struct Set<const WIDENS: bool = true>(u8);

    impl<const WIDENS: bool> Lattice for Set<WIDENS> {
        type Edge = ();
        type Pair = ();
        type Context = ();
        type Many = ();

        const WIDENS: bool = WIDENS;

        fn bottom() -> Self {
            Self(0)
        }

        fn join(&mut self, other: &Self) -> bool {
            let before = self.0;
            self.0 |= other.0;
            before != self.0
        }

        fn carries((): &()) -> Carry {
            Carry::Passes
        }

        fn carries_many((): &()) -> Carry {
            Carry::Passes
        }

        fn combine_many<'a>(
            &'a self,
            (): &(),
            others: impl Iterator<Item = &'a Self>,
            _: bool,
            (): &(),
        ) -> Self {
            Self(others.fold(self.0, |bits, other| bits | other.0))
        }

        fn carries_pair((): &()) -> [Carry; 2] {
            [Carry::Passes; 2]
        }

        fn transfer(&self, (): &(), _: bool, (): &()) -> Self {
            *self
        }

        fn combine(&self, (): &(), other: &Self, _: bool, (): &()) -> Self {
            Self(self.0 | other.0)
        }

        fn narrow(&mut self, _: &Self) -> bool {
            false
        }
    }

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
        type Pair = Infallible;
        type Context = ();
        type Many = std::convert::Infallible;

        fn bottom() -> Self {
            Self::new(i64::MIN, i64::MAX)
        }

        fn join(&mut self, other: &Self) -> bool {
            let before = *self;
            self.lo = self.lo.max(other.lo);
            self.hi = self.hi.min(other.hi);
            before != *self
        }

        fn carries(offset: &i64) -> Carry {
            if *offset == 0 {
                Carry::Passes
            } else {
                Carry::Grows
            }
        }

        fn carries_many(many: &Self::Many) -> Carry {
            match *many {}
        }

        fn combine_many<'a>(
            &'a self,
            many: &Self::Many,
            _: impl Iterator<Item = &'a Self>,
            _: bool,
            _: &Self::Context,
        ) -> Self {
            match *many {}
        }

        fn carries_pair(never: &Infallible) -> [Carry; 2] {
            match *never {}
        }

        fn transfer(&self, offset: &i64, _: bool, (): &()) -> Self {
            if *self == Self::bottom() {
                return *self;
            }
            Self::new(
                self.lo.saturating_add(*offset),
                self.hi.saturating_add(*offset),
            )
        }

        fn combine(&self, never: &Infallible, _: &Self, _: bool, (): &()) -> Self {
            match *never {}
        }

        fn narrow(&mut self, _: &Self) -> bool {
            false
        }
    }

    fn classes<'g, L: Lattice, const N: usize>() -> (Builder<'g, L>, [NodeId; N]) {
        (Builder::with_classes(N), std::array::from_fn(NodeId::new))
    }

    #[test]
    fn a_flow_is_five_words() {
        assert!(size_of::<crate::lattice::Pair>() <= 4);
        assert_eq!(size_of::<Flow<crate::lattice::Evidence>>(), 20);
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    struct Seen {
        set: u8,
        cyclic: bool,
    }

    impl Lattice for Seen {
        type Edge = ();
        type Pair = Infallible;
        type Context = ();
        type Many = std::convert::Infallible;

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

        fn carries((): &()) -> Carry {
            Carry::Grows
        }

        fn carries_many(many: &Self::Many) -> Carry {
            match *many {}
        }

        fn combine_many<'a>(
            &'a self,
            many: &Self::Many,
            _: impl Iterator<Item = &'a Self>,
            _: bool,
            _: &Self::Context,
        ) -> Self {
            match *many {}
        }

        fn carries_pair(never: &Infallible) -> [Carry; 2] {
            match *never {}
        }

        fn transfer(&self, (): &(), cyclic: bool, (): &()) -> Self {
            Self {
                set: self.set,
                cyclic: self.cyclic | (cyclic && self.set != 0),
            }
        }

        fn combine(&self, never: &Infallible, _: &Self, _: bool, (): &()) -> Self {
            match *never {}
        }

        fn narrow(&mut self, _: &Self) -> bool {
            false
        }
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    struct Hull {
        lo: i64,
        hi: i64,
    }

    #[derive(Clone, Copy)]
    enum HullEdge {
        Add(i64),
        Cap(i64),
        Inert,
    }

    impl Lattice for Hull {
        type Edge = HullEdge;
        type Pair = ();
        type Context = ();
        type Many = ();

        fn bottom() -> Self {
            Self {
                lo: i64::MAX,
                hi: i64::MIN,
            }
        }

        fn join(&mut self, other: &Self) -> bool {
            let before = *self;
            self.lo = self.lo.min(other.lo);
            self.hi = self.hi.max(other.hi);
            before != *self
        }

        fn carries(edge: &HullEdge) -> Carry {
            match edge {
                HullEdge::Inert => Carry::Nothing,
                HullEdge::Add(k) if *k != 0 => Carry::Grows,
                _ => Carry::Passes,
            }
        }

        fn carries_many((): &()) -> Carry {
            Carry::Passes
        }

        fn combine_many<'a>(
            &'a self,
            (): &(),
            others: impl Iterator<Item = &'a Self>,
            cyclic: bool,
            (): &(),
        ) -> Self {
            let mut result = *self;
            for other in others {
                result.join(other);
            }
            if cyclic && result.lo <= result.hi {
                result.hi = i64::MAX;
            }
            result
        }

        fn carries_pair((): &()) -> [Carry; 2] {
            [Carry::Passes; 2]
        }

        fn combine(&self, (): &(), other: &Self, cyclic: bool, (): &()) -> Self {
            self.combine_many(&(), std::iter::once(other), cyclic, &())
        }

        fn transfer(&self, edge: &HullEdge, cyclic: bool, (): &()) -> Self {
            if self.lo > self.hi {
                return *self;
            }
            let mut out = match *edge {
                HullEdge::Add(k) => Self {
                    lo: self.lo.saturating_add(k),
                    hi: self.hi.saturating_add(k),
                },
                HullEdge::Cap(c) => Self {
                    lo: self.lo,
                    hi: self.hi.min(c),
                },
                HullEdge::Inert => return Self::bottom(),
            };
            if cyclic {
                out.hi = i64::MAX;
            }
            out
        }

        fn narrow(&mut self, exact: &Self) -> bool {
            if self == exact {
                return false;
            }
            *self = *exact;
            true
        }
    }

    #[test]
    fn narrowing_takes_back_what_widening_overshot() {
        for reversed in [false, true] {
            let (mut solver, [x, capped, stepped, downstream]) = classes::<Hull, 4>();
            solver.expect(x, &Hull { lo: 0, hi: 0 });
            let mut flows = vec![
                (x, capped, HullEdge::Cap(100)),
                (capped, stepped, HullEdge::Add(7)),
                (stepped, x, HullEdge::Add(0)),
                (x, downstream, HullEdge::Add(1)),
            ];
            if reversed {
                flows.reverse();
            }
            for (provider, consumer, edge) in flows {
                solver.flow(provider, consumer, edge);
            }
            let solver = solver.solve(&());
            assert_eq!(solver[x.index()], Hull { lo: 0, hi: 107 });
            assert_eq!(solver[capped.index()], Hull { lo: 0, hi: 100 });
            assert_eq!(solver[stepped.index()], Hull { lo: 7, hi: 107 });
            assert_eq!(solver[downstream.index()], Hull { lo: 1, hi: 108 });
        }
    }

    #[test]
    fn narrowing_keeps_an_unbounded_chain_unbounded() {
        let (mut solver, [x, stepped]) = classes::<Hull, 2>();
        solver.expect(x, &Hull { lo: 0, hi: 0 });
        solver.flow(x, stepped, HullEdge::Add(1));
        solver.flow(stepped, x, HullEdge::Add(0));
        let solver = solver.solve(&());
        assert_eq!(
            solver[x.index()],
            Hull {
                lo: 0,
                hi: i64::MAX
            }
        );
    }

    #[test]
    fn frozen_topology_and_workspace_accept_independent_seeds() {
        let [x, capped, stepped, copied, downstream] = std::array::from_fn(NodeId::new);
        let operands = [capped, stepped, stepped];
        let build = || {
            let mut builder = Builder::<Hull>::with_classes(5);
            builder.derive_many(x, &operands, x, ());
            builder.flow(x, capped, HullEdge::Cap(100));
            builder.flow(capped, stepped, HullEdge::Add(7));
            builder.flow(x, copied, HullEdge::Add(0));
            builder.flow(copied, copied, HullEdge::Add(0));
            builder.flow(copied, x, HullEdge::Inert);
            builder.flow(copied, downstream, HullEdge::Add(1));
            builder
        };
        let (solver, mut evidence) = build().freeze();
        let mut workspace = Workspace::default();
        for seed in [0, 30, -10, 200] {
            evidence.fill(Hull::bottom());
            let initial = Hull { lo: seed, hi: seed };
            evidence[x.index()] = initial;
            solver.solve(&mut evidence, &mut workspace, &());
            let mut fresh = build();
            fresh.expect(x, &initial);
            assert_eq!(evidence, fresh.solve(&()));
        }
        evidence.fill(Hull::bottom());
        solver.solve(&mut evidence, &mut workspace, &());
        assert!(evidence.iter().all(|value| *value == Hull::bottom()));
    }

    #[test]
    fn narrowing_reads_multi_provider_flows_with_external_first_providers() {
        for many in [false, true] {
            let (mut solver, [seed, x, capped, stepped, downstream]) = classes::<Hull, 5>();
            solver.expect(seed, &Hull { lo: 0, hi: 0 });
            let others = [capped, stepped, stepped];
            if many {
                solver.derive_many(seed, &others, x, ());
            } else {
                solver.derive(seed, stepped, x, ());
            }
            solver.flow(x, capped, HullEdge::Cap(100));
            solver.flow(capped, stepped, HullEdge::Add(7));
            solver.flow(x, downstream, HullEdge::Add(1));
            let solver = solver.solve(&());
            assert_eq!(solver[x.index()], Hull { lo: 0, hi: 107 });
            assert_eq!(solver[capped.index()], Hull { lo: 0, hi: 100 });
            assert_eq!(solver[stepped.index()], Hull { lo: 7, hi: 107 });
            assert_eq!(solver[downstream.index()], Hull { lo: 1, hi: 108 });
        }
    }

    #[test]
    fn self_dependencies_widen_only_when_they_grow() {
        let (mut solver, [growing, copied]) = classes::<Hull, 2>();
        for node in [growing, copied] {
            solver.expect(node, &Hull { lo: 0, hi: 0 });
        }
        solver.flow(growing, growing, HullEdge::Add(1));
        solver.flow(copied, copied, HullEdge::Add(0));
        let solver = solver.solve(&());
        assert_eq!(
            solver[growing.index()],
            Hull {
                lo: 0,
                hi: i64::MAX
            }
        );
        assert_eq!(solver[copied.index()], Hull { lo: 0, hi: 0 });
    }

    #[test]
    fn inert_arcs_close_no_cycle_of_values() {
        let (mut solver, [seed, passed, x, capped, stepped, first, second]) = classes::<Hull, 7>();
        solver.expect(seed, &Hull { lo: 4, hi: 9 });
        solver.flow(seed, passed, HullEdge::Add(0));
        solver.flow(passed, seed, HullEdge::Inert);
        solver.expect(x, &Hull { lo: 0, hi: 0 });
        solver.flow(x, capped, HullEdge::Cap(100));
        solver.flow(capped, stepped, HullEdge::Add(7));
        solver.flow(stepped, x, HullEdge::Add(0));
        solver.flow(x, first, HullEdge::Add(0));
        solver.flow(first, second, HullEdge::Add(0));
        solver.flow(second, first, HullEdge::Add(0));
        solver.flow(second, x, HullEdge::Inert);
        let solver = solver.solve(&());
        assert_eq!(solver[passed.index()], Hull { lo: 4, hi: 9 });
        assert_eq!(solver[x.index()], Hull { lo: 0, hi: 107 });
        assert_eq!(solver[first.index()], Hull { lo: 0, hi: 107 });
        assert_eq!(solver[second.index()], Hull { lo: 0, hi: 107 });
    }

    #[test]
    fn flows_on_a_cycle_are_told_so() {
        let (mut solver, [a, b, c, d]) = classes::<Seen, 4>();
        solver.expect(
            a,
            &Seen {
                set: 1,
                cyclic: false,
            },
        );
        solver.flow(a, b, ());
        solver.flow(b, c, ());
        solver.flow(c, b, ());
        solver.flow(c, d, ());
        let solver = solver.solve(&());
        assert!(!solver[a.index()].cyclic);
        assert!(solver[b.index()].cyclic && solver[c.index()].cyclic);
        assert_eq!(solver[d.index()].set, 1);
    }

    #[test]
    fn expectations_join_and_flows_deliver() {
        let (mut solver, [a, b]) = classes::<Set, 2>();
        solver.flow(a, b, ());
        solver.expect(a, &Set(1));
        solver.expect(a, &Set(2));
        let solver = solver.solve(&());
        assert_eq!(solver[a.index()], Set(3));
        assert_eq!(solver[b.index()], Set(3));
    }

    #[test]
    fn flows_never_carry_evidence_back() {
        let (mut solver, [provider, consumer]) = classes::<Set, 2>();
        solver.flow(provider, consumer, ());
        solver.expect(consumer, &Set(1));
        let solver = solver.solve(&());
        assert_eq!(solver[provider.index()], Set::bottom());
        assert_eq!(solver[consumer.index()], Set(1));
    }

    #[test]
    fn intervals_narrow_transfer_and_empty_out() {
        let (mut solver, [x, y]) = classes::<Interval, 2>();
        solver.expect(x, &Interval::new(0, 10));
        solver.flow(x, y, 100);
        solver.expect(x, &Interval::new(5, 20));
        solver.expect(y, &Interval::new(130, 140));
        let solver = solver.solve(&());
        assert_eq!(solver[x.index()], Interval::new(5, 10));
        assert!(solver[y.index()].is_empty());
    }

    fn constraint() -> impl proptest::strategy::Strategy<Value = (u8, usize, usize)> {
        (0u8..4, 0usize..8, 0usize..8)
    }

    fn apply<'g, const W: bool>(
        solver: &mut Builder<'g, Set<W>>,
        vars: &'g [NodeId],
        (kind, a, b): (u8, usize, usize),
    ) {
        match kind {
            0 => solver.expect(vars[a], &Set(1 << (b % 3))),
            1 => solver.flow(vars[a], vars[b], ()),
            2 => solver.derive(vars[a], vars[b], vars[(b + 1) % 8], ()),
            _ => solver.derive_many(vars[a], &vars[a.min(b)..=a.max(b)], vars[(b + 1) % 8], ()),
        }
    }

    proptest::proptest! {
        #[test]
        fn evidence_is_independent_of_arrival_order(
            constraints in proptest::collection::vec(constraint(), 0..64),
            seed in proptest::num::u64::ANY,
        ) {
            let (mut ordered, vars) = classes::<Set, 8>();
            for &c in &constraints {
                apply(&mut ordered, &vars, c);
            }
            let ordered = ordered.solve(&());
            let mut permuted = constraints.clone();
            let mut state = seed;
            for i in (1..permuted.len()).rev() {
                state = state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                permuted.swap(i, ((state >> 33) as usize) % (i + 1));
            }
            let (mut shuffled, shuffled_vars) = classes::<Set, 8>();
            for &c in &permuted {
                apply(&mut shuffled, &shuffled_vars, c);
            }
            let shuffled = shuffled.solve(&());
            for (&a, &b) in vars.iter().zip(&shuffled_vars) {
                proptest::prop_assert_eq!(&ordered[a.index()], &shuffled[b.index()]);
            }
        }

        #[test]
        fn worklist_matches_full_scan(
            constraints in proptest::collection::vec(constraint(), 0..128),
        ) {
            let (mut solver, vars) = classes::<Set, 8>();
            for &c in &constraints {
                apply(&mut solver, &vars, c);
            }
            let mut expected = solver.initial.clone();
            loop {
                let mut changed = false;
                for flow in &solver.flows.entries {
                    let first = expected[flow.first.index()];
                    let evidence = match flow.shape {
                        Shape::Edge(()) => first.transfer(&(), false, &()),
                        Shape::Pair { second, pair: () } => {
                            first.combine(&(), &expected[second.index()], false, &())
                        }
                        Shape::Many { others, many: () } => {
                            let others = solver.flows.others[others as usize].iter()
                                .map(|node| &expected[node.index()]);
                            first.combine_many(&(), others, false, &())
                        },
                    };
                    changed |= expected[flow.consumer.index()].join(&evidence);
                }
                if !changed {
                    break;
                }
            }
            let (mut finite, finite_vars) = classes::<Set<false>, 8>();
            for &constraint in &constraints {
                apply(&mut finite, &finite_vars, constraint);
            }
            let finite = finite.solve(&());
            let solver = solver.solve(&());
            for &var in &vars {
                proptest::prop_assert_eq!(solver[var.index()], expected[var.index()]);
                proptest::prop_assert_eq!(finite[var.index()].0, expected[var.index()].0);
            }
        }
    }
}
