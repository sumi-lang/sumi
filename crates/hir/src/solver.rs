//! A monotone framework: a join-semilattice payload per class and directed flows with a transfer
//! per edge, settled one strongly connected component at a time, providers first. Evidence never
//! flows back and is never retracted; a conflict is a lattice element like any other.

use std::collections::VecDeque;
use std::num::NonZeroU32;

use sumi_graph::NodeId;

/// `join` is commutative, associative, and idempotent with identity `bottom`; `transfer` and
/// `combine` are monotone; ascending chains are finite, or `solve` may not end.
pub trait Lattice: Clone + Eq {
    /// An edge from one provider.
    type Edge;
    /// An edge from two providers.
    type Pair;
    type Context;

    fn bottom() -> Self;

    /// Whether `self` grew.
    fn join(&mut self, other: &Self) -> bool;

    /// What the provider's evidence can do crossing `edge`.
    fn carries(edge: &Self::Edge) -> Carry;

    /// What the first provider's evidence, then the second's, can do crossing `pair`.
    fn carries_pair(pair: &Self::Pair) -> [Carry; 2];

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

    /// `exact`: the class recomputed with no flow cyclic, from what it held before its component
    /// was taken and its inward flows. True if changed.
    fn narrow(&mut self, exact: &Self) -> bool;
}

/// What a provider's evidence can do crossing an edge, least first.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Carry {
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
}

impl<L: Lattice> Flow<L> {
    /// Each provider with what its evidence can do crossing this flow, the first first.
    fn providers(&self) -> impl Iterator<Item = (Carry, NodeId)> + use<L> {
        let (first, second) = match &self.shape {
            Shape::Edge(edge) => (L::carries(edge), None),
            Shape::Pair { second, pair } => {
                let [first, of_second] = L::carries_pair(pair);
                (first, Some((of_second, *second)))
            }
        };
        std::iter::once((first, self.first)).chain(second)
    }

    fn widens(&self) -> bool {
        match &self.shape {
            Shape::Edge(edge) => L::widens(edge),
            Shape::Pair { pair, .. } => L::widens_pair(pair),
        }
    }

    fn grows(&self) -> bool {
        self.providers().any(|(carry, _)| carry == Carry::Grows)
    }
}

pub struct Solver<L: Lattice> {
    evidence: Vec<L>,
    flows: Vec<Flow<L>>,
}

impl<L: Lattice> Solver<L> {
    /// `n` is the graph's node count: class `i` is node `i`.
    pub fn with_classes(n: usize) -> Self {
        Self {
            evidence: vec![L::bottom(); n],
            flows: Vec::with_capacity(n),
        }
    }

    pub fn classes(&self) -> usize {
        self.evidence.len()
    }

    pub fn evidence(&self, node: NodeId) -> &L {
        &self.evidence[node.index()]
    }

    /// A fact about `node` or a demand on it alike; which one is not recorded.
    pub fn expect(&mut self, node: NodeId, evidence: &L) {
        self.evidence[node.index()].join(evidence);
    }

    /// [`expect`](Self::expect) joined in place, for a lattice built of parts.
    pub fn class_mut(&mut self, node: NodeId) -> &mut L {
        &mut self.evidence[node.index()]
    }

    pub fn flow(&mut self, provider: NodeId, consumer: NodeId, edge: L::Edge) {
        self.flows.push(Flow {
            consumer,
            first: provider,
            shape: Shape::Edge(edge),
        });
    }

    pub fn derive(&mut self, first: NodeId, second: NodeId, consumer: NodeId, pair: L::Pair) {
        self.flows.push(Flow {
            consumer,
            first,
            shape: Shape::Pair { second, pair },
        });
    }

    pub fn into_evidence(self) -> Vec<L> {
        self.evidence
    }

    /// Each one-provider flow's consumer, edge, and provider's evidence.
    pub fn edges(&self) -> impl Iterator<Item = (NodeId, &L::Edge, &L)> {
        self.flows.iter().filter_map(|flow| match &flow.shape {
            Shape::Edge(edge) => Some((flow.consumer, edge, self.evidence(flow.first))),
            Shape::Pair { .. } => None,
        })
    }

    /// A two-provider flow counts once, under its first provider.
    fn inward(&self, index: usize, provider: usize, of: &[u32], component: u32) -> Option<usize> {
        let flow = &self.flows[index];
        let consumer = flow.consumer.index();
        if of[consumer] != component {
            return None;
        }
        let first = flow.first.index();
        if first != provider && of[first] == component {
            return None;
        }
        Some(consumer)
    }

    fn delivery(&self, index: usize, cyclic: bool, cx: &L::Context) -> L {
        let flow = &self.flows[index];
        let first = self.evidence(flow.first);
        match &flow.shape {
            Shape::Edge(edge) => first.transfer(edge, cyclic, cx),
            Shape::Pair { second, pair } => first.combine(pair, self.evidence(*second), cyclic, cx),
        }
    }

    /// A cyclic delivery the consumer already holds is not rounded, so a value that only passes
    /// through a growing component stays exact.
    fn deliver(&mut self, index: usize, cyclic: bool, cx: &L::Context) -> bool {
        let consumer = self.flows[index].consumer.index();
        let exact = self.delivery(index, false, cx);
        if !cyclic || !self.flows[index].widens() {
            return self.evidence[consumer].join(&exact);
        }
        let mut probe = self.evidence[consumer].clone();
        if !probe.join(&exact) {
            return false;
        }
        let rounded = self.delivery(index, true, cx);
        self.evidence[consumer].join(&rounded)
    }

    fn ascend(
        &mut self,
        outgoing: &Outgoing,
        members: impl IntoIterator<Item = usize>,
        (of, component, cyclic): (&[u32], u32, &[bool]),
        queued: &mut [bool],
        queue: &mut VecDeque<usize>,
        cx: &L::Context,
    ) {
        let bottom = L::bottom();
        for member in members {
            if outgoing.head[member].is_some() && self.evidence[member] != bottom {
                queued[member] = true;
                queue.push_back(member);
            }
        }
        while let Some(provider) = queue.pop_front() {
            queued[provider] = false;
            for index in outgoing.of(provider) {
                let consumer = self.flows[index].consumer.index();
                if of[consumer] != component {
                    continue;
                }
                let cyclic = cyclic.get(index).is_some_and(|&cyclic| cyclic);
                if self.deliver(index, cyclic, cx) && !queued[consumer] {
                    queued[consumer] = true;
                    queue.push_back(consumer);
                }
            }
        }
    }

    pub fn solve(&mut self, cx: &L::Context) {
        let n = self.evidence.len();
        if self.flows.is_empty() {
            return;
        }
        // Prepending in reverse keeps each provider's flows in order.
        let mut outgoing = Outgoing {
            head: vec![None; n],
            links: Vec::with_capacity(self.flows.len()),
        };
        let mut arcs = Vec::with_capacity(self.flows.len());
        for (index, flow) in self.flows.iter().enumerate().rev() {
            let consumer = flow.consumer.index();
            for (_, provider) in flow.providers() {
                let provider = provider.index();
                outgoing.links.push((index as u32, outgoing.head[provider]));
                let link = u32::try_from(outgoing.links.len()).expect("flow count fits u32");
                outgoing.head[provider] = NonZeroU32::new(link);
                arcs.push((provider as u32, consumer as u32));
            }
        }
        let components = self::components(n, &arcs);
        let count = components.count();
        let mut inside = vec![false; count];
        let mut grows_in = vec![false; count];
        for (&(provider, consumer), &(index, _)) in arcs.iter().zip(&outgoing.links) {
            let component = components.of[consumer as usize];
            if components.of[provider as usize] == component {
                inside[component as usize] = true;
                grows_in[component as usize] |= self.flows[index as usize].grows();
            }
        }
        // Cycles of values are SCCs of the carrying arcs alone: a cycle closed through an arc that
        // carries nothing must not widen. One that climbs lies in a component a growing flow is
        // inside, so only those components' members get a value, `NEVER` marking the rest.
        const NEVER: u32 = u32::MAX;
        let values = grows_in.contains(&true).then(|| {
            let mut local = vec![NEVER; n];
            let mut numbered = 0u32;
            for component in (0..count).filter(|&component| grows_in[component]) {
                for &member in components.members(component) {
                    local[member as usize] = numbered;
                    numbered += 1;
                }
            }
            let mut carrying: Vec<(u32, u32)> = Vec::new();
            for flow in &self.flows {
                let consumer = flow.consumer.index();
                if local[consumer] == NEVER {
                    continue;
                }
                for (carry, provider) in flow.providers() {
                    let provider = provider.index();
                    if carry >= Carry::Passes && components.of[provider] == components.of[consumer]
                    {
                        carrying.push((local[provider], local[consumer]));
                    }
                }
            }
            let components = self::components(numbered as usize, &carrying);
            let values: Vec<u32> = local
                .iter()
                .map(|&local| match local {
                    NEVER => NEVER,
                    local => components.of[local as usize],
                })
                .collect();
            let mut climbs = vec![false; components.count()];
            let carried = |flow: &Flow<L>, value: u32, least: Carry| {
                flow.providers()
                    .any(|(carry, p)| carry >= least && values[p.index()] == value)
            };
            for flow in &self.flows {
                let value = values[flow.consumer.index()];
                if value != NEVER && carried(flow, value, Carry::Grows) {
                    climbs[value as usize] = true;
                }
            }
            let cyclic: Vec<bool> = self
                .flows
                .iter()
                .map(|flow| {
                    let value = values[flow.consumer.index()];
                    value != NEVER && climbs[value as usize] && carried(flow, value, Carry::Passes)
                })
                .collect();
            (values, climbs, cyclic)
        });
        let cyclic: &[bool] = values.as_ref().map_or(&[], |(_, _, cyclic)| cyclic);
        let mut growing = vec![false; count];
        for (&(provider, consumer), &(index, _)) in arcs.iter().zip(&outgoing.links) {
            let component = components.of[consumer as usize];
            if components.of[provider as usize] == component
                && cyclic.get(index as usize).is_some_and(|&cyclic| cyclic)
            {
                growing[component as usize] = true;
            }
        }
        drop(arcs);
        let any_grows = growing.contains(&true);
        let bottom = L::bottom();
        let mut queued = vec![false; n];
        let mut queue = VecDeque::new();
        let mut position = vec![0u32; if any_grows { n } else { 0 }];
        let mut external: Vec<L> = Vec::new();
        let mut incoming_start: Vec<u32> = Vec::new();
        let mut incoming: Vec<u32> = Vec::new();
        let mut preorder: Vec<u32> = Vec::new();
        let mut reached: Vec<bool> = Vec::new();
        let mut at = components.order.len();
        while at > 0 {
            at -= 1;
            let class = components.order[at] as usize;
            let current = components.of[class];
            if !inside[current as usize] {
                if outgoing.head[class].is_none() || self.evidence[class] == bottom {
                    continue;
                }
                for index in outgoing.of(class) {
                    self.deliver(index, false, cx);
                }
                continue;
            }
            // Reached at its last member: members are contiguous in `order`.
            let members = components.members(current as usize);
            at -= members.len() - 1;
            let grows = growing[current as usize];
            if grows {
                external.clear();
                external.extend(
                    members
                        .iter()
                        .map(|&member| self.evidence[member as usize].clone()),
                );
            }
            self.ascend(
                &outgoing,
                members.iter().map(|&member| member as usize),
                (&components.of, current, cyclic),
                &mut queued,
                &mut queue,
                cx,
            );
            // Narrowed in preorder from the root, each reading those already narrowed, so one pass
            // tightens along every acyclic path.
            if grows {
                let (values, climbing, _) = values
                    .as_ref()
                    .expect("a growing component has a climbing cycle");
                let climbs = |member: usize| climbing[values[member] as usize];
                for (position_of, &member) in members.iter().enumerate() {
                    position[member as usize] = position_of as u32;
                }
                incoming_start.clear();
                incoming_start.resize(members.len() + 2, 0);
                let mut inward = 0;
                for &provider in members {
                    for index in outgoing.of(provider as usize) {
                        if let Some(consumer) =
                            self.inward(index, provider as usize, &components.of, current)
                        {
                            incoming_start[position[consumer] as usize + 2] += 1;
                            inward += 1;
                        }
                    }
                }
                for i in 0..=members.len() {
                    incoming_start[i + 1] += incoming_start[i];
                }
                incoming.clear();
                incoming.resize(inward, 0);
                for &provider in members {
                    for index in outgoing.of(provider as usize) {
                        if let Some(consumer) =
                            self.inward(index, provider as usize, &components.of, current)
                        {
                            let slot = &mut incoming_start[position[consumer] as usize + 1];
                            incoming[*slot as usize] = index as u32;
                            *slot += 1;
                        }
                    }
                }
                preorder.clear();
                reached.clear();
                reached.resize(members.len(), false);
                let root = members.len() - 1;
                reached[root] = true;
                preorder.push(root as u32);
                let mut at = 0;
                while at < preorder.len() {
                    let member = members[preorder[at] as usize] as usize;
                    at += 1;
                    for index in outgoing.of(member) {
                        let consumer = self.flows[index].consumer.index();
                        if components.of[consumer] != current {
                            continue;
                        }
                        let consumer = position[consumer] as usize;
                        if !reached[consumer] {
                            reached[consumer] = true;
                            preorder.push(consumer as u32);
                        }
                    }
                }
                for _ in 0..NARROWING_PASSES {
                    let mut moved = false;
                    for &position_of in &preorder {
                        let position_of = position_of as usize;
                        if !climbs(members[position_of] as usize) {
                            continue;
                        }
                        let mut exact = external[position_of].clone();
                        for &index in &incoming[incoming_start[position_of] as usize
                            ..incoming_start[position_of + 1] as usize]
                        {
                            exact.join(&self.delivery(index as usize, false, cx));
                        }
                        moved |= self.evidence[members[position_of] as usize].narrow(&exact);
                    }
                    if !moved {
                        break;
                    }
                }
                // A descent cannot leave a fixpoint of copies, so members that never climb restart
                // from outside, where an ascent is exact.
                for (position_of, &member) in members.iter().enumerate() {
                    if !climbs(member as usize) {
                        self.evidence[member as usize] = external[position_of].clone();
                    }
                }
                self.ascend(
                    &outgoing,
                    members.iter().map(|&member| member as usize),
                    (&components.of, current, cyclic),
                    &mut queued,
                    &mut queue,
                    cx,
                );
            }
            for &member in members {
                let member = member as usize;
                if outgoing.head[member].is_none() || self.evidence[member] == bottom {
                    continue;
                }
                for index in outgoing.of(member) {
                    let component = components.of[self.flows[index].consumer.index()];
                    if component == current {
                        continue;
                    }
                    self.deliver(index, false, cx);
                }
            }
        }
    }
}

/// Links are one-based; a two-provider flow is listed under both providers.
struct Outgoing {
    head: Vec<Option<NonZeroU32>>,
    links: Vec<(u32, Option<NonZeroU32>)>,
}

impl Outgoing {
    fn of(&self, provider: usize) -> impl Iterator<Item = usize> + '_ {
        let mut link = self.head[provider];
        std::iter::from_fn(move || {
            let (index, next) = self.links[link?.get() as usize - 1];
            link = next;
            Some(index as usize)
        })
    }
}

/// Numbered in completion order: a component completes before any that reaches it.
pub(crate) struct Components {
    pub of: Vec<u32>,
    /// Every node, grouped by component in completion order.
    order: Vec<u32>,
    start: Vec<u32>,
}

impl Components {
    pub fn count(&self) -> usize {
        self.start.len() - 1
    }

    pub fn members(&self, component: usize) -> &[u32] {
        &self.order[self.start[component] as usize..self.start[component + 1] as usize]
    }
}

pub(crate) fn components(n: usize, arcs: &[(u32, u32)]) -> Components {
    // Rows are counted and filled one slot to the right, so the fill leaves the row starts in
    // place.
    let mut start = vec![0u32; n + 2];
    for &(from, _) in arcs {
        start[from as usize + 2] += 1;
    }
    for i in 0..=n {
        start[i + 1] += start[i];
    }
    let mut targets = vec![0u32; arcs.len()];
    for &(from, to) in arcs {
        targets[start[from as usize + 1] as usize] = to;
        start[from as usize + 1] += 1;
    }
    let adjacent = |node: usize| &targets[start[node] as usize..start[node + 1] as usize];
    // A slot holds the visit index while open, then the component. Completed nodes give their index
    // back, so a component is above every open index.
    let mut slot = vec![0u32; n];
    let mut index = 1u32;
    let mut component = u32::try_from(n)
        .expect("class count fits u32")
        .wrapping_sub(1);
    let mut order = Vec::with_capacity(n);
    let mut group_start = Vec::with_capacity(n + 1);
    group_start.push(0);
    let mut open: Vec<u32> = Vec::new();
    let mut work: Vec<(u32, u32, bool)> = Vec::new();
    for root in 0..n {
        if slot[root] != 0 {
            continue;
        }
        slot[root] = index;
        index += 1;
        work.push((root as u32, 0, true));
        while let Some(&mut (node, ref mut position, ref mut is_root)) = work.last_mut() {
            let node = node as usize;
            if let Some(&next) = adjacent(node).get(*position as usize) {
                let next = next as usize;
                *position += 1;
                if slot[next] == 0 {
                    slot[next] = index;
                    index += 1;
                    work.push((next as u32, 0, true));
                } else if slot[next] < slot[node] {
                    slot[node] = slot[next];
                    *is_root = false;
                }
                continue;
            }
            let (node, _, is_root) = work.pop().expect("the frame just read");
            let node = node as usize;
            if is_root {
                index -= 1;
                while let Some(&member) = open.last()
                    && slot[node] <= slot[member as usize]
                {
                    open.pop();
                    slot[member as usize] = component;
                    order.push(member);
                    index -= 1;
                }
                slot[node] = component;
                order.push(node as u32);
                group_start.push(order.len() as u32);
                component = component.wrapping_sub(1);
            } else {
                open.push(node as u32);
            }
            if let Some(&mut (parent, _, ref mut parent_is_root)) = work.last_mut()
                && slot[node] < slot[parent as usize]
            {
                slot[parent as usize] = slot[node];
                *parent_is_root = false;
            }
        }
    }
    let last = u32::try_from(n)
        .expect("class count fits u32")
        .wrapping_sub(1);
    for slot in &mut slot {
        *slot = last - *slot;
    }
    Components {
        of: slot,
        order,
        start: group_start,
    }
}

#[cfg(test)]
mod tests {
    use std::convert::Infallible;

    use super::*;

    #[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
    struct Set(u8);

    impl Lattice for Set {
        type Edge = ();
        type Pair = ();
        type Context = ();

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

    fn classes<L: Lattice, const N: usize>() -> (Solver<L>, [NodeId; N]) {
        (Solver::with_classes(N), std::array::from_fn(NodeId::new))
    }

    #[test]
    fn a_flow_is_five_words() {
        assert!(size_of::<crate::lattice::Pair>() <= 4);
        assert_eq!(size_of::<Flow<crate::lattice::Product>>(), 20);
    }

    #[test]
    fn components_follow_the_arcs() {
        let components = components(5, &[(0, 1), (1, 2), (2, 0), (1, 3), (4, 4)]);
        let component = &components.of;
        assert_eq!(component[0], component[1]);
        assert_eq!(component[1], component[2]);
        assert_ne!(component[0], component[3]);
        assert_ne!(component[0], component[4]);
        assert!(component[3] < component[0]);
        assert_eq!(components.count(), 3);
        let mut cycle = components.members(component[0] as usize).to_vec();
        cycle.sort_unstable();
        assert_eq!(cycle, [0, 1, 2]);
        assert_eq!(components.members(component[3] as usize), [3]);
        assert_eq!(components.members(component[4] as usize), [4]);
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
        type Pair = Infallible;
        type Context = ();

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

        fn carries_pair(never: &Infallible) -> [Carry; 2] {
            match *never {}
        }

        fn combine(&self, never: &Infallible, _: &Self, _: bool, (): &()) -> Self {
            match *never {}
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
            solver.solve(&());
            assert_eq!(*solver.evidence(x), Hull { lo: 0, hi: 107 });
            assert_eq!(*solver.evidence(capped), Hull { lo: 0, hi: 100 });
            assert_eq!(*solver.evidence(stepped), Hull { lo: 7, hi: 107 });
            assert_eq!(*solver.evidence(downstream), Hull { lo: 1, hi: 108 });
        }
    }

    #[test]
    fn narrowing_keeps_an_unbounded_chain_unbounded() {
        let (mut solver, [x, stepped]) = classes::<Hull, 2>();
        solver.expect(x, &Hull { lo: 0, hi: 0 });
        solver.flow(x, stepped, HullEdge::Add(1));
        solver.flow(stepped, x, HullEdge::Add(0));
        solver.solve(&());
        assert_eq!(
            *solver.evidence(x),
            Hull {
                lo: 0,
                hi: i64::MAX
            }
        );
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
        solver.solve(&());
        assert_eq!(*solver.evidence(passed), Hull { lo: 4, hi: 9 });
        assert_eq!(*solver.evidence(x), Hull { lo: 0, hi: 107 });
        assert_eq!(*solver.evidence(first), Hull { lo: 0, hi: 107 });
        assert_eq!(*solver.evidence(second), Hull { lo: 0, hi: 107 });
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
        solver.solve(&());
        assert!(!solver.evidence(a).cyclic);
        assert!(solver.evidence(b).cyclic && solver.evidence(c).cyclic);
        assert_eq!(solver.evidence(d).set, 1);
    }

    #[test]
    fn expectations_join_and_flows_deliver() {
        let (mut solver, [a, b]) = classes::<Set, 2>();
        solver.flow(a, b, ());
        solver.expect(a, &Set(1));
        solver.expect(a, &Set(2));
        solver.solve(&());
        assert_eq!(*solver.evidence(a), Set(3));
        assert_eq!(*solver.evidence(b), Set(3));
    }

    #[test]
    fn flows_never_carry_evidence_back() {
        let (mut solver, [provider, consumer]) = classes::<Set, 2>();
        solver.flow(provider, consumer, ());
        solver.expect(consumer, &Set(1));
        solver.solve(&());
        assert_eq!(*solver.evidence(provider), Set::bottom());
        assert_eq!(*solver.evidence(consumer), Set(1));
    }

    #[test]
    fn intervals_narrow_transfer_and_empty_out() {
        let (mut solver, [x, y]) = classes::<Interval, 2>();
        solver.expect(x, &Interval::new(0, 10));
        solver.flow(x, y, 100);
        solver.expect(x, &Interval::new(5, 20));
        solver.expect(y, &Interval::new(130, 140));
        solver.solve(&());
        assert_eq!(*solver.evidence(x), Interval::new(5, 10));
        assert!(solver.evidence(y).is_empty());
    }

    fn constraint() -> impl proptest::strategy::Strategy<Value = (u8, usize, usize)> {
        (0u8..3, 0usize..8, 0usize..8)
    }

    fn apply(solver: &mut Solver<Set>, vars: &[NodeId], (kind, a, b): (u8, usize, usize)) {
        match kind {
            0 => solver.expect(vars[a], &Set(1 << (b % 3))),
            1 => solver.flow(vars[a], vars[b], ()),
            _ => solver.derive(vars[a], vars[b], vars[(b + 1) % 8], ()),
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
            ordered.solve(&());
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
            shuffled.solve(&());
            for (&a, &b) in vars.iter().zip(&shuffled_vars) {
                proptest::prop_assert_eq!(ordered.evidence(a), shuffled.evidence(b));
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
            let mut expected = solver.evidence.clone();
            loop {
                let mut changed = false;
                for flow in &solver.flows {
                    let first = expected[flow.first.index()];
                    let evidence = match flow.shape {
                        Shape::Edge(()) => first.transfer(&(), false, &()),
                        Shape::Pair { second, pair: () } => {
                            first.combine(&(), &expected[second.index()], false, &())
                        }
                    };
                    changed |= expected[flow.consumer.index()].join(&evidence);
                }
                if !changed {
                    break;
                }
            }
            solver.solve(&());
            for &var in &vars {
                proptest::prop_assert_eq!(*solver.evidence(var), expected[var.index()]);
            }
        }
    }
}
