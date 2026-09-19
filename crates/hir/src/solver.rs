//! A lattice-join solver: a join-semilattice payload on each class, and
//! directed flow between classes with a transfer function on every edge. In
//! dataflow terms, a monotone framework.
//!
//! The solver knows nothing about types. An instance chooses the [`Lattice`]:
//! what the evidence on a class is, how two pieces of it combine, and how
//! evidence changes when it crosses a flow.
//!
//! Two constraint forms feed it. [`expect`](Solver::expect) joins evidence
//! into a class, what it is known to be on its own account or what one use
//! of it demands alike, and because join is commutative, associative, and
//! idempotent the order of arrival is invisible in the result; the instance
//! remembers which evidence was a fact. [`flow`](Solver::flow) lets
//! evidence pass from one class to another and never back: the consumer
//! learns everything the provider knows, transformed by the edge, and the
//! provider is unaffected by what its consumers demand, which keeps blame
//! on the consumer's side. [`derive`](Solver::derive) is a flow with two
//! providers, for evidence that is a function of two classes, an operator's
//! result of its operands. Evidence is applied as it arrives; flows are
//! settled by [`solve`](Solver::solve), a worklist over the flow graph.
//!
//! A transfer may consult a context the instance supplies to `solve`: what
//! is true of the whole program and fixed before any flow settles, such as
//! the constants an interval analysis rounds to. It is also told whether
//! its flow closes a cycle of the flow graph that can grow, which is where
//! a lattice without finite ascending chains of its own must widen: the
//! solver finds the cycles, the lattice says which edges can grow a value,
//! and a cycle of edges that only pass values along, refine them, or gate
//! them settles on its own.
//!
//! Widening overshoots by construction: at the moment it fires it cannot
//! tell a chain that a guard will stop from one that never stops. So
//! `solve` works one strongly connected component at a time, providers
//! first, and narrows each before anything downstream reads it: it
//! recomputes each class of the component exactly from what it held before
//! the component was taken and the flows inside it, with no flow told it
//! is cyclic, and lets the lattice take back what the overshoot cost, since
//! at a post-fixpoint the exact recomputation can only be smaller. The
//! passes stop when nothing moves or at a fixed bound, every prefix of a
//! descent being sound.
//!
//! A conflict is a lattice element like any other. The solver never retracts
//! evidence or stops at the first disagreement, so when an instance reads a
//! class it sees every claim made about it, and the classes around a
//! conflicted one are untouched.

use std::collections::VecDeque;
use std::num::NonZeroU32;

use sumi_graph::NodeId;

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

    /// What of the first provider's evidence, or the `second` one's, can
    /// climb through `edge` into the consumer. The cycles an ascent can
    /// run on are cycles of arcs that carry, and a cycle some arc grows
    /// along is what widening cuts; a cycle of arcs that only pass settles
    /// in one lap, and a cycle closed through an arc that carries nothing
    /// is no cycle of values.
    fn carries(edge: &Self::Edge, second: bool) -> Carry;

    /// The evidence a consumer receives when `self`, and for a two-provider
    /// edge `other`, cross `edge`. `cyclic` says the flow lies on a cycle of
    /// the flow graph that can grow, so the evidence delivered here may come
    /// back larger.
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

    /// Take back what widening overshot: `exact` is everything the class
    /// held before its component was taken — what was joined into it
    /// before the solve and what flowed in from outside — plus what the
    /// flows inside the component deliver with none treated as cyclic,
    /// recomputed once the worklist has settled, so it is at most `self`.
    /// A lattice that never widens has nothing to take back. Reports
    /// whether `self` changed.
    fn narrow(&mut self, exact: &Self) -> bool;
}

/// What a provider's evidence can do crossing an edge into the consumer,
/// least first.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Carry {
    /// Nothing that can climb: the edge delivers nothing of the provider's,
    /// or only something finite, a boolean or whether a point is live.
    Nothing,
    /// A copy or a narrowing of it, or the value a gate lets through: never
    /// more than the provider holds.
    Passes,
    /// More than the provider holds: a value an operator computes from it.
    Grows,
}

/// The most exact passes a narrowing makes. One pass carries a tightening
/// through every acyclic path, providers first; a cycle descends one pass
/// at a time, and a pair of counters that bound each other can descend for
/// as many passes as they have steps, which this cuts short: every prefix
/// of a descent is sound, so stopping early costs precision, never
/// soundness.
const NARROWING_PASSES: usize = 8;

/// One flow: what `consumer` learns from `first`, and from `second` when
/// the edge has two providers, through `edge`.
struct Flow<E> {
    first: NodeId,
    second: Option<NodeId>,
    consumer: NodeId,
    edge: E,
}

pub struct Solver<L: Lattice> {
    /// By class index.
    evidence: Vec<L>,
    /// Settled by `solve`.
    flows: Vec<Flow<L::Edge>>,
}

impl<L: Lattice> Solver<L> {
    /// A solver of `n` classes, one per node of a graph of `n` nodes at
    /// the node's index, that nothing is known about yet, with room for
    /// about a flow per class.
    pub fn with_classes(n: usize) -> Self {
        Self {
            evidence: vec![L::bottom(); n],
            flows: Vec::with_capacity(n),
        }
    }

    /// How many classes there are: the node count the solver was made
    /// for, since nothing merges or adds a class.
    pub fn classes(&self) -> usize {
        self.evidence.len()
    }

    /// The evidence on `node`.
    pub fn evidence(&self, node: NodeId) -> &L {
        &self.evidence[node.index()]
    }

    /// Join `evidence` into `node`: a fact it carries on its own account, or
    /// what one use of it demands. The solver keeps no record of which.
    pub fn expect(&mut self, node: NodeId, evidence: &L) {
        self.evidence[node.index()].join(evidence);
    }

    /// Let everything `provider`'s class learns reach `consumer`'s class
    /// through `edge`, and nothing travel back. Settled by `solve`.
    pub fn flow(&mut self, provider: NodeId, consumer: NodeId, edge: L::Edge) {
        self.flows.push(Flow {
            first: provider,
            second: None,
            consumer,
            edge,
        });
    }

    /// Let `consumer`'s class learn the transfer of `first`'s and
    /// `second`'s evidence through `edge`, recomputed whenever either grows.
    pub fn derive(&mut self, first: NodeId, second: NodeId, consumer: NodeId, edge: L::Edge) {
        self.flows.push(Flow {
            first,
            second: Some(second),
            consumer,
            edge,
        });
    }

    /// The evidence of every class by index, and nothing else: what is
    /// left once no more flows will be settled.
    pub fn into_evidence(self) -> Vec<L> {
        self.evidence
    }

    /// Every flow: its consumer, its edge, and what its first provider
    /// holds.
    pub fn flows(&self) -> impl Iterator<Item = (NodeId, &L::Edge, &L)> {
        self.flows
            .iter()
            .map(|flow| (flow.consumer, &flow.edge, self.evidence(flow.first)))
    }

    /// A flow's providers, each with whether it is the second.
    fn providers<'f>(&self, flow: &'f Flow<L::Edge>) -> impl Iterator<Item = (bool, NodeId)> + 'f {
        std::iter::once((false, flow.first)).chain(flow.second.map(|second| (true, second)))
    }

    /// Whether some provider's evidence grows crossing `flow`.
    fn grows(&self, flow: &Flow<L::Edge>) -> bool {
        self.providers(flow)
            .any(|(second, _)| L::carries(&flow.edge, second) == Carry::Grows)
    }

    /// The consumer of flow `index` when the flow stays inside `component`
    /// and is counted under `provider`: a flow with both providers inside is
    /// listed under both, and counts under the first.
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

    /// What flow `index` delivers to its consumer, from its providers as
    /// they are now.
    fn delivery(&self, index: usize, cyclic: bool, cx: &L::Context) -> L {
        let flow = &self.flows[index];
        let second = flow.second.map(|second| self.evidence(second));
        self.evidence(flow.first)
            .transfer(&flow.edge, second, cyclic, cx)
    }

    /// Deliver flow `index`: whether its consumer grew. Widening is for
    /// growth alone: a cyclic delivery the consumer already holds is not
    /// rounded, so a value that only passes through a growing component
    /// stays exact, while a consumer on a cycle still lands on the
    /// thresholds every time it grows.
    fn deliver(&mut self, index: usize, cyclic: bool, cx: &L::Context) -> bool {
        let consumer = self.flows[index].consumer.index();
        let exact = self.delivery(index, false, cx);
        if !cyclic {
            return self.evidence[consumer].join(&exact);
        }
        let mut probe = self.evidence[consumer].clone();
        if !probe.join(&exact) {
            return false;
        }
        let rounded = self.delivery(index, true, cx);
        self.evidence[consumer].join(&rounded)
    }

    /// Carry growth from the `members` of one component that have something
    /// to deliver along the flows that stay inside it, and on from every
    /// consumer that grows. A class waits in the queue at most once however
    /// often it grows before its turn: a join can improve evidence in ways
    /// no transfer passes on, and every visit rescans every outgoing flow.
    /// Every flow from a member to a member closes a cycle, and `grows` says
    /// whether that cycle can grow.
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

    /// Settle every flow. The flow graph is taken one strongly connected
    /// component at a time, providers first: a class on no cycle has all it
    /// will get when its turn comes and delivers along its flows once, and
    /// a component some flow stays inside is settled by a worklist over its
    /// members, narrowed by a bounded number of exact passes when it can
    /// grow, and then delivers along the flows that leave it. A class is
    /// visited once for each time it grows while not already waiting, and
    /// a visit scans its outgoing flows, so the work is bounded by the
    /// flows times the height of the lattice, plus the exact passes.
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
            for (_, provider) in self.providers(flow) {
                let provider = provider.index();
                outgoing.links.push((index as u32, outgoing.head[provider]));
                let link = u32::try_from(outgoing.links.len()).expect("flow count fits u32");
                outgoing.head[provider] = NonZeroU32::new(link);
                arcs.push((provider as u32, consumer as u32));
            }
        }
        // The components of every arc are the schedule: what a class can
        // reach, it is settled before. A component is widened only where a
        // flow inside it can grow a value.
        let components = self::components(n, &arcs);
        let count = components.count();
        let mut inside = vec![false; count];
        let mut grows_inside = false;
        for (&(provider, consumer), &(index, _)) in arcs.iter().zip(&outgoing.links) {
            let component = components.of[consumer as usize];
            if components.of[provider as usize] == component {
                inside[component as usize] = true;
                grows_inside |= self.grows(&self.flows[index as usize]);
            }
        }
        // Values climb along the carrying arcs alone, so their cycles are
        // the components of those, found only when some cycle can grow: a
        // flow is cyclic, to be widened, when its consumer's value component
        // has an edge that grows and a carrying provider of the flow is
        // inside it. A cycle closed through an arc that carries nothing, a
        // peer's claims or a context, is no cycle of values.
        let values = grows_inside.then(|| {
            let mut carrying: Vec<(u32, u32)> = Vec::with_capacity(self.flows.len());
            for flow in &self.flows {
                let consumer = flow.consumer.index() as u32;
                for (second, provider) in self.providers(flow) {
                    if L::carries(&flow.edge, second) != Carry::Nothing {
                        carrying.push((provider.index() as u32, consumer));
                    }
                }
            }
            let values = self::components(n, &carrying);
            let mut climbs = vec![false; values.count()];
            // Whether some provider of `flow` inside the value component
            // `value` carries at least `least` along it.
            let carried = |flow: &Flow<L::Edge>, value: u32, least: Carry| {
                self.providers(flow).any(|(second, p): (bool, NodeId)| {
                    L::carries(&flow.edge, second) >= least && values.of[p.index()] == value
                })
            };
            for flow in &self.flows {
                let value = values.of[flow.consumer.index()];
                if carried(flow, value, Carry::Grows) {
                    climbs[value as usize] = true;
                }
            }
            let cyclic: Vec<bool> = self
                .flows
                .iter()
                .map(|flow| {
                    let value = values.of[flow.consumer.index()];
                    climbs[value as usize] && carried(flow, value, Carry::Passes)
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
        // Narrowing scratch, kept across the components that grow: what each
        // member was before its component moved it, then the exact
        // recomputation, by the member's position in its component. Nothing
        // to narrow, nothing to allocate.
        let mut position = vec![0u32; if any_grows { n } else { 0 }];
        let mut external: Vec<L> = Vec::new();
        // The flows into each member from inside its component, in
        // compressed sparse rows by position, and the members in a
        // preorder from the component's root along those flows.
        let mut incoming_start: Vec<u32> = Vec::new();
        let mut incoming: Vec<u32> = Vec::new();
        let mut preorder: Vec<u32> = Vec::new();
        let mut reached: Vec<bool> = Vec::new();
        // A delivery from outside a component is made once and never
        // widened; what a member holds before its component is taken is
        // what the narrowing recomputes from.
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
            // A component some flow stays inside, reached at its last member.
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
            // Ascend: what comes from outside is already in, so a worklist
            // over the members carries growth along the flows that stay
            // inside.
            self.ascend(
                &outgoing,
                members.iter().map(|&member| member as usize),
                (&components.of, current, cyclic),
                &mut queued,
                &mut queue,
                cx,
            );
            // Narrow: recompute each member exactly from what it was and the
            // flows into it from inside, with none told it is cyclic, until
            // nothing moves. Members are taken in a preorder from the
            // component's root and each reads the members already narrowed
            // in the pass, so one pass carries a tightening along every
            // path that does not come back on itself; a cycle descends one
            // pass at a time.
            if grows {
                let (values, climbing, _) = values
                    .as_ref()
                    .expect("a growing component has a climbing cycle");
                let climbs = |member: usize| climbing[values.of[member] as usize];
                for (position_of, &member) in members.iter().enumerate() {
                    position[member as usize] = position_of as u32;
                }
                // The rows are counted one slot to the right and filled with
                // the cursor one slot to the right, as `components` does.
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
                // A member whose values never climb took its overshoot from
                // the members that did, and a descent cannot leave a
                // fixpoint of copies; but with no widening among them their
                // least fixpoint is what an ascent finds. Start those over
                // from what came from outside, with the climbing members
                // settled where the descent left them.
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
            // Deliver: each member with something to deliver feeds the flows
            // that leave the component, whose consumers are not taken yet.
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

/// The flows out of each class, as one-based links so `None` is compact:
/// `head` holds a class's first link, and each link names a flow and the
/// next link. A two-provider flow is listed under both providers, since
/// either can grow.
struct Outgoing {
    head: Vec<Option<NonZeroU32>>,
    links: Vec<(u32, Option<NonZeroU32>)>,
}

impl Outgoing {
    /// The flows out of `provider`.
    fn of(&self, provider: usize) -> impl Iterator<Item = usize> + '_ {
        let mut link = self.head[provider];
        std::iter::from_fn(move || {
            let (index, next) = self.links[link?.get() as usize - 1];
            link = next;
            Some(index as usize)
        })
    }
}

/// The strongly connected components of `n` nodes under `arcs`, numbered in
/// reverse topological order: a component completes before any that reaches
/// it.
pub(crate) struct Components {
    /// The component of each node.
    pub of: Vec<u32>,
    /// Every node, grouped by component, in the order the components
    /// complete.
    order: Vec<u32>,
    /// Where each component's run of `order` begins, and one past the last.
    start: Vec<u32>,
}

impl Components {
    pub fn count(&self) -> usize {
        self.start.len() - 1
    }

    /// The nodes of component `component`.
    pub fn members(&self, component: usize) -> &[u32] {
        &self.order[self.start[component] as usize..self.start[component + 1] as usize]
    }
}

/// Pearce's one-array variant of Tarjan's algorithm, on an explicit stack:
/// a node's slot holds its visit index while it is open, then the number of
/// its component.
pub(crate) fn components(n: usize, arcs: &[(u32, u32)]) -> Components {
    // Adjacency in compressed sparse rows: a few allocations however many
    // nodes, since a solve calls this once over every class. The rows are
    // counted one slot to the right and filled with the cursor one slot to
    // the right, so no second copy of the row starts is needed.
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
    // Visit indices count up from one; component numbers count down from
    // `n - 1`, and since every completed node gives an index back, a
    // component number is always above every open index.
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
    // Numbered from zero in completion order.
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
        fn carries((): &(), _: bool) -> Carry {
            Carry::Passes
        }

        fn transfer(&self, (): &(), other: Option<&Self>, _: bool, (): &()) -> Self {
            Self(self.0 | other.map_or(0, |other| other.0))
        }

        fn narrow(&mut self, _: &Self) -> bool {
            false
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

        fn carries(offset: &i64, _: bool) -> Carry {
            if *offset == 0 {
                Carry::Passes
            } else {
                Carry::Grows
            }
        }

        fn transfer(&self, offset: &i64, _: Option<&Self>, _: bool, (): &()) -> Self {
            Self::new(
                self.lo.saturating_add(*offset),
                self.hi.saturating_add(*offset),
            )
        }

        fn narrow(&mut self, _: &Self) -> bool {
            false
        }
    }

    /// `N` classes nothing is known about yet, by index.
    fn classes<L: Lattice, const N: usize>() -> (Solver<L>, [NodeId; N]) {
        (Solver::with_classes(N), std::array::from_fn(NodeId::new))
    }

    /// Three classes, and an edge of two words: no edge carries where it
    /// came from, since the graph knows.
    #[test]
    fn a_flow_is_five_words() {
        assert_eq!(size_of::<Option<NodeId>>(), 4);
        assert_eq!(size_of::<Flow<crate::lattice::Edge>>(), 20);
    }

    #[test]
    fn components_follow_the_arcs() {
        // 0 -> 1 -> 2 -> 0 is a cycle; 3 hangs off it; 4 is alone.
        let components = components(5, &[(0, 1), (1, 2), (2, 0), (1, 3), (4, 4)]);
        let component = &components.of;
        assert_eq!(component[0], component[1]);
        assert_eq!(component[1], component[2]);
        assert_ne!(component[0], component[3]);
        assert_ne!(component[0], component[4]);
        // The callee completes first.
        assert!(component[3] < component[0]);
        assert_eq!(components.count(), 3);
        let mut cycle = components.members(component[0] as usize).to_vec();
        cycle.sort_unstable();
        assert_eq!(cycle, [0, 1, 2]);
        assert_eq!(components.members(component[3] as usize), [3]);
        assert_eq!(components.members(component[4] as usize), [4]);
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

        fn carries((): &(), _: bool) -> Carry {
            Carry::Grows
        }

        /// Nothing comes of nothing: an empty set is not marked.
        fn transfer(&self, (): &(), _: Option<&Self>, cyclic: bool, (): &()) -> Self {
            Self {
                set: self.set,
                cyclic: self.cyclic | (cyclic && self.set != 0),
            }
        }

        fn narrow(&mut self, _: &Self) -> bool {
            false
        }
    }

    /// A hull of integers that widens to `i64::MAX` on a cyclic flow and
    /// narrows back to whatever the exact recomputation says: the shape of
    /// an interval analysis, with an edge that adds and one that caps.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    struct Hull {
        lo: i64,
        hi: i64,
    }

    #[derive(Clone, Copy)]
    enum HullEdge {
        Add(i64),
        Cap(i64),
        /// Delivers nothing: an arc of the schedule, not of the values.
        Inert,
    }

    impl Lattice for Hull {
        type Edge = HullEdge;
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

        fn carries(edge: &HullEdge, _: bool) -> Carry {
            match edge {
                HullEdge::Inert => Carry::Nothing,
                HullEdge::Add(k) if *k != 0 => Carry::Grows,
                _ => Carry::Passes,
            }
        }

        fn transfer(&self, edge: &HullEdge, _: Option<&Self>, cyclic: bool, (): &()) -> Self {
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

    /// `x = {0} ∪ ((x ∩ (-∞, 100]) + 7)`: widening sends `x` to the top,
    /// and narrowing brings it back to the exact fixpoint `[0, 107]`, along
    /// with everything downstream of it, however the flows arrived.
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

    /// A chain with no cap keeps the overshoot: narrowing recomputes what
    /// the flows deliver, and with nothing bounding the climb that is the
    /// widened value itself.
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

    /// A cycle closed by an arc that carries no value is no cycle of values:
    /// a bound value passed around it is never widened, and a cycle of
    /// copies downstream of a widened class in the same component, which a
    /// descent alone could not leave, is recomputed exactly once the class
    /// has narrowed.
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
        // `d` is downstream of the cycle: its own flow is not on it, but the
        // evidence it receives was marked on the way.
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

    /// One constraint over eight classes: an expectation, a flow, or a
    /// derive into the class after the second.
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
        /// The three lattice laws promise that arrival order is invisible;
        /// this checks the solver keeps that promise.
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

        /// The worklist agrees with a naive fixed point that has no adjacency
        /// structure and rescans every flow until nothing changes.
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
                    let second = flow.second.map(|second| expected[second.index()]);
                    let evidence = first.transfer(&(), second.as_ref(), false, &());
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
