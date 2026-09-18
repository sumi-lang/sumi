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
//! result. [`expect`](Solver::expect) joins evidence into a class, what it
//! is known to be on its own account or what one use of it demands alike;
//! the instance remembers which is which, and restates the facts to a
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

    /// Whether `edge` can deliver more than it receives: an operator over
    /// its operands, where an edge that copies, narrows, or gates a value
    /// cannot. A cycle with no such edge settles in one lap and is never
    /// widened.
    fn grows(edge: &Self::Edge) -> bool;

    /// Whether what the first provider holds, or the `second` one's, can
    /// climb through `edge` into the consumer: a value an operator computes
    /// from it, a copy or a narrowing of it, the value a gate lets through.
    /// The cycles an ascent can run on are cycles of such arcs, and those
    /// are the cycles widening cuts. An edge that delivers nothing, or only
    /// something finite, a boolean or whether a point is live, carries
    /// none, and a cycle closed through it alone is no cycle of values.
    fn carries(edge: &Self::Edge, second: bool) -> bool;

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

    fn grows(edge: &Self::Edge) -> bool {
        A::grows(&edge.0) || B::grows(&edge.1)
    }

    fn carries(edge: &Self::Edge, second: bool) -> bool {
        A::carries(&edge.0, second) || B::carries(&edge.1, second)
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

    fn narrow(&mut self, exact: &Self) -> bool {
        let a = self.0.narrow(&exact.0);
        let b = self.1.narrow(&exact.1);
        a | b
    }
}

/// The most exact passes a narrowing makes. One pass carries a tightening
/// through every acyclic path, providers first; a cycle descends one pass
/// at a time, and a pair of counters that bound each other can descend for
/// as many passes as they have steps, which this cuts short: every prefix
/// of a descent is sound, so stopping early costs precision, never
/// soundness.
const NARROWING_PASSES: usize = 8;

/// A member of some class: what the solver hands out and takes back. One
/// past its index, so an `Option<Var>` is one word.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Var(NonZeroU32);

impl Var {
    /// The class at `index`: the `index`th one opened.
    pub fn new(index: usize) -> Self {
        let past = u32::try_from(index + 1).expect("class count fits u32");
        Self(NonZeroU32::new(past).expect("one past an index"))
    }

    /// The index the class was opened at.
    pub fn index(self) -> usize {
        self.0.get() as usize - 1
    }
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
    /// Settled by `solve`.
    flows: Vec<Flow<L::Edge>>,
}

impl<L: Lattice> Default for Solver<L> {
    fn default() -> Self {
        Self::with_capacity(0, 0)
    }
}

impl<L: Lattice> Solver<L> {
    /// A solver with room for `classes` classes and `flows` flows before
    /// any vector grows. Only a guide.
    pub fn with_capacity(classes: usize, flows: usize) -> Self {
        Self {
            parent: Vec::with_capacity(classes),
            size: Vec::with_capacity(classes),
            evidence: Vec::with_capacity(classes),
            flows: Vec::with_capacity(flows),
        }
    }

    /// A solver of `n` classes, `Var::new(0)` to `Var::new(n - 1)`, that
    /// nothing is known about yet, with room for about a flow per class.
    /// The caller's numbering is the solver's.
    pub fn with_classes(n: usize) -> Self {
        Self {
            parent: (0..n as u32).collect(),
            size: vec![1; n],
            evidence: vec![L::bottom(); n],
            flows: Vec::with_capacity(n),
        }
    }

    /// One more class, nothing known about it yet, numbered after every
    /// class so far: how the solver's tests and benches grow a graph. The
    /// checker opens every class at once.
    #[allow(dead_code)]
    pub fn fresh(&mut self) -> Var {
        let var = Var::new(self.parent.len());
        let id = u32::try_from(self.parent.len()).expect("class count fits u32");
        self.parent.push(id);
        self.size.push(1);
        self.evidence.push(L::bottom());
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

    /// A fresh class that `provider` flows into through `edge`.
    #[cfg(test)]
    pub fn import(&mut self, provider: Var, edge: L::Edge) -> Var {
        let consumer = self.fresh();
        self.flow(provider, consumer, edge);
        consumer
    }

    /// The evidence on `var`'s class.
    pub fn evidence(&self, var: Var) -> &L {
        &self.evidence[self.root(var.index())]
    }

    /// Join `evidence` into `var`'s class: a fact it carries on its own
    /// account, or what one use of it demands. The solver keeps no record
    /// of which; the instance restates its facts to a replay.
    pub fn expect(&mut self, var: Var, evidence: &L) {
        let root = self.compress(var.index());
        self.evidence[root].join(evidence);
    }

    /// A fresh class carrying `evidence`.
    #[cfg(test)]
    pub fn known(&mut self, evidence: L) -> Var {
        let var = self.fresh();
        self.expect(var, &evidence);
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

    /// `var`'s root, once every class is compressed: one load.
    fn class(&self, var: Var) -> usize {
        self.parent[var.index()] as usize
    }

    /// The evidence of every class by index, each merged class's being
    /// its root's, and nothing else: what is left once no more flows
    /// will be settled.
    pub fn into_evidence(mut self) -> Vec<L> {
        for index in 0..self.parent.len() {
            let root = self.root(index);
            if root != index {
                self.evidence[index] = self.evidence[root].clone();
            }
        }
        self.evidence
    }

    /// A flow's providers, each with whether it is the second.
    fn providers<'f>(&self, flow: &'f Flow<L::Edge>) -> impl Iterator<Item = (bool, Var)> + 'f {
        std::iter::once((false, flow.first)).chain(flow.second.map(|second| (true, second)))
    }

    /// The consumer of flow `index` when the flow stays inside `component`
    /// and is counted under `provider`: a flow with both providers inside is
    /// listed under both, and counts under the first.
    fn inward(&self, index: usize, provider: usize, of: &[u32], component: u32) -> Option<usize> {
        let flow = &self.flows[index];
        let consumer = self.class(flow.consumer);
        if of[consumer] != component {
            return None;
        }
        let first = self.class(flow.first);
        if first != provider && of[first] == component {
            return None;
        }
        Some(consumer)
    }

    /// What flow `index` delivers to its consumer, from its providers as
    /// they are now.
    fn delivery(&self, index: usize, cyclic: bool, cx: &L::Context) -> L {
        let flow = &self.flows[index];
        let second = flow.second.map(|second| &self.evidence[self.class(second)]);
        self.evidence[self.class(flow.first)].transfer(&flow.edge, second, cyclic, cx)
    }

    /// Deliver flow `index`: whether its consumer grew. Widening is for
    /// growth alone: a cyclic delivery the consumer already holds is not
    /// rounded, so a value that only passes through a growing component
    /// stays exact, while a consumer on a cycle still lands on the
    /// thresholds every time it grows.
    fn deliver(&mut self, index: usize, cyclic: bool, cx: &L::Context) -> bool {
        let consumer = self.class(self.flows[index].consumer);
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
                let consumer = self.class(self.flows[index].consumer);
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

    /// Settle every flow. Call once every equality is in; a flow between
    /// classes unioned afterwards is not revisited. The flow graph is taken
    /// one strongly connected component at a time, providers first. A class
    /// on no cycle has all it will get when its turn comes and delivers
    /// along its flows once. A component some flow stays inside is settled
    /// by a worklist over its members, narrowed by a bounded number of
    /// exact passes when it can grow, and then delivers along the flows
    /// that leave it, into components not yet taken. A class is visited
    /// once for each time it grows while not already waiting, and a visit
    /// scans its outgoing flows, so the work is bounded by the flows times
    /// the height of the lattice, plus the exact passes.
    pub fn solve(&mut self, cx: &L::Context) {
        let n = self.parent.len();
        for id in 0..n {
            self.compress(id);
        }
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
            let consumer = self.class(flow.consumer);
            for (_, provider) in self.providers(flow) {
                let provider = self.class(provider);
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
                grows_inside |= L::grows(&self.flows[index as usize].edge);
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
                let consumer = self.class(flow.consumer) as u32;
                for (second, provider) in self.providers(flow) {
                    if L::carries(&flow.edge, second) {
                        carrying.push((self.class(provider) as u32, consumer));
                    }
                }
            }
            let values = self::components(n, &carrying);
            let mut climbs = vec![false; values.count()];
            let carried = |flow: &Flow<L::Edge>, value: u32| {
                self.providers(flow).any(|(second, p): (bool, Var)| {
                    L::carries(&flow.edge, second) && values.of[self.class(p)] == value
                })
            };
            for flow in &self.flows {
                let value = values.of[self.class(flow.consumer)];
                if L::grows(&flow.edge) && carried(flow, value) {
                    climbs[value as usize] = true;
                }
            }
            let cyclic: Vec<bool> = self
                .flows
                .iter()
                .map(|flow| {
                    let value = values.of[self.class(flow.consumer)];
                    climbs[value as usize] && carried(flow, value)
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
        // Every class, providers first: a class outside any cycle has all it
        // will get by the time it is reached, so it delivers once. A delivery
        // made from outside a component happens once, so it is never
        // widened: only the worklist inside a growing component rounds, and
        // what a member holds before its component is taken stays exact for
        // the narrowing to recompute from.
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
                        let consumer = self.class(self.flows[index].consumer);
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
                    let component = components.of[self.class(self.flows[index].consumer)];
                    if component == current {
                        continue;
                    }
                    self.deliver(index, false, cx);
                }
            }
        }
    }

    /// A solver over the same classes as singletons again, carrying only
    /// the `facts` the instance restates, as its replay reads them, and
    /// what `export` lets each settled flow deliver to its consumer, in a
    /// lattice `M` of the instance's choosing: the part of the evidence its
    /// replay reads, which need not be all of it. Replaying expectations
    /// one at a time on it attributes a disagreement to the expectation
    /// that first raised it, with the flows final rather than provisional.
    /// `export` sees the provider's settled evidence, the second provider's
    /// for a two-provider flow, and the edge.
    pub fn replay<M: Lattice>(
        &self,
        facts: impl IntoIterator<Item = (Var, M)>,
        export: impl Fn(&L, Option<&L>, &L::Edge) -> Option<M>,
    ) -> Solver<M> {
        let mut replay = Solver::with_classes(self.parent.len());
        for (var, evidence) in facts {
            replay.expect(var, &evidence);
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
        fn grows((): &()) -> bool {
            false
        }

        fn carries((): &(), _: bool) -> bool {
            true
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

        fn carries(_: &i64, _: bool) -> bool {
            true
        }

        fn grows(offset: &i64) -> bool {
            *offset != 0
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

    /// Three classes, and an edge of two words: no edge carries where it
    /// came from, since the graph knows.
    #[test]
    fn a_flow_is_six_words() {
        assert_eq!(size_of::<Option<Var>>(), 4);
        assert_eq!(
            size_of::<Flow<(crate::typing::Edge, crate::ranges::RangeEdge)>>(),
            24
        );
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

        fn grows((): &()) -> bool {
            true
        }

        fn carries((): &(), _: bool) -> bool {
            true
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

        fn carries(edge: &HullEdge, _: bool) -> bool {
            !matches!(edge, HullEdge::Inert)
        }

        fn grows(edge: &HullEdge) -> bool {
            matches!(edge, HullEdge::Add(k) if *k != 0)
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
            let mut solver = Solver::<Hull>::default();
            let x = solver.known(Hull { lo: 0, hi: 0 });
            let capped = solver.fresh();
            let stepped = solver.fresh();
            let downstream = solver.fresh();
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
        let mut solver = Solver::<Hull>::default();
        let x = solver.known(Hull { lo: 0, hi: 0 });
        let stepped = solver.import(x, HullEdge::Add(1));
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
        let mut solver = Solver::<Hull>::default();
        let seed = solver.known(Hull { lo: 4, hi: 9 });
        let passed = solver.import(seed, HullEdge::Add(0));
        solver.flow(passed, seed, HullEdge::Inert);
        let x = solver.known(Hull { lo: 0, hi: 0 });
        let capped = solver.import(x, HullEdge::Cap(100));
        let stepped = solver.import(capped, HullEdge::Add(7));
        solver.flow(stepped, x, HullEdge::Add(0));
        let first = solver.import(x, HullEdge::Add(0));
        let second = solver.import(first, HullEdge::Add(0));
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
        let replay = solver.replay([(x, Interval::new(0, 10))], |band, _, offset| {
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

    /// A replay starts from the facts its caller restates and what the
    /// settled flows export, and from nothing else: a demand joined into a
    /// class before the solve is gone, a fact beside it stays, and an
    /// export lands on it whatever the class held.
    #[test]
    fn replay_keeps_restated_facts_and_exported_flows_only() {
        let mut solver = Solver::<Set>::default();
        let known = solver.known(Set(1));
        solver.expect(known, &Set(2));
        let demanded = solver.fresh();
        solver.expect(demanded, &Set(2));
        let conflicted = solver.fresh();
        solver.expect(conflicted, &Set(1));
        solver.expect(conflicted, &Set(2));
        let from_conflict = solver.import(conflicted, ());
        let provider = solver.known(Set(4));
        solver.flow(provider, known, ());
        solver.solve(&());
        assert_eq!(*solver.evidence(known), Set(7));
        let replay = solver.replay([(known, Set(1)), (provider, Set(4))], |set, _, ()| {
            (set.0.count_ones() == 1).then_some(*set)
        });
        assert_eq!(*replay.evidence(known), Set(5));
        assert_eq!(*replay.evidence(provider), Set(4));
        assert_eq!(*replay.evidence(demanded), Set::bottom());
        assert_eq!(*replay.evidence(conflicted), Set::bottom());
        assert_eq!(*replay.evidence(from_conflict), Set::bottom());
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
