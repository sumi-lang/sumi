//! The checker's instance of the [`Solver`]: a class for every node of the
//! graph, the one at its index, carrying the [`Product`] of its type
//! claims and may-values.
//!
//! Nothing the checker draws merges two classes: what the solve decides of
//! a node is read back at the node. Equality is local to a declaration;
//! flows never unify caller and callee, so a caller's demands never decide
//! a callee's result, and signatures are read off result classes after one
//! solve, in any declaration order.
//!
//! The typing keeps what the solver does not: where each claim was made,
//! which claims were facts rather than demands, and which classes are one
//! in the [`Replay`], where demands are checked one at a time against the
//! settled flows so a disagreement is blamed on the first demand that
//! raised it.

use sumi_text::TextRange;

use sumi_graph::{Domain, May, NodeId, Thresholds, Ty};

use crate::lattice::{Claim, Edge, Evidence, Product};
use crate::solver::Solver;

/// What a demand asks of an expression: a fixed type, or the type of a
/// peer it is compared to.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Expected {
    Ty(Ty),
    /// Compared with `Peer`: each learns the other's types and nothing of
    /// its values.
    Peer(NodeId),
}

pub(crate) struct Typing {
    solver: Solver<Product>,
    /// Where each claim was made, by claim index.
    origins: Vec<TextRange>,
    /// Every type claimed on a class's own account, with the claim that
    /// made it: what the replay starts from, restated to it since the
    /// solver keeps no record of which evidence was a fact.
    facts: Vec<(NodeId, Ty, Claim)>,
    /// Every class that is one with another in the replay, beside that
    /// other: the consumer of each aliasing edge beside its provider. The
    /// replay resolves types alone, so a demand on the read or the
    /// binding is a demand on the local or the initializer wherever its
    /// type comes from, a branch settled later included.
    aliased: Vec<(NodeId, NodeId)>,
}

impl Typing {
    /// A typing of `nodes` classes, one per node at the node's index, with
    /// room for about a claim, a fact, and a flow per class.
    pub fn for_nodes(nodes: usize) -> Self {
        Self {
            solver: Solver::with_classes(nodes),
            origins: Vec::with_capacity(nodes),
            facts: Vec::with_capacity(nodes),
            aliased: Vec::with_capacity(nodes / 8),
        }
    }

    fn claim(&mut self, origin: TextRange) -> Claim {
        let claim = Claim::local(self.origins.len());
        self.origins.push(origin);
        claim
    }

    /// Where `claim` was made; none for a replay's own claims.
    pub fn origin(&self, claim: Claim) -> Option<TextRange> {
        self.origins.get(claim.index()).copied()
    }

    /// `node` is known to have `ty` because of what is at `origin`: an
    /// annotation, or an operator's result, whose values arrive by flows.
    pub fn known(&mut self, node: NodeId, ty: Ty, origin: TextRange) {
        self.fact(node, ty, May::NONE, origin);
    }

    /// `node` is a literal: known to have `ty` and to be exactly `value`.
    pub fn literal(&mut self, node: NodeId, ty: Ty, value: May, origin: TextRange) {
        self.fact(node, ty, value, origin);
    }

    /// What `node` is on its own account: a claim of `ty` made at `origin`,
    /// which survives a replay, and its own values.
    fn fact(&mut self, node: NodeId, ty: Ty, value: May, origin: TextRange) {
        let claim = self.claim(origin);
        self.solver.expect(
            node,
            &Product {
                types: Evidence::single(ty, claim),
                values: value,
            },
        );
        self.facts.push((node, ty, claim));
    }

    /// `node` is a function's entry context: live on its own account when
    /// the function can be run without arguments, otherwise live when a
    /// call site is. Liveness is not a type claim, so no replay reads it.
    pub fn entry(&mut self, node: NodeId, runnable: bool) {
        if runnable {
            self.solver.expect(
                node,
                &Product {
                    types: Evidence::NONE,
                    values: May::unit(),
                },
            );
        }
    }

    /// Let `call`, the class of a call at `origin`, learn its callee's
    /// `result`: the same types, all claimed at the call site.
    pub fn call(&mut self, result: NodeId, call: NodeId, origin: TextRange) {
        let claim = self.claim(origin);
        self.flow(result, call, Edge::Call(claim));
    }

    /// Let everything `provider` learns reach `consumer` through `edge`,
    /// and nothing travel back.
    pub fn flow(&mut self, provider: NodeId, consumer: NodeId, edge: Edge) {
        self.solver.flow(provider, consumer, edge);
        if edge.aliases() {
            self.aliased.push((consumer, provider));
        }
    }

    /// Let `consumer` learn the transfer of `first` and `second` through
    /// `edge`, recomputed whenever either grows.
    pub fn derive(&mut self, first: NodeId, second: NodeId, consumer: NodeId, edge: Edge) {
        self.solver.derive(first, second, consumer, edge);
        if edge.aliases() {
            self.aliased.push((consumer, first));
        }
    }

    /// The use at `origin` demands that `node` be `expected`.
    pub fn expect(&mut self, node: NodeId, expected: Expected, origin: TextRange) {
        match expected {
            Expected::Ty(ty) => {
                let claim = self.claim(origin);
                self.solver.expect(
                    node,
                    &Product {
                        types: Evidence::single(ty, claim),
                        values: May::NONE,
                    },
                );
            }
            Expected::Peer(peer) => {
                self.solver.flow(node, peer, Edge::Peer);
                self.solver.flow(peer, node, Edge::Peer);
            }
        }
    }

    pub fn evidence(&self, node: NodeId) -> &Evidence {
        &self.solver.evidence(node).types
    }

    pub fn may(&self, node: NodeId) -> &May {
        &self.solver.evidence(node).values
    }

    pub fn resolve(&self, node: NodeId) -> Option<Ty> {
        self.evidence(node).ty()
    }

    /// Settle every flow. Signatures can be read off result classes after
    /// this, in any declaration order.
    pub fn solve(&mut self, thresholds: &Thresholds) {
        self.solver.solve(thresholds);
    }

    /// The same classes carrying only the types known on their own account:
    /// the facts, restated, and the calls whose callee result is solved,
    /// with each aliased class one with the class it aliases. An unresolved
    /// or conflicted callee delivers nothing: it is reported at its
    /// declaration. A branch is settled by [`Replay::branch`] when its `if`
    /// comes up among the demands.
    pub fn replay(&self) -> Replay {
        let mut replay = Replay::new(self.solver.classes());
        for &(node, ty, claim) in &self.facts {
            replay.learn(node, &Evidence::single(ty, claim));
        }
        for (call, edge, solved) in self.solver.flows() {
            if let Edge::Call(claim) = *edge
                && solved.types.ty().is_some()
            {
                replay.learn(call, &solved.types.imported(claim));
            }
        }
        for &(alias, of) in &self.aliased {
            replay.union(alias, of);
        }
        replay
    }

    /// What the solve decided of every class, and nothing else: the flows,
    /// facts, claim origins, and aliases are done with once the verdicts
    /// are given.
    pub fn settle(self) -> Settled {
        Settled(self.solver.into_evidence().into_boxed_slice())
    }
}

/// The evidence of every class once the flows are settled and the
/// verdicts given, by class index.
pub(crate) struct Settled(Box<[Product]>);

impl Settled {
    pub fn resolve(&self, node: NodeId) -> Option<Ty> {
        self.0[node.index()].types.ty()
    }

    pub fn may(&self, node: NodeId) -> &May {
        &self.0[node.index()].values
    }
}

/// A [`Typing::replay`]: the classes again, carrying type evidence alone
/// over a union-find, so an aliased class or a peer reads and takes the
/// evidence of the class it is one with. Handed the demands one at a
/// time, in node order, it blames a disagreement on the first demand
/// that raised it, with the flows final rather than provisional. Its own
/// claims record no origin; the claims flows delivered do.
pub(crate) struct Replay {
    /// Each class's parent; a root is its own.
    parent: Vec<u32>,
    /// How many classes a root is one with, itself included; meaningful
    /// at roots only, as is the evidence.
    size: Vec<u32>,
    evidence: Vec<Evidence>,
}

impl Replay {
    fn new(classes: usize) -> Self {
        Self {
            parent: (0..classes as u32).collect(),
            size: vec![1; classes],
            evidence: vec![Evidence::NONE; classes],
        }
    }

    fn root(&self, node: NodeId) -> usize {
        let mut id = node.index();
        while self.parent[id] as usize != id {
            id = self.parent[id] as usize;
        }
        id
    }

    fn learn(&mut self, node: NodeId, evidence: &Evidence) {
        let root = self.root(node);
        self.evidence[root].join(evidence);
    }

    /// Make `a` and `b` one class, joining their evidence. The smaller
    /// class goes under the larger root, so no chain outgrows the
    /// logarithm of the class count however many reads alias one local.
    fn union(&mut self, a: NodeId, b: NodeId) {
        let (a, b) = (self.root(a), self.root(b));
        if a == b {
            return;
        }
        let (root, absorbed) = if self.size[a] >= self.size[b] {
            (a, b)
        } else {
            (b, a)
        };
        self.parent[absorbed] = root as u32;
        self.size[root] += self.size[absorbed];
        let evidence = std::mem::replace(&mut self.evidence[absorbed], Evidence::NONE);
        self.evidence[root].join(&evidence);
    }

    pub fn evidence(&self, node: NodeId) -> &Evidence {
        &self.evidence[self.root(node)]
    }

    pub fn resolve(&self, node: NodeId) -> Option<Ty> {
        self.evidence(node).ty()
    }

    /// Settle a branch flow: what `branch` is so far, delivered to `join`,
    /// the class of its `if`, as a solved call is delivered.
    pub fn branch(&mut self, branch: NodeId, join: NodeId) {
        let evidence = *self.evidence(branch);
        if evidence.ty().is_some() {
            self.learn(join, &evidence);
        }
    }

    /// One demand, replayed.
    pub fn expect(&mut self, node: NodeId, expected: Expected) {
        match expected {
            Expected::Ty(ty) => self.learn(node, &Evidence::single(ty, Claim::REPLAYED)),
            Expected::Peer(peer) => self.union(node, peer),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn at(offset: u32) -> TextRange {
        use sumi_text::TextSize;
        TextRange::new(TextSize::new(offset), TextSize::new(offset + 1))
    }

    /// A typing of `N` classes nothing is known about yet, by index.
    fn classes<const N: usize>() -> (Typing, [NodeId; N]) {
        (Typing::for_nodes(N), std::array::from_fn(NodeId::new))
    }

    fn cx() -> Thresholds {
        Thresholds::default()
    }

    /// A fact restated to the replay is three words.
    #[test]
    fn a_fact_is_three_words() {
        assert_eq!(size_of::<(NodeId, Ty, Claim)>(), 12);
    }

    #[test]
    fn calls_never_export_consumer_demands() {
        let (mut typing, [provider, call]) = classes();
        typing.call(provider, call, at(0));
        typing.expect(call, Expected::Ty(Ty::Int), at(1));
        typing.solve(&cx());
        assert_eq!(typing.resolve(provider), None);
        assert_eq!(typing.resolve(call), Some(Ty::Int));
    }

    #[test]
    fn conflicts_keep_their_earliest_origins() {
        for reverse in [false, true] {
            let (mut typing, [result, downstream, first, second]) = classes();
            let mut types = [(Ty::Int, 10), (Ty::Bool, 20)];
            if reverse {
                types.reverse();
            }
            for (literal, (ty, offset)) in [first, second].into_iter().zip(types) {
                typing.known(literal, ty, at(offset));
                typing.flow(literal, result, Edge::Bind);
            }
            typing.call(result, downstream, at(30));
            typing.solve(&cx());
            let evidence = typing.evidence(result);
            assert!(evidence.is_conflict() && !evidence.inherited());
            let claims = evidence.claims();
            assert_eq!(claims.len(), 2);
            assert_eq!(claims[0].0, types[0].0);
            assert_eq!(typing.origin(claims[0].1), Some(at(types[0].1)));
            assert_eq!(typing.origin(claims[1].1), Some(at(types[1].1)));
            let downstream = typing.evidence(downstream);
            assert!(downstream.is_conflict() && downstream.inherited());
            assert!(
                downstream
                    .claims()
                    .iter()
                    .all(|(_, c)| typing.origin(*c) == Some(at(30)))
            );
        }
    }

    #[test]
    fn a_claim_of_the_classs_own_makes_a_conflict_local() {
        let (mut typing, [conflicted, call]) = classes();
        typing.known(conflicted, Ty::Int, at(0));
        typing.expect(conflicted, Expected::Ty(Ty::Bool), at(1));
        typing.call(conflicted, call, at(2));
        typing.expect(call, Expected::Ty(Ty::Unit), at(3));
        typing.solve(&cx());
        let evidence = typing.evidence(call);
        assert!(evidence.is_conflict() && !evidence.inherited());
        let claims = evidence.claims();
        assert_eq!(claims.len(), 3);
        assert_eq!(
            (claims[0].0, typing.origin(claims[0].1)),
            (Ty::Unit, Some(at(3)))
        );
        assert!(
            claims[1..]
                .iter()
                .all(|(_, claim)| typing.origin(*claim) == Some(at(2)))
        );
    }

    #[test]
    fn a_local_claim_outranks_an_earlier_imported_one() {
        let (mut typing, [provider, call]) = classes();
        typing.known(provider, Ty::Int, at(0));
        typing.call(provider, call, at(1));
        typing.expect(call, Expected::Ty(Ty::Int), at(2));
        typing.solve(&cx());
        assert_eq!(
            typing.origin(typing.evidence(call).claims()[0].1),
            Some(at(2))
        );
    }

    #[test]
    fn peers_share_types_but_not_values() {
        let (mut typing, [x, y, unknown, known]) = classes();
        typing.literal(x, Ty::Int, May::int(&5.into()), at(0));
        typing.literal(y, Ty::Int, May::int(&9.into()), at(1));
        typing.expect(x, Expected::Peer(y), at(2));
        typing.solve(&cx());
        assert_eq!(typing.resolve(x), Some(Ty::Int));
        assert_eq!(typing.may(x), &May::int(&5.into()));
        assert_eq!(typing.may(y), &May::int(&9.into()));
        typing.known(known, Ty::Bool, at(3));
        typing.expect(unknown, Expected::Peer(known), at(4));
        typing.solve(&cx());
        assert_eq!(typing.resolve(unknown), Some(Ty::Bool));
        assert!(!typing.evidence(unknown).is_conflict());
    }

    #[test]
    fn branches_decide_their_if_and_keep_their_origins() {
        let (mut typing, [live, then_branch, else_branch, join, call]) = classes();
        typing.entry(live, true);
        typing.known(then_branch, Ty::Int, at(0));
        typing.known(else_branch, Ty::Bool, at(1));
        typing.derive(then_branch, live, join, Edge::Branch);
        typing.derive(else_branch, live, join, Edge::Branch);
        typing.call(join, call, at(2));
        let cx = cx();
        typing.solve(&cx);
        assert_eq!(typing.resolve(then_branch), Some(Ty::Int));
        assert_eq!(typing.resolve(else_branch), Some(Ty::Bool));
        let evidence = typing.evidence(join);
        assert!(evidence.is_conflict() && !evidence.inherited());
        let origins: Vec<_> = evidence
            .claims()
            .into_iter()
            .map(|(ty, claim)| (ty, typing.origin(claim).unwrap()))
            .collect();
        assert_eq!(origins, [(Ty::Int, at(0)), (Ty::Bool, at(1))]);
        assert!(typing.evidence(call).inherited());
        // A replay settles the branches when asked, from what the branches
        // are in the replay; a demand refused before then does not reach
        // the `if`.
        let mut replay = typing.replay();
        assert_eq!(replay.resolve(join), None);
        assert_eq!(replay.resolve(call), None);
        replay.branch(then_branch, join);
        assert_eq!(replay.resolve(join), Some(Ty::Int));
        replay.branch(else_branch, join);
        assert!(replay.evidence(join).is_conflict());
        assert_eq!(
            replay.evidence(join).claims(),
            typing.evidence(join).claims()
        );
    }

    #[test]
    fn a_dead_branch_delivers_no_values() {
        let (mut typing, [dead, live, then_branch, else_branch, join]) = classes();
        typing.entry(dead, false);
        typing.entry(live, true);
        typing.literal(then_branch, Ty::Int, May::int(&1.into()), at(0));
        typing.literal(else_branch, Ty::Int, May::int(&2.into()), at(1));
        typing.derive(then_branch, dead, join, Edge::Branch);
        typing.derive(else_branch, live, join, Edge::Branch);
        typing.solve(&cx());
        // The type still arrives from both arms; the value from the live one.
        assert_eq!(typing.resolve(join), Some(Ty::Int));
        assert_eq!(typing.may(join), &May::int(&2.into()));
    }

    #[test]
    fn replay_keeps_facts_solved_calls_and_refined_reads_only() {
        let (
            mut typing,
            [
                literal,
                demanded,
                unknown,
                unknown_call,
                conflict,
                conflict_call,
                literal_call,
                refined,
            ],
        ) = classes();
        typing.known(literal, Ty::Int, at(0));
        typing.expect(demanded, Expected::Ty(Ty::Bool), at(1));
        typing.call(unknown, unknown_call, at(2));
        typing.expect(conflict, Expected::Ty(Ty::Bool), at(3));
        typing.expect(conflict, Expected::Ty(Ty::Unit), at(4));
        typing.call(conflict, conflict_call, at(5));
        typing.call(literal, literal_call, at(6));
        typing.flow(literal, refined, Edge::Exactly(true));
        let cx = cx();
        typing.solve(&cx);
        let mut replay = typing.replay();
        assert_eq!(replay.resolve(literal), Some(Ty::Int));
        assert_eq!(replay.resolve(demanded), None);
        assert_eq!(replay.resolve(unknown_call), None);
        assert_eq!(replay.resolve(conflict_call), None);
        assert_eq!(replay.resolve(literal_call), Some(Ty::Int));
        assert_eq!(replay.resolve(refined), Some(Ty::Int));
        replay.expect(demanded, Expected::Peer(literal));
        assert_eq!(replay.resolve(demanded), Some(Ty::Int));
        replay.expect(unknown_call, Expected::Ty(Ty::Bool));
        assert_eq!(replay.resolve(unknown_call), Some(Ty::Bool));
    }

    /// A refined read of a local whose type arrives only when its `if` is
    /// settled in the replay is one class with the local there, so it
    /// resolves once the branches deliver and a demand on it is a demand
    /// on the local.
    #[test]
    fn a_refined_read_of_a_branch_bound_local_resolves_with_its_if() {
        let (mut typing, [live, then_branch, else_branch, local, refined]) = classes();
        typing.entry(live, true);
        typing.known(then_branch, Ty::Int, at(0));
        typing.known(else_branch, Ty::Int, at(1));
        typing.derive(then_branch, live, local, Edge::Branch);
        typing.derive(else_branch, live, local, Edge::Branch);
        typing.flow(local, refined, Edge::Exactly(true));
        typing.solve(&cx());
        let mut replay = typing.replay();
        assert_eq!(replay.resolve(refined), None);
        replay.branch(then_branch, local);
        replay.branch(else_branch, local);
        assert_eq!(replay.resolve(refined), Some(Ty::Int));
        replay.expect(refined, Expected::Ty(Ty::Bool));
        assert!(replay.evidence(refined).is_conflict());
        assert!(replay.evidence(local).is_conflict());
    }

    /// An unannotated `let` is its initializer: the same types and
    /// values in the solve, where the two stay apart, so a demand on the
    /// binding conflicts the binding and not the initializer; and one
    /// class in the replay, so the demand is blamed on the initializer's
    /// type there, a call settled by the replay included.
    #[test]
    fn a_let_copies_its_initializer_and_is_one_with_it_in_the_replay() {
        let (mut typing, [literal, binding, unknown, unknown_call, bound_call]) = classes();
        typing.literal(literal, Ty::Int, May::int(&5.into()), at(0));
        typing.flow(literal, binding, Edge::Bind);
        typing.expect(binding, Expected::Ty(Ty::Bool), at(1));
        typing.call(unknown, unknown_call, at(2));
        typing.flow(unknown_call, bound_call, Edge::Bind);
        typing.solve(&cx());
        assert_eq!(typing.may(binding).ints, typing.may(literal).ints);
        assert!(typing.evidence(binding).is_conflict());
        assert_eq!(typing.resolve(literal), Some(Ty::Int));
        assert_eq!(typing.resolve(bound_call), None);
        let mut replay = typing.replay();
        assert_eq!(replay.resolve(binding), Some(Ty::Int));
        replay.expect(bound_call, Expected::Ty(Ty::Bool));
        assert_eq!(replay.resolve(unknown_call), Some(Ty::Bool));
    }

    /// Every read of one local aliases it, whichever way each union is
    /// stated: the larger class stays the root, so no read ever reaches its
    /// evidence through another read, and a local's type still reaches
    /// every read once it is learned.
    #[test]
    fn reads_aliasing_one_local_stay_one_step_from_its_root() {
        const READS: usize = 1000;
        let mut typing = Typing::for_nodes(READS + 1);
        let local = NodeId::new(0);
        for read in 1..=READS {
            typing.flow(local, NodeId::new(read), Edge::Exactly(true));
        }
        typing.solve(&cx());
        let mut replay = typing.replay();
        let root = replay.root(local);
        for class in 0..=READS {
            let parent = replay.parent[class] as usize;
            assert!(parent == root || parent == class && class == root);
        }
        replay.expect(local, Expected::Ty(Ty::Int));
        assert_eq!(replay.resolve(NodeId::new(READS)), Some(Ty::Int));
    }

    /// Once settled, every class reads back what the solve decided of it.
    #[test]
    fn settled_evidence_is_read_by_class() {
        let (mut typing, [literal, copied, apart]) = classes();
        typing.literal(literal, Ty::Int, May::int(&5.into()), at(0));
        typing.flow(literal, copied, Edge::Bind);
        typing.solve(&cx());
        let settled = typing.settle();
        assert_eq!(settled.resolve(literal), Some(Ty::Int));
        assert_eq!(settled.resolve(copied), Some(Ty::Int));
        assert_eq!(settled.may(copied).ints, settled.may(literal).ints);
        assert_eq!(settled.resolve(apart), None);
        assert!(!settled.may(apart).live());
    }
}
