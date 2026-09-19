//! Scalar type evidence with provenance, and the may-values beside it, over
//! the lattice-join [`Solver`].
//!
//! Every node of the graph owns a class, the one at its index, and nothing
//! the checker draws merges two: what the solve decides of a node is read
//! back at the node. The evidence on a class is a pair: the set of types
//! claimed for it, each with the best claim that made it, so a conflicted
//! class explains itself, and the [`May`] set of values that reach it,
//! which `ranges` defines. A call is a flow from the callee's result class
//! into the call expression's class, and the type claims crossing it are
//! relabeled to the call site, so no origin ever points outside the
//! declaration that owns the class. A conflict whose every claim arrived
//! through a call is inherited: it was already a conflict where it arose,
//! and is reported there, once. A class with a claim of its own in the
//! conflict reports it.
//!
//! An `if` with an else owns a class its branches flow into, unchanged, and
//! never unify with. Branches that disagree make a conflict on the `if`
//! alone, reported there with each branch's origin; the branches keep their
//! own types, and whatever takes the `if`'s type resolves to nothing rather
//! than to whichever branch came first.
//!
//! A claim on a class is one word: its rank, which is also its identity. The
//! span it was made at lives in a table on the [`Typing`], consulted only
//! when a conflict is reported, so joining or transferring evidence never
//! touches memory beyond the class.
//!
//! Equality is local to a declaration; flows never unify caller and callee,
//! so a caller's demands never decide a callee's result. Signatures are read
//! off result classes after one solve, and depend on no declaration order.
//! Only concrete types cross into public HIR. Structural types will need a
//! structural lattice in place of [`Evidence`], partial types with holes
//! joined by unification with an occurs check, and nothing else here changes.

use std::num::NonZeroU32;

use sumi_text::Span;

use sumi_graph::{Domain, May, Thresholds, Ty};

use crate::ranges::RangeEdge;
use crate::solver::{Lattice, Solver, Var};

/// One claim that a class has some type, as its rank: the one-based sequence
/// number of the claim in the walk, under a bit set once the claim has
/// crossed a flow. A claim made on the class itself therefore outranks one
/// delivered by a flow, and an earlier claim outranks a later one. One-based
/// so an absent claim needs no extra word.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct Claim(NonZeroU32);

const IMPORTED: u32 = 1 << 31;

impl Claim {
    /// The claim made `index` claims into the walk.
    fn local(index: usize) -> Self {
        let rank = u32::try_from(index + 1).expect("claim count fits u32");
        assert!(rank < IMPORTED, "claim count fits below the imported bit");
        Self(NonZeroU32::new(rank).unwrap())
    }

    /// The one claim a replay makes: it records no origin, since nothing is
    /// reported from where a replay's evidence came.
    const REPLAYED: Self = Self(NonZeroU32::MAX);

    fn imported(self) -> bool {
        self.0.get() & IMPORTED != 0
    }

    fn index(self) -> usize {
        ((self.0.get() & !IMPORTED) - 1) as usize
    }
}

/// The type evidence on a class: for each scalar type, the best claim that
/// the class has it. No claim is unresolved, one is solved, and more than
/// one is a conflict, kept rather than retracted so its report can name
/// every side.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Evidence {
    claims: [Option<Claim>; Ty::ALL.len()],
}

impl Evidence {
    fn single(ty: Ty, claim: Claim) -> Self {
        let mut evidence = Self::bottom();
        evidence.claims[ty as usize] = Some(claim);
        evidence
    }

    /// The one type claimed, if exactly one is.
    pub fn ty(&self) -> Option<Ty> {
        let mut found = None;
        for (ty, claim) in Ty::ALL.iter().zip(&self.claims) {
            if claim.is_some() {
                if found.is_some() {
                    return None;
                }
                found = Some(*ty);
            }
        }
        found
    }

    pub fn is_conflict(&self) -> bool {
        self.claims.iter().filter(|claim| claim.is_some()).count() > 1
    }

    /// Whether this is a conflict whose every claim arrived through a flow:
    /// it was already a conflict where it came from, and is reported there.
    pub fn inherited(&self) -> bool {
        self.is_conflict() && self.claims.iter().flatten().all(|claim| claim.imported())
    }

    /// Every type claimed and the claim behind it, best first.
    pub fn claims(&self) -> Vec<(Ty, Claim)> {
        let mut claims: Vec<_> = Ty::ALL
            .iter()
            .zip(&self.claims)
            .filter_map(|(ty, claim)| claim.map(|claim| (*ty, claim)))
            .collect();
        claims.sort_by_key(|(_, claim)| *claim);
        claims
    }
}

/// Evidence slots are indexed by discriminant, in the order `Ty::ALL` lists.
const _: () = {
    let mut index = 0;
    while index < Ty::ALL.len() {
        assert!(Ty::ALL[index] as usize == index);
        index += 1;
    }
};

impl Lattice for Evidence {
    type Edge = Edge;
    type Context = ();

    fn bottom() -> Self {
        Self {
            claims: [None; Ty::ALL.len()],
        }
    }

    fn join(&mut self, other: &Self) -> bool {
        let mut grew = false;
        for (mine, theirs) in self.claims.iter_mut().zip(&other.claims) {
            if let Some(claim) = theirs
                && mine.is_none_or(|existing| *claim < existing)
            {
                *mine = Some(*claim);
                grew = true;
            }
        }
        grew
    }

    /// Three claims a class, so no chain of them is long enough to widen.
    fn grows(_: &Edge) -> bool {
        false
    }

    /// Nothing of a type claim climbs: the cycles that matter are the
    /// values', and a peer's or a branch's claims close none.
    fn carries(_: &Edge, _: bool) -> bool {
        false
    }

    fn transfer(&self, edge: &Edge, _: Option<&Self>, _: bool, (): &()) -> Self {
        match *edge {
            Edge::Branch | Edge::Peer | Edge::Refine | Edge::Copy => *self,
            Edge::Call(call) => {
                let imported = Claim(call.0 | IMPORTED);
                Self {
                    claims: self.claims.map(|claim| claim.map(|_| imported)),
                }
            }
            Edge::None => Self::bottom(),
        }
    }

    /// Type claims never widen, so there is nothing to take back.
    fn narrow(&mut self, _: &Self) -> bool {
        false
    }
}

/// What type evidence crosses when it flows into a class.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Edge {
    /// A call, from the callee's result: the same types, all claimed at the
    /// call site.
    Call(Claim),
    /// A branch joining its `if`, within one declaration: the claims as they
    /// are.
    Branch,
    /// One operand of `==` or `!=` telling the other its type: the claims as
    /// they are, each way, while the classes stay apart, since comparing
    /// two values says nothing about their ranges.
    Peer,
    /// A read of a local under a refinement: the local's claims as they
    /// are, exported by a replay once solved, so the read still types.
    Refine,
    /// A `let` without an annotation: its initializer's claims as they
    /// are, and one class with it in the replay, so a demand on a read of
    /// the binding is a demand on what it was bound to. Also the typing
    /// side of a range-only copy.
    Copy,
    /// Nothing: the typing side of a range-only flow.
    None,
}

/// What a demand asks of an expression: a fixed type, or the type of a
/// peer it is compared to.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Expected {
    Ty(Ty),
    /// Compared with `Peer`: each learns the other's types and nothing of
    /// its values.
    Peer(Var),
}

pub(crate) type Product = (Evidence, May);
pub(crate) type ProductContext = ((), Thresholds);

pub(crate) struct Typing {
    solver: Solver<Product>,
    /// Where each claim was made, by claim index.
    origins: Vec<Span>,
    /// Every type claimed on a class's own account, with the claim that
    /// made it: what the replay starts from, restated to it since the
    /// solver keeps no record of which evidence was a fact.
    facts: Vec<(Var, Ty, Claim)>,
    /// Every class that is one with another in the replay, beside that
    /// other: a refined read beside the local it reads, and an
    /// unannotated `let` beside its initializer. The replay resolves
    /// types alone, so a demand on the read or the binding is a demand
    /// on the local or the initializer wherever its type comes from, a
    /// branch settled later included.
    aliased: Vec<(Var, Var)>,
}

impl Typing {
    /// A typing of `nodes` classes, `Var::new(0)` to `Var::new(nodes - 1)`,
    /// with room for about a claim, a fact, and a flow per class: most
    /// nodes make a fact, and the room for those that make none costs
    /// less than growing would. Only the room is a guide.
    pub fn for_nodes(nodes: usize) -> Self {
        Self {
            solver: Solver::with_classes(nodes),
            origins: Vec::with_capacity(nodes),
            facts: Vec::with_capacity(nodes),
            aliased: Vec::with_capacity(nodes / 8),
        }
    }

    fn claim(&mut self, origin: Span) -> Claim {
        let claim = Claim::local(self.origins.len());
        self.origins.push(origin);
        claim
    }

    /// Where `claim` was made; none for a replay's own claims.
    pub fn origin(&self, claim: Claim) -> Option<Span> {
        self.origins.get(claim.index()).copied()
    }

    /// `var` is known to have `ty` because of what is at `origin`: an
    /// annotation, or an operator's result, whose values arrive by flows.
    pub fn known(&mut self, var: Var, ty: Ty, origin: Span) {
        self.fact(var, ty, May::bottom(), origin);
    }

    /// `var` is a literal: known to have `ty` and to be exactly `value`.
    pub fn literal(&mut self, var: Var, ty: Ty, value: May, origin: Span) {
        self.fact(var, ty, value, origin);
    }

    /// What `var` is on its own account: a claim of `ty` made at `origin`,
    /// which survives a replay, and its own values.
    fn fact(&mut self, var: Var, ty: Ty, value: May, origin: Span) {
        let claim = self.claim(origin);
        self.solver
            .expect(var, &(Evidence::single(ty, claim), value));
        self.facts.push((var, ty, claim));
    }

    /// `var` is a function's entry context: live on its own account when
    /// the function can be run without arguments, otherwise live when a
    /// call site is. Liveness is not a type claim, so no replay reads it.
    pub fn entry(&mut self, var: Var, runnable: bool) {
        if runnable {
            self.solver.expect(var, &(Evidence::bottom(), May::unit()));
        }
    }

    /// Let `call`, the class of a call at `origin`, learn its callee's
    /// `result`: the same types, all claimed at the call site.
    pub fn call(&mut self, result: Var, call: Var, origin: Span) {
        let claim = self.claim(origin);
        self.solver
            .flow(result, call, (Edge::Call(claim), RangeEdge::Call));
    }

    /// Let `branch` decide `join`, the class of the `if` it is one arm of,
    /// without learning anything from the other arm, and only while
    /// `context`, the branch's own, is live.
    pub fn branch(&mut self, branch: Var, context: Var, join: Var) {
        self.solver
            .derive(branch, context, join, (Edge::Branch, RangeEdge::Branch));
    }

    /// Let `read`, a read of `local` narrowed by a comparison with
    /// `other`, learn the narrowing; it is one class with `local` in the
    /// replay.
    pub fn refine(&mut self, local: Var, other: Var, read: Var, edge: RangeEdge) {
        self.solver.derive(local, other, read, (Edge::Refine, edge));
        self.aliased.push((read, local));
    }

    /// Let `read`, a read of the boolean `local`, learn it is `value`.
    pub fn refine_bool(&mut self, local: Var, read: Var, value: bool) {
        self.solver
            .flow(local, read, (Edge::Refine, RangeEdge::Exactly(value)));
        self.aliased.push((read, local));
    }

    /// Let `copy`, a `let` without an annotation, be its `initializer`:
    /// the same types and values, and one class with it in the replay.
    pub fn copy(&mut self, initializer: Var, copy: Var) {
        self.solver
            .flow(initializer, copy, (Edge::Copy, RangeEdge::Copy));
        self.aliased.push((copy, initializer));
    }

    /// A range-only flow from one provider.
    pub fn flow(&mut self, provider: Var, consumer: Var, edge: RangeEdge) {
        self.solver.flow(provider, consumer, (Edge::None, edge));
    }

    /// A range-only flow from two providers.
    pub fn derive(&mut self, first: Var, second: Var, consumer: Var, edge: RangeEdge) {
        self.solver
            .derive(first, second, consumer, (Edge::None, edge));
    }

    /// The use at `origin` demands that `var` be `expected`.
    pub fn expect(&mut self, var: Var, expected: Expected, origin: Span) {
        match expected {
            Expected::Ty(ty) => {
                let claim = self.claim(origin);
                self.solver
                    .expect(var, &(Evidence::single(ty, claim), May::bottom()));
            }
            Expected::Peer(peer) => {
                self.solver.flow(var, peer, (Edge::Peer, RangeEdge::None));
                self.solver.flow(peer, var, (Edge::Peer, RangeEdge::None));
            }
        }
    }

    pub fn evidence(&self, var: Var) -> &Evidence {
        &self.solver.evidence(var).0
    }

    pub fn may(&self, var: Var) -> &May {
        &self.solver.evidence(var).1
    }

    pub fn resolve(&self, var: Var) -> Option<Ty> {
        self.evidence(var).ty()
    }

    /// Settle every flow. Signatures can be read off result classes after
    /// this, in any declaration order.
    pub fn solve(&mut self, cx: &ProductContext) {
        self.solver.solve(cx);
    }

    /// The same classes carrying only the types known on their own account:
    /// the facts, restated, and the calls whose callee result is solved,
    /// with each aliased class one with the class it aliases. An unresolved
    /// or conflicted callee delivers nothing: it is reported at its
    /// declaration. A branch is settled by [`Replay::branch`] when its `if`
    /// comes up among the demands.
    pub fn replay(&self) -> Replay {
        let mut replay = Replay::new(self.solver.classes());
        for &(var, ty, claim) in &self.facts {
            replay.learn(var, &Evidence::single(ty, claim));
        }
        for (call, edge, solved) in self.solver.flows() {
            if let Edge::Call(_) = edge.0
                && solved.0.ty().is_some()
            {
                replay.learn(call, &solved.0.transfer(&edge.0, None, false, &()));
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
    pub fn resolve(&self, var: Var) -> Option<Ty> {
        self.0[var.index()].0.ty()
    }

    pub fn may(&self, var: Var) -> &May {
        &self.0[var.index()].1
    }
}

/// A [`Typing::replay`]: the classes again, carrying type evidence alone
/// over a union-find, so an aliased class or a peer reads and takes the
/// evidence of the class it is one with. Handed the demands one at a
/// time, in source order, it blames a disagreement on the first demand
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
            evidence: vec![Evidence::bottom(); classes],
        }
    }

    fn root(&self, var: Var) -> usize {
        let mut id = var.index();
        while self.parent[id] as usize != id {
            id = self.parent[id] as usize;
        }
        id
    }

    fn learn(&mut self, var: Var, evidence: &Evidence) {
        let root = self.root(var);
        self.evidence[root].join(evidence);
    }

    /// Make `a` and `b` one class, joining their evidence. The smaller
    /// class goes under the larger root, so no chain outgrows the
    /// logarithm of the class count however many reads alias one local.
    fn union(&mut self, a: Var, b: Var) {
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
        let evidence = std::mem::replace(&mut self.evidence[absorbed], Evidence::bottom());
        self.evidence[root].join(&evidence);
    }

    pub fn evidence(&self, var: Var) -> &Evidence {
        &self.evidence[self.root(var)]
    }

    pub fn resolve(&self, var: Var) -> Option<Ty> {
        self.evidence(var).ty()
    }

    /// Settle a branch flow: what `branch` is so far, delivered to `join`,
    /// the class of its `if`, as a solved call is delivered.
    pub fn branch(&mut self, branch: Var, join: Var) {
        let evidence = *self.evidence(branch);
        if evidence.ty().is_some() {
            self.learn(join, &evidence.transfer(&Edge::Branch, None, false, &()));
        }
    }

    /// One demand, replayed.
    pub fn expect(&mut self, var: Var, expected: Expected) {
        match expected {
            Expected::Ty(ty) => self.learn(var, &Evidence::single(ty, Claim::REPLAYED)),
            Expected::Peer(peer) => self.union(var, peer),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn at(offset: u32) -> Span {
        use sumi_text::{FileId, TextRange, TextSize};
        Span::new(
            FileId::new(0),
            TextRange::new(TextSize::new(offset), TextSize::new(offset + 1)),
        )
    }

    /// A typing of `N` classes nothing is known about yet, by index.
    fn classes<const N: usize>() -> (Typing, [Var; N]) {
        (Typing::for_nodes(N), std::array::from_fn(Var::new))
    }

    fn cx() -> ProductContext {
        ((), Thresholds::default())
    }

    #[test]
    fn evidence_is_three_words() {
        assert_eq!(size_of::<Evidence>(), 12);
        assert_eq!(size_of::<Option<Claim>>(), 4);
        assert_eq!(size_of::<Option<Var>>(), 4);
        // A fact restated to the replay is three words too.
        assert_eq!(size_of::<(Var, Ty, Claim)>(), 12);
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
                typing.copy(literal, result);
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
        typing.branch(then_branch, live, join);
        typing.branch(else_branch, live, join);
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
        typing.branch(then_branch, dead, join);
        typing.branch(else_branch, live, join);
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
        typing.refine_bool(literal, refined, true);
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
        typing.branch(then_branch, live, local);
        typing.branch(else_branch, live, local);
        typing.refine_bool(local, refined, true);
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
        typing.copy(literal, binding);
        typing.expect(binding, Expected::Ty(Ty::Bool), at(1));
        typing.call(unknown, unknown_call, at(2));
        typing.copy(unknown_call, bound_call);
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
        let local = Var::new(0);
        for read in 1..=READS {
            typing.refine_bool(local, Var::new(read), true);
        }
        typing.solve(&cx());
        let mut replay = typing.replay();
        let root = replay.root(local);
        for class in 0..=READS {
            let parent = replay.parent[class] as usize;
            assert!(parent == root || parent == class && class == root);
        }
        replay.expect(local, Expected::Ty(Ty::Int));
        assert_eq!(replay.resolve(Var::new(READS)), Some(Ty::Int));
    }

    /// Once settled, every class reads back what the solve decided of it.
    #[test]
    fn settled_evidence_is_read_by_class() {
        let (mut typing, [literal, copied, apart]) = classes();
        typing.literal(literal, Ty::Int, May::int(&5.into()), at(0));
        typing.copy(literal, copied);
        typing.solve(&cx());
        let settled = typing.settle();
        assert_eq!(settled.resolve(literal), Some(Ty::Int));
        assert_eq!(settled.resolve(copied), Some(Ty::Int));
        assert_eq!(settled.may(copied).ints, settled.may(literal).ints);
        assert_eq!(settled.resolve(apart), None);
        assert!(!settled.may(apart).live());
    }
}
