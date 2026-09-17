//! Scalar type evidence with provenance, and the may-values beside it, over
//! the lattice-join [`Solver`].
//!
//! Every expression, local, and function result owns a class. The evidence
//! on a class is a pair: the set of types claimed for it, each with the best
//! claim that made it, so a conflicted class explains itself, and the
//! [`May`] set of values that reach it, which `ranges` defines. A call is a
//! flow from the callee's result class into the call expression's class,
//! and the type claims crossing it are relabeled to the call site, so no
//! origin ever points outside the declaration that owns the class. A
//! conflict whose every claim arrived through a call is inherited: it was
//! already a conflict where it arose, and is reported there, once. A class
//! with a claim of its own in the conflict reports it.
//!
//! An `if` with an else owns a class its branches flow into, unchanged, and
//! never unify with. Branches that disagree make a conflict on the `if`
//! alone, reported there with each branch's origin; the branches keep their
//! own types, and whatever takes the `if`'s type resolves to nothing rather
//! than to whichever branch came first.
//!
//! A claim on a class is one word: its rank, which is also its identity. The
//! node it was made at lives in a table on the [`Typing`], consulted only
//! when a conflict is reported, so making a claim never computes a span and
//! joining or transferring evidence never touches memory beyond the class.
//!
//! Equality is local to a declaration; flows never unify caller and callee,
//! so a caller's demands never decide a callee's result. Signatures are read
//! off result classes after one solve, and depend on no declaration order.
//! Only concrete types cross into public HIR. Structural types will need a
//! structural lattice in place of [`Evidence`], partial types with holes
//! joined by unification with an occurs check, and nothing else here changes.

use std::num::NonZeroU32;

use sumi_syntax::NodeIdx;

use crate::Ty;
use crate::ranges::{May, RangeEdge, Thresholds};
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

    fn transfer(&self, edge: &Edge, _: Option<&Self>, _: bool, (): &()) -> Self {
        match *edge {
            Edge::Branch | Edge::Peer => *self,
            Edge::Call(call) => {
                let imported = Claim(call.0 | IMPORTED);
                Self {
                    claims: self.claims.map(|claim| claim.map(|_| imported)),
                }
            }
            Edge::None => Self::bottom(),
        }
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
    /// Nothing: the typing side of a range-only flow.
    None,
}

/// What a demand asks of an expression: a fixed type, the type of another
/// class it is one value with, or the type of a peer it is compared to.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Expected {
    Ty(Ty),
    /// The same value as `Class`: the classes merge, values included.
    Class(Var),
    /// Compared with `Peer`: each learns the other's types and nothing of
    /// its values.
    Peer(Var),
}

pub(crate) type Product = (Evidence, May);
pub(crate) type ProductContext = ((), Thresholds);

#[derive(Default)]
pub(crate) struct Typing {
    solver: Solver<Product>,
    /// The node each claim was made at, by claim index.
    origins: Vec<NodeIdx>,
}

impl Typing {
    /// A typing sized for a tree of `nodes` nodes: about a class per two
    /// nodes, a claim per node, and a flow per node, so the common file
    /// fills its vectors without growing them. Only a guide.
    pub fn for_nodes(nodes: usize) -> Self {
        Self {
            solver: Solver::with_capacity(nodes / 2, nodes),
            origins: Vec::with_capacity(nodes),
        }
    }

    fn claim(&mut self, node: NodeIdx) -> Claim {
        let claim = Claim::local(self.origins.len());
        self.origins.push(node);
        claim
    }

    /// The node `claim` was made at; none for a replay's own claims.
    pub fn origin(&self, claim: Claim) -> Option<NodeIdx> {
        self.origins.get(claim.index()).copied()
    }

    /// A class nothing is known about yet.
    pub fn fresh(&mut self) -> Var {
        self.solver.fresh()
    }

    /// A class known to have `ty` because of `node`: an annotation, or an
    /// operator's result, whose values arrive by flows.
    pub fn known(&mut self, ty: Ty, node: NodeIdx) -> Var {
        let claim = self.claim(node);
        self.solver
            .known((Evidence::single(ty, claim), May::bottom()))
    }

    /// A class known to be unit because of `node`, a block without a tail
    /// or an `if` without an else, whose one value it holds while
    /// `context` is live.
    pub fn unit(&mut self, context: Var, node: NodeIdx) -> Var {
        let class = self.known(Ty::Unit, node);
        self.solver
            .flow(context, class, (Edge::None, RangeEdge::Enter));
        class
    }

    /// A literal: known to have `ty` and to be exactly `value`.
    pub fn literal(&mut self, ty: Ty, value: May, node: NodeIdx) -> Var {
        let claim = self.claim(node);
        self.solver.known((Evidence::single(ty, claim), value))
    }

    /// A function's entry context: live on its own account when the function
    /// can be run without arguments, otherwise live when a call site is.
    pub fn entry(&mut self, runnable: bool) -> Var {
        if runnable {
            self.solver.known((Evidence::bottom(), May::unit()))
        } else {
            self.solver.fresh()
        }
    }

    /// The class of the call at `node` whose callee's result class is
    /// `result`.
    pub fn call(&mut self, result: Var, node: NodeIdx) -> Var {
        let claim = self.claim(node);
        self.solver
            .import(result, (Edge::Call(claim), RangeEdge::Call))
    }

    /// Let `branch` decide `join`, the class of the `if` it is one arm of,
    /// without learning anything from the other arm, and only while
    /// `context`, the branch's own, is live.
    pub fn branch(&mut self, branch: Var, context: Var, join: Var) {
        self.solver
            .derive(branch, context, join, (Edge::Branch, RangeEdge::Branch));
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

    /// A fresh class deriving its values from `first` and `second`.
    pub fn derived(&mut self, first: Var, second: Var, edge: RangeEdge) -> Var {
        let consumer = self.solver.fresh();
        self.derive(first, second, consumer, edge);
        consumer
    }

    /// The use at `node` demands that `var` be `expected`.
    pub fn expect(&mut self, var: Var, expected: Expected, node: NodeIdx) {
        match expected {
            Expected::Ty(ty) => {
                let claim = self.claim(node);
                self.solver
                    .expect(var, &(Evidence::single(ty, claim), May::bottom()));
            }
            Expected::Class(class) => self.solver.equal(var, class),
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

    /// The same classes carrying only what is known on their own account:
    /// facts, and the calls whose callee result is solved. Replaying demands
    /// on it one at a time, in source order, blames a disagreement on the
    /// first demand that raised it. An unresolved or conflicted callee
    /// delivers nothing: it is reported at its declaration. A branch is
    /// settled by [`Replay::branch`] when its `if` comes up in that order,
    /// since what it delivers is shaped by the demands before it.
    pub fn replay<'a>(&self, cx: &'a ProductContext) -> Replay<'a> {
        Replay {
            solver: self.solver.replay(|solved, other, edge| match edge.0 {
                Edge::Call(_) => solved
                    .0
                    .ty()
                    .is_some()
                    .then(|| solved.transfer(edge, other, false, cx)),
                Edge::Branch | Edge::Peer | Edge::None => None,
            }),
            cx,
        }
    }
}

/// A [`Typing::replay`]: the classes again, to be handed the demands in
/// order. Its own claims record no origin; the claims flows delivered do.
pub(crate) struct Replay<'a> {
    solver: Solver<Product>,
    cx: &'a ProductContext,
}

impl Replay<'_> {
    pub fn evidence(&self, var: Var) -> &Evidence {
        &self.solver.evidence(var).0
    }

    pub fn resolve(&self, var: Var) -> Option<Ty> {
        self.evidence(var).ty()
    }

    /// Settle a branch flow: what `branch` is so far, delivered to `join`,
    /// the class of its `if`, as a solved call is delivered.
    pub fn branch(&mut self, branch: Var, join: Var) {
        let evidence = self.solver.evidence(branch).clone();
        if evidence.0.ty().is_some() {
            let delivered =
                evidence.transfer(&(Edge::Branch, RangeEdge::None), None, false, self.cx);
            self.solver.expect(join, &delivered);
        }
    }

    /// One demand, replayed.
    pub fn expect(&mut self, var: Var, expected: Expected) {
        match expected {
            Expected::Ty(ty) => self
                .solver
                .expect(var, &(Evidence::single(ty, Claim::REPLAYED), May::bottom())),
            Expected::Class(class) | Expected::Peer(class) => self.solver.equal(var, class),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn at(node: u32) -> NodeIdx {
        NodeIdx::new(node)
    }

    fn typing() -> Typing {
        Typing::default()
    }

    fn cx() -> ProductContext {
        ((), Thresholds::default())
    }

    fn call(typing: &mut Typing, result: Var, node: NodeIdx) -> Var {
        typing.call(result, node)
    }

    #[test]
    fn evidence_is_three_words() {
        assert_eq!(size_of::<Evidence>(), 12);
        assert_eq!(size_of::<Option<Claim>>(), 4);
    }

    #[test]
    fn calls_never_export_consumer_demands() {
        let mut typing = typing();
        let provider = typing.fresh();
        let call = call(&mut typing, provider, at(0));
        typing.expect(call, Expected::Ty(Ty::Int), at(1));
        typing.solve(&cx());
        assert_eq!(typing.resolve(provider), None);
        assert_eq!(typing.resolve(call), Some(Ty::Int));
    }

    #[test]
    fn conflicts_keep_their_earliest_origins() {
        for reverse in [false, true] {
            let mut typing = typing();
            let result = typing.fresh();
            let mut types = [(Ty::Int, 10), (Ty::Bool, 20)];
            if reverse {
                types.reverse();
            }
            for (ty, offset) in types {
                let literal = typing.known(ty, at(offset));
                typing.expect(result, Expected::Class(literal), at(offset + 1));
            }
            let downstream = call(&mut typing, result, at(30));
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
        let mut typing = typing();
        let conflicted = typing.known(Ty::Int, at(0));
        typing.expect(conflicted, Expected::Ty(Ty::Bool), at(1));
        let call = call(&mut typing, conflicted, at(2));
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
        let mut typing = typing();
        let provider = typing.known(Ty::Int, at(0));
        let call = call(&mut typing, provider, at(1));
        typing.expect(call, Expected::Ty(Ty::Int), at(2));
        typing.solve(&cx());
        assert_eq!(
            typing.origin(typing.evidence(call).claims()[0].1),
            Some(at(2))
        );
    }

    #[test]
    fn peers_share_types_but_not_values() {
        let mut typing = typing();
        let x = typing.literal(Ty::Int, May::int(5.into()), at(0));
        let y = typing.literal(Ty::Int, May::int(9.into()), at(1));
        typing.expect(x, Expected::Peer(y), at(2));
        typing.solve(&cx());
        assert_eq!(typing.resolve(x), Some(Ty::Int));
        assert_eq!(typing.may(x), &May::int(5.into()));
        assert_eq!(typing.may(y), &May::int(9.into()));
        let unknown = typing.fresh();
        let known = typing.known(Ty::Bool, at(3));
        typing.expect(unknown, Expected::Peer(known), at(4));
        typing.solve(&cx());
        assert_eq!(typing.resolve(unknown), Some(Ty::Bool));
        assert!(!typing.evidence(unknown).is_conflict());
    }

    #[test]
    fn branches_decide_their_if_and_keep_their_origins() {
        let mut typing = typing();
        let live = typing.entry(true);
        let then_branch = typing.known(Ty::Int, at(0));
        let else_branch = typing.known(Ty::Bool, at(1));
        let join = typing.fresh();
        typing.branch(then_branch, live, join);
        typing.branch(else_branch, live, join);
        let call = call(&mut typing, join, at(2));
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
        let mut replay = typing.replay(&cx);
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
        let mut typing = typing();
        let dead = typing.entry(false);
        let live = typing.entry(true);
        let then_branch = typing.literal(Ty::Int, May::int(1.into()), at(0));
        let else_branch = typing.literal(Ty::Int, May::int(2.into()), at(1));
        let join = typing.fresh();
        typing.branch(then_branch, dead, join);
        typing.branch(else_branch, live, join);
        typing.solve(&cx());
        // The type still arrives from both arms; the value from the live one.
        assert_eq!(typing.resolve(join), Some(Ty::Int));
        assert_eq!(typing.may(join), &May::int(2.into()));
    }

    #[test]
    fn replay_keeps_facts_and_solved_calls_only() {
        let mut typing = typing();
        let literal = typing.known(Ty::Int, at(0));
        let demanded = typing.fresh();
        typing.expect(demanded, Expected::Ty(Ty::Bool), at(1));
        let unknown = typing.fresh();
        let unknown_call = call(&mut typing, unknown, at(2));
        let conflict = typing.fresh();
        typing.expect(conflict, Expected::Ty(Ty::Bool), at(3));
        typing.expect(conflict, Expected::Ty(Ty::Unit), at(4));
        let conflict_call = call(&mut typing, conflict, at(5));
        let literal_call = call(&mut typing, literal, at(6));
        let cx = cx();
        typing.solve(&cx);
        let mut replay = typing.replay(&cx);
        assert_eq!(replay.resolve(literal), Some(Ty::Int));
        assert_eq!(replay.resolve(demanded), None);
        assert_eq!(replay.resolve(unknown_call), None);
        assert_eq!(replay.resolve(conflict_call), None);
        assert_eq!(replay.resolve(literal_call), Some(Ty::Int));
        replay.expect(demanded, Expected::Class(literal));
        assert_eq!(replay.resolve(demanded), Some(Ty::Int));
        replay.expect(unknown_call, Expected::Ty(Ty::Bool));
        assert_eq!(replay.resolve(unknown_call), Some(Ty::Bool));
    }
}
