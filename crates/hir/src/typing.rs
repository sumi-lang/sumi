//! Scalar type evidence with provenance, over the lattice-join [`Solver`].
//!
//! Every expression, local, and function result owns a class. The evidence on
//! a class is the set of types claimed for it, each with the best claim that
//! made it, so a conflicted class explains itself: which types, and where
//! each came from. A call is a flow from the callee's result class into the
//! call expression's class, and the evidence crossing it is relabeled to the
//! call site, so no origin ever points outside the declaration that owns the
//! class. A conflict whose every claim arrived through a flow is inherited:
//! it was already a conflict where it arose, and is reported there, once. A
//! class with a claim of its own in the conflict reports it.
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

/// The evidence on a class: for each scalar type, the best claim that the
/// class has it. No claim is unresolved, one is solved, and more than one is
/// a conflict, kept rather than retracted so its report can name every side.
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
    type Edge = Claim;

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

    /// Crossing a call: the same types, all claimed at the call site.
    fn transfer(&self, call: &Claim) -> Self {
        let imported = Claim(call.0 | IMPORTED);
        Self {
            claims: self.claims.map(|claim| claim.map(|_| imported)),
        }
    }
}

/// What a demand asks of an expression: a fixed type, or the type of another
/// class.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Expected {
    Ty(Ty),
    Class(Var),
}

#[derive(Default)]
pub(crate) struct Typing {
    solver: Solver<Evidence>,
    /// The node each claim was made at, by claim index.
    origins: Vec<NodeIdx>,
}

impl Typing {
    /// A typing sized for a tree of `nodes` nodes: about a class per two
    /// nodes, a claim per node, and a call per eight, so the common file
    /// fills its vectors without growing them. Only a guide.
    pub fn for_nodes(nodes: usize) -> Self {
        Self {
            solver: Solver::with_capacity(nodes / 2, nodes / 8),
            origins: Vec::with_capacity(nodes),
        }
    }

    fn claim(&mut self, node: NodeIdx) -> Claim {
        let claim = Claim::local(self.origins.len());
        self.origins.push(node);
        claim
    }

    /// The node `claim` was made at.
    pub fn origin(&self, claim: Claim) -> NodeIdx {
        self.origins[claim.index()]
    }

    /// A class nothing is known about yet.
    pub fn fresh(&mut self) -> Var {
        self.solver.fresh()
    }

    /// A class known to have `ty` because of `node`: a literal, an
    /// annotation, or an operator's result.
    pub fn known(&mut self, ty: Ty, node: NodeIdx) -> Var {
        let claim = self.claim(node);
        self.solver.known(Evidence::single(ty, claim))
    }

    /// The class of the call at `node` whose callee's result class is
    /// `result`.
    pub fn call(&mut self, result: Var, node: NodeIdx) -> Var {
        let claim = self.claim(node);
        self.solver.import(result, claim)
    }

    /// The use at `node` demands that `var` be `expected`.
    pub fn expect(&mut self, var: Var, expected: Expected, node: NodeIdx) {
        match expected {
            Expected::Ty(ty) => {
                let claim = self.claim(node);
                self.solver.expect(var, &Evidence::single(ty, claim));
            }
            Expected::Class(class) => self.solver.equal(var, class),
        }
    }

    pub fn evidence(&self, var: Var) -> &Evidence {
        self.solver.evidence(var)
    }

    pub fn resolve(&self, var: Var) -> Option<Ty> {
        self.evidence(var).ty()
    }

    /// Settle every call flow. Signatures can be read off result classes
    /// after this, in any declaration order.
    pub fn solve(&mut self) {
        self.solver.solve();
    }

    /// The same classes carrying only what is known on their own account:
    /// facts, and the calls whose callee result is solved. Replaying demands
    /// on it one at a time, in source order, blames a disagreement on the
    /// first demand that raised it. An unresolved or conflicted callee
    /// delivers nothing: it is reported at its declaration.
    pub fn replay(&self) -> Replay {
        Replay(
            self.solver
                .replay(|evidence, call| evidence.ty().is_some().then(|| evidence.transfer(call))),
        )
    }
}

/// A [`Typing::replay`]: the classes again, to be handed the demands in
/// order. Only what each class resolves to is read off it, never a claim.
pub(crate) struct Replay(Solver<Evidence>);

impl Replay {
    pub fn resolve(&self, var: Var) -> Option<Ty> {
        self.0.evidence(var).ty()
    }

    /// One demand, replayed.
    pub fn expect(&mut self, var: Var, expected: Expected) {
        match expected {
            Expected::Ty(ty) => self.0.expect(var, &Evidence::single(ty, Claim::REPLAYED)),
            Expected::Class(class) => self.0.equal(var, class),
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

    #[test]
    fn evidence_is_three_words() {
        assert_eq!(size_of::<Evidence>(), 12);
        assert_eq!(size_of::<Option<Claim>>(), 4);
    }

    #[test]
    fn calls_never_export_consumer_demands() {
        let mut typing = typing();
        let provider = typing.fresh();
        let call = typing.call(provider, at(0));
        typing.expect(call, Expected::Ty(Ty::Int), at(1));
        typing.solve();
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
            let downstream = typing.call(result, at(30));
            typing.solve();
            let evidence = typing.evidence(result);
            assert!(evidence.is_conflict() && !evidence.inherited());
            let claims = evidence.claims();
            assert_eq!(claims.len(), 2);
            assert_eq!(claims[0].0, types[0].0);
            assert_eq!(typing.origin(claims[0].1), at(types[0].1));
            assert_eq!(typing.origin(claims[1].1), at(types[1].1));
            let downstream = typing.evidence(downstream);
            assert!(downstream.is_conflict() && downstream.inherited());
            assert!(
                downstream
                    .claims()
                    .iter()
                    .all(|(_, c)| typing.origin(*c) == at(30))
            );
        }
    }

    #[test]
    fn a_claim_of_the_classs_own_makes_a_conflict_local() {
        let mut typing = typing();
        let conflicted = typing.known(Ty::Int, at(0));
        typing.expect(conflicted, Expected::Ty(Ty::Bool), at(1));
        let call = typing.call(conflicted, at(2));
        typing.expect(call, Expected::Ty(Ty::Unit), at(3));
        typing.solve();
        let evidence = typing.evidence(call);
        assert!(evidence.is_conflict() && !evidence.inherited());
        let claims = evidence.claims();
        assert_eq!(claims.len(), 3);
        assert_eq!((claims[0].0, typing.origin(claims[0].1)), (Ty::Unit, at(3)));
        assert!(
            claims[1..]
                .iter()
                .all(|(_, claim)| typing.origin(*claim) == at(2))
        );
    }

    #[test]
    fn a_local_claim_outranks_an_earlier_imported_one() {
        let mut typing = typing();
        let provider = typing.known(Ty::Int, at(0));
        let call = typing.call(provider, at(1));
        typing.expect(call, Expected::Ty(Ty::Int), at(2));
        typing.solve();
        assert_eq!(typing.origin(typing.evidence(call).claims()[0].1), at(2));
    }

    #[test]
    fn replay_keeps_facts_and_solved_calls_only() {
        let mut typing = typing();
        let literal = typing.known(Ty::Int, at(0));
        let demanded = typing.fresh();
        typing.expect(demanded, Expected::Ty(Ty::Bool), at(1));
        let unknown = typing.fresh();
        let unknown_call = typing.call(unknown, at(2));
        let conflict = typing.fresh();
        typing.expect(conflict, Expected::Ty(Ty::Bool), at(3));
        typing.expect(conflict, Expected::Ty(Ty::Unit), at(4));
        let conflict_call = typing.call(conflict, at(5));
        let literal_call = typing.call(literal, at(6));
        typing.solve();
        let mut replay = typing.replay();
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
