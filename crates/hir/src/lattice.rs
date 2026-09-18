//! The evidence on every class of the graph, and what it becomes crossing
//! each kind of flow: the [`Lattice`] the [`Solver`](crate::solver::Solver)
//! carries for the checker.
//!
//! A class holds a [`Product`]: the set of scalar types claimed for it,
//! each with the best claim that made it, so a conflicted class explains
//! itself, and the [`May`] set of values that reach it. A claim is one
//! word, its rank, which is also its identity; the span it was made at
//! lives in a table on the typing, consulted only when a conflict is
//! reported, so joining or transferring evidence never touches memory
//! beyond the class. A conflict is kept rather than retracted, so its
//! report can name every side.
//!
//! Types and values cross the same [`Edge`]. A call relabels the claims to
//! the call site, so no origin ever points outside the declaration that
//! owns the class, and a conflict whose every claim arrived through a call
//! was already a conflict where it arose and is reported there, once. A
//! branch delivers its types to its `if` whichever branch is live, and the
//! `if` never unifies with its branches: branches that disagree make a
//! conflict on the `if` alone.
//!
//! Values arrive by flows only. A literal and a known-unit class are facts;
//! everything else is derived along an edge from one or two providers. An
//! operator's edge reads the operator in the may-[`Domain`], the one
//! semantics every reader of the graph shares; the other edges copy, gate,
//! or narrow a value by the contexts the graph records. Hull is the join,
//! and a recursion would climb forever, so an edge that closes a cycle of
//! the flow graph rounds its endpoints to the program's [`Thresholds`],
//! which keeps every ascending chain finite.

use std::num::NonZeroU32;

use sumi_graph::{BinaryOp, Domain, May, Thresholds, Ty};

use crate::solver::Lattice;

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
    pub fn local(index: usize) -> Self {
        let rank = u32::try_from(index + 1).expect("claim count fits u32");
        assert!(rank < IMPORTED, "claim count fits below the imported bit");
        Self(NonZeroU32::new(rank).unwrap())
    }

    /// The one claim a replay makes: it records no origin, since nothing is
    /// reported from where a replay's evidence came.
    pub const REPLAYED: Self = Self(NonZeroU32::MAX);

    fn imported(self) -> bool {
        self.0.get() & IMPORTED != 0
    }

    pub fn index(self) -> usize {
        ((self.0.get() & !IMPORTED) - 1) as usize
    }
}

/// The type evidence on a class: for each scalar type, the best claim that
/// the class has it. No claim is unresolved, one is solved, and more than
/// one is a conflict.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Evidence {
    claims: [Option<Claim>; Ty::ALL.len()],
}

/// Evidence slots are indexed by discriminant, in the order `Ty::ALL` lists.
const _: () = {
    let mut index = 0;
    while index < Ty::ALL.len() {
        assert!(Ty::ALL[index] as usize == index);
        index += 1;
    }
};

impl Evidence {
    pub const NONE: Self = Self {
        claims: [None; Ty::ALL.len()],
    };

    pub fn single(ty: Ty, claim: Claim) -> Self {
        let mut evidence = Self::NONE;
        evidence.claims[ty as usize] = Some(claim);
        evidence
    }

    /// Join `other` in, keeping the best claim of each type: whether
    /// anything changed.
    pub fn join(&mut self, other: &Self) -> bool {
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

    /// The same types, all claimed by `claim` on the far side of a call.
    pub fn imported(&self, claim: Claim) -> Self {
        let imported = Claim(claim.0 | IMPORTED);
        Self {
            claims: self.claims.map(|claim| claim.map(|_| imported)),
        }
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

/// What a class learns crossing a flow: its types and values in terms of
/// the first provider's, and the second's for a two-provider edge.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Edge {
    /// A callee's result into a call: the same types, all claimed at the
    /// call site, and the values, rounded to the thresholds when the flow
    /// closes a cycle.
    Call(Claim),
    /// A `let` without an annotation from its initializer: the types and
    /// values as they are, and one class with it in the replay, so a
    /// demand on a read of the binding is a demand on what it was bound to.
    Bind,
    /// A value unchanged and nothing of its types: a declared binding's
    /// initializer, a declared result's body, and the parent context of a
    /// branch whose condition has no value.
    Copy,
    /// A read of a local narrowed by a comparison with the second provider
    /// holding in the given sense: the local's types as they are, and one
    /// class with it in the replay, so the read still types once solved.
    Refine {
        op: BinaryOp,
        local_is_lhs: bool,
        sense: bool,
    },
    /// A read of a boolean local narrowed to one value, typed as `Refine`.
    Exactly(bool),
    /// A branch's value into its `if`, while the branch's context, the
    /// second provider, is live; its types either way, so the `if` learns
    /// what each arm is and never decides what an arm is.
    Branch,
    /// One operand of `==` or `!=` telling the other its types, each way,
    /// and nothing of its values, since comparing two values says nothing
    /// about their ranges.
    Peer,
    Neg,
    Not,
    /// An eager operator over its operands.
    Binary(BinaryOp),
    /// `&&` or `||` over its operands' values.
    Lazy {
        and: bool,
    },
    /// A context: live when the condition may be true, or false, and the
    /// enclosing context, the second provider, is live.
    Then,
    Else,
    /// An argument into a parameter, while the call's context, the second
    /// provider, is live. Rounded to the thresholds when the flow closes a
    /// cycle.
    Argument,
    /// A context into a class that is unit while the context is live: a
    /// call's into the callee's entry, a block's into its tail-less self.
    Enter,
}

impl Edge {
    /// Whether the consumer is one class with the first provider in the
    /// replay: a binding with its initializer, a narrowed read with its
    /// local.
    pub fn aliases(self) -> bool {
        matches!(self, Self::Bind | Self::Refine { .. } | Self::Exactly(_))
    }
}

/// The evidence on a class: its types and its values, joined side by side
/// and crossing the same edges.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Product {
    pub types: Evidence,
    pub values: May,
}

impl Lattice for Product {
    type Edge = Edge;
    type Context = Thresholds;

    fn bottom() -> Self {
        Self {
            types: Evidence::NONE,
            values: May::NONE,
        }
    }

    fn join(&mut self, other: &Self) -> bool {
        let types = self.types.join(&other.types);
        let ints = self.values.ints.join(&other.values.ints);
        let bools = self.values.bools.join(other.values.bools);
        let unit = !self.values.unit && other.values.unit;
        self.values.unit |= other.values.unit;
        types | ints | bools | unit
    }

    /// An arithmetic result can outgrow its operands. Everything else
    /// copies, narrows, or gates a value, or is a boolean, unit, or a set
    /// of at most three type claims, none of which can climb.
    fn grows(edge: &Edge) -> bool {
        matches!(
            edge,
            Edge::Neg
                | Edge::Binary(
                    BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Div | BinaryOp::Rem
                )
        )
    }

    /// Integers climb through copies, arithmetic, refinement, branches,
    /// arguments, and calls. A comparison, a lazy operator, and a context
    /// deliver a boolean or liveness, which are finite; the context that
    /// gates a branch or an argument carries nothing of its own; and type
    /// claims never climb, so a peer carries nothing.
    fn carries(edge: &Edge, second: bool) -> bool {
        match edge {
            Edge::Peer
            | Edge::Not
            | Edge::Lazy { .. }
            | Edge::Then
            | Edge::Else
            | Edge::Enter
            | Edge::Exactly(_) => false,
            Edge::Binary(op) => matches!(
                op,
                BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Div | BinaryOp::Rem
            ),
            Edge::Call(_) | Edge::Bind | Edge::Copy | Edge::Neg | Edge::Refine { .. } => true,
            Edge::Branch | Edge::Argument => !second,
        }
    }

    fn transfer(&self, edge: &Edge, other: Option<&Self>, cyclic: bool, cx: &Thresholds) -> Self {
        let second = || {
            &other
                .expect("a two-provider edge has its second provider")
                .values
        };
        // Within one body the flow graph is acyclic, so every cycle crosses
        // a call and back: rounding the two interprocedural edges on a cycle
        // is what keeps every ascending chain finite.
        let rounded = |value: &May| {
            if cyclic {
                May {
                    ints: value.ints.round(cx),
                    ..value.clone()
                }
            } else {
                value.clone()
            }
        };
        // An operator is read in the may-domain, where it never faults.
        const TOTAL: &str = "the may-domain is total";
        let types = match *edge {
            Edge::Call(claim) => self.types.imported(claim),
            Edge::Bind | Edge::Refine { .. } | Edge::Exactly(_) | Edge::Branch | Edge::Peer => {
                self.types
            }
            Edge::Copy
            | Edge::Neg
            | Edge::Not
            | Edge::Binary(_)
            | Edge::Lazy { .. }
            | Edge::Then
            | Edge::Else
            | Edge::Argument
            | Edge::Enter => Evidence::NONE,
        };
        let values = &self.values;
        let values = match *edge {
            Edge::Call(_) => rounded(values),
            Edge::Bind | Edge::Copy => values.clone(),
            Edge::Peer => May::NONE,
            Edge::Neg => values.neg().expect(TOTAL),
            Edge::Not => values.not().expect(TOTAL),
            Edge::Binary(op) => May::binary(op, values, second()).expect(TOTAL),
            Edge::Lazy { and } => May::lazy(and, values, second()).expect(TOTAL),
            Edge::Refine {
                op,
                local_is_lhs,
                sense,
            } => values.refine(op, local_is_lhs, sense, second()),
            Edge::Exactly(value) => values.exactly(value),
            Edge::Then => May::of_unit(values.bools.may_true() && second().live()),
            Edge::Else => May::of_unit(values.bools.may_false() && second().live()),
            Edge::Branch => {
                if second().live() {
                    values.clone()
                } else {
                    May::NONE
                }
            }
            Edge::Argument => {
                if second().live() {
                    rounded(values)
                } else {
                    May::NONE
                }
            }
            Edge::Enter => May::of_unit(values.live()),
        };
        Self { types, values }
    }

    /// Type claims never widen. The exact recomputation of the values
    /// starts from what the class held before its component moved it, a
    /// literal's value or an entry's liveness included, and adds the flows
    /// without rounding, so it is complete: what rounding widened comes
    /// back to what the flows deliver without it.
    fn narrow(&mut self, exact: &Self) -> bool {
        if self.values == exact.values {
            return false;
        }
        self.values = exact.values.clone();
        true
    }
}

#[cfg(test)]
mod tests {
    use sumi_graph::{Bools, Int};

    use super::*;

    /// The may-values of every integer from `lo` to `hi`, zero included
    /// when it lies between: the join of two points keeps a hole there.
    fn band(lo: i64, hi: i64) -> May {
        let mut band = May::int(&Int::from(lo));
        for point in [0, hi] {
            if lo <= point && point <= hi {
                band.ints.join(&May::int(&Int::from(point)).ints);
            }
        }
        band
    }

    fn values(values: May) -> Product {
        Product {
            types: Evidence::NONE,
            values,
        }
    }

    #[test]
    fn evidence_is_three_words_and_an_edge_two() {
        assert_eq!(size_of::<Evidence>(), 12);
        assert_eq!(size_of::<Option<Claim>>(), 4);
        assert_eq!(size_of::<Edge>(), 8);
    }

    #[test]
    fn transfers_derive_and_only_cyclic_interprocedural_flows_round() {
        let cx = [15, 2].map(Int::from).into_iter().collect::<Thresholds>();
        let a = values(band(4, 13));
        let b = values(May::int(&2.into()));
        let edge = Edge::Binary(BinaryOp::Mul);
        assert_eq!(a.transfer(&edge, Some(&b), false, &cx).values, band(8, 26));
        let edge = Edge::Binary(BinaryOp::Lt);
        assert_eq!(
            a.transfer(&edge, Some(&b), false, &cx).values.bools,
            Bools::from(false)
        );
        let edge = Edge::Lazy { and: true };
        assert_eq!(
            values(May::bool(false))
                .transfer(&edge, Some(&Product::bottom()), false, &cx)
                .values
                .bools,
            Bools::from(false)
        );
        assert_eq!(
            values(May::bool(true))
                .transfer(&Edge::Not, None, false, &cx)
                .values
                .bools,
            Bools::from(false)
        );
        let call = Edge::Call(Claim::local(0));
        assert_eq!(a.transfer(&call, None, false, &cx).values, a.values);
        assert_eq!(a.transfer(&call, None, true, &cx).values, band(3, 14));
        let live = values(May::unit());
        assert_eq!(
            a.transfer(&Edge::Argument, Some(&live), true, &cx).values,
            band(3, 14)
        );
        assert_eq!(a.transfer(&Edge::Copy, None, true, &cx).values, a.values);
        assert_eq!(a.transfer(&Edge::Peer, None, false, &cx).values, May::NONE);
    }

    #[test]
    fn contexts_gate_branches_arguments_and_entries() {
        let cx = Thresholds::default();
        let live = values(May::unit());
        let dead = Product::bottom();
        let cond = values(May::bool(false));
        assert_eq!(cond.transfer(&Edge::Then, Some(&live), false, &cx), dead);
        assert_eq!(cond.transfer(&Edge::Else, Some(&live), false, &cx), live);
        assert_eq!(cond.transfer(&Edge::Else, Some(&dead), false, &cx), dead);
        let value = values(May::int(&3.into()));
        assert_eq!(
            value.transfer(&Edge::Branch, Some(&live), false, &cx),
            value
        );
        assert_eq!(value.transfer(&Edge::Branch, Some(&dead), false, &cx), dead);
        assert_eq!(
            value.transfer(&Edge::Argument, Some(&dead), false, &cx),
            dead
        );
        assert_eq!(
            value.transfer(&Edge::Argument, Some(&live), false, &cx),
            value
        );
        assert_eq!(live.transfer(&Edge::Enter, None, false, &cx), live);
        assert_eq!(dead.transfer(&Edge::Enter, None, false, &cx), dead);
    }

    /// Types cross the edges that carry a value unchanged or narrowed,
    /// and a call relabels them; an operator's result, a context, and a
    /// declared copy learn nothing of their providers' types.
    #[test]
    fn types_cross_aliasing_edges_and_are_relabeled_by_calls() {
        let cx = Thresholds::default();
        let int = Product {
            types: Evidence::single(Ty::Int, Claim::local(3)),
            values: May::int(&1.into()),
        };
        let live = values(May::unit());
        for edge in [Edge::Bind, Edge::Exactly(true), Edge::Peer] {
            assert_eq!(int.transfer(&edge, None, false, &cx).types, int.types);
        }
        assert_eq!(
            int.transfer(&Edge::Branch, Some(&Product::bottom()), false, &cx)
                .types,
            int.types
        );
        for edge in [Edge::Copy, Edge::Neg, Edge::Enter] {
            assert_eq!(int.transfer(&edge, None, false, &cx).types, Evidence::NONE);
        }
        assert_eq!(
            int.transfer(&Edge::Argument, Some(&live), false, &cx).types,
            Evidence::NONE
        );
        let called = int.transfer(&Edge::Call(Claim::local(7)), None, false, &cx);
        assert_eq!(called.types.ty(), Some(Ty::Int));
        assert!(called.types.claims()[0].1.imported());
        assert_eq!(called.types.claims()[0].1.index(), 7);
    }

    #[test]
    fn a_boolean_read_is_narrowed_to_its_guard() {
        let flag = values(May::bools(Bools::BOTH));
        let cx = Thresholds::default();
        assert_eq!(
            flag.transfer(&Edge::Exactly(false), None, false, &cx)
                .values
                .bools,
            Bools::from(false)
        );
    }
}
