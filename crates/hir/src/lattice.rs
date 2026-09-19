//! The [`Lattice`] the solver carries: per class, the best claim of each scalar type and the
//! [`May`] values, crossing the same [`Edge`]s. A call or argument edge that closes a cycle rounds
//! the ints to the thresholds, so every ascending chain is finite.

use std::convert::Infallible;
use std::num::NonZeroU32;

use sumi_graph::{BinaryOp, Domain, May, Thresholds, Ty};

use crate::solver::{Carry, Lattice};

/// A claim that a class has a type, as its rank: its one-based index in the walk, with `IMPORTED`
/// set once it crossed a flow. Lower wins.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct Claim(NonZeroU32);

const IMPORTED: u32 = 1 << 31;

impl Claim {
    pub fn local(index: usize) -> Self {
        let rank = u32::try_from(index + 1).expect("claim count fits u32");
        assert!(rank < IMPORTED, "claim count fits below the imported bit");
        Self(NonZeroU32::new(rank).unwrap())
    }

    /// The claim a replay makes: no origin, since a replay reports nothing.
    pub const REPLAYED: Self = Self(NonZeroU32::MAX);

    fn imported(self) -> bool {
        self.0.get() & IMPORTED != 0
    }

    pub fn index(self) -> usize {
        ((self.0.get() & !IMPORTED) - 1) as usize
    }
}

/// Per scalar type, the best claim that the class has it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Evidence {
    claims: [Option<Claim>; Ty::ALL.len()],
}

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

    pub fn imported(&self, claim: Claim) -> Self {
        let imported = Claim(claim.0 | IMPORTED);
        Self {
            claims: self.claims.map(|claim| claim.map(|_| imported)),
        }
    }

    /// The type claimed, if exactly one is.
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

    /// A conflict whose every claim crossed a flow; it is reported where it arose.
    pub fn inherited(&self) -> bool {
        self.is_conflict() && self.claims.iter().flatten().all(|claim| claim.imported())
    }

    /// Every claim, best first.
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

fn total(result: Result<May, Infallible>) -> May {
    match result {
        Ok(value) => value,
    }
}

/// The second provider of `Binary`, `Lazy`, and `Refine` is the other operand; of `Branch`, `Then`,
/// `Else`, and `Argument`, the context that gates them.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Edge {
    /// A callee's result into a call, its types relabeled to the call site's claim.
    Call(Claim),
    /// An unannotated `let` from its initializer.
    Bind,
    Values,
    Refine {
        op: BinaryOp,
        local_is_lhs: bool,
        sense: bool,
    },
    Exactly(bool),
    Branch,
    /// One operand of `==` or `!=` typing the other.
    Peer,
    Neg,
    Not,
    Binary(BinaryOp),
    Lazy {
        and: bool,
    },
    Then,
    Else,
    Argument,
    Enter,
}

impl Edge {
    /// Whether the consumer is one class with its first provider in the replay.
    pub fn aliases(self) -> bool {
        matches!(self, Self::Bind | Self::Refine { .. } | Self::Exactly(_))
    }
}

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

    /// Only values climb: type claims are finite, so `Peer` carries nothing.
    fn carries(edge: &Edge, second: bool) -> Carry {
        match edge {
            Edge::Peer
            | Edge::Not
            | Edge::Lazy { .. }
            | Edge::Then
            | Edge::Else
            | Edge::Enter
            | Edge::Exactly(_) => Carry::Nothing,
            Edge::Neg => Carry::Grows,
            Edge::Binary(op) => {
                if op.result() == Ty::Int {
                    Carry::Grows
                } else {
                    Carry::Nothing
                }
            }
            Edge::Call(_) | Edge::Bind | Edge::Values | Edge::Refine { .. } => Carry::Passes,
            Edge::Branch | Edge::Argument => {
                if second {
                    Carry::Nothing
                } else {
                    Carry::Passes
                }
            }
        }
    }

    fn transfer(&self, edge: &Edge, other: Option<&Self>, cyclic: bool, cx: &Thresholds) -> Self {
        let second = || {
            &other
                .expect("a two-provider edge has its second provider")
                .values
        };
        // A body's flow graph is acyclic, so every cycle crosses a call and an argument edge;
        // rounding those two keeps every chain finite.
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
        let types = match *edge {
            Edge::Call(claim) => self.types.imported(claim),
            Edge::Bind | Edge::Refine { .. } | Edge::Exactly(_) | Edge::Branch | Edge::Peer => {
                self.types
            }
            Edge::Values
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
            Edge::Bind | Edge::Values => values.clone(),
            Edge::Peer => May::NONE,
            Edge::Neg => total(values.neg()),
            Edge::Not => total(values.not()),
            Edge::Binary(op) => total(May::binary(op, values, second())),
            Edge::Lazy { and } => total(May::lazy(and, values, second())),
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

    /// Types never widen, so only the values narrow.
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

    /// `lo` to `hi` inclusive; the join of two points leaves a hole at zero.
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
        assert_eq!(a.transfer(&Edge::Values, None, true, &cx).values, a.values);
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
        for edge in [Edge::Values, Edge::Neg, Edge::Enter] {
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
