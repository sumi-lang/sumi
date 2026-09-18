//! The may-values as the solver carries them: what a [`May`] set becomes
//! crossing each kind of flow, and how a chain of them is kept finite.
//!
//! Values arrive by flows only. A literal and a known-unit class are facts;
//! everything else is derived along a [`RangeEdge`] from one or two
//! providers. An operator's edge reads the operator in the may-[`Domain`],
//! the one semantics every reader of the graph shares; the other edges
//! copy, gate, or narrow a value by the contexts the graph records. Hull
//! is the join, and a recursion would climb forever, so an edge that
//! closes a cycle of the flow graph rounds its endpoints to the program's
//! [`Thresholds`], which keeps every ascending chain finite without a
//! widening operator in the solver.

use sumi_graph::{BinaryOp, Domain, May, Thresholds};

use crate::solver::Lattice;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnaryOp {
    Neg,
    Not,
}

/// How a may-set changes crossing a flow: what the consumer's values are in
/// terms of the first provider's, and the second's for a two-provider edge.
#[derive(Clone, Copy, Debug)]
pub enum RangeEdge {
    /// Nothing: the range side of a typing-only flow.
    None,
    /// The value unchanged: a binding's initializer, annotated or not, a
    /// declared result's body, and the parent context of a branch whose
    /// condition has no value.
    Copy,
    Unary(UnaryOp),
    /// An eager operator over its operands.
    Binary(BinaryOp),
    /// `&&` or `||` over its operands' values.
    Lazy {
        and: bool,
    },
    /// A local narrowed by a comparison with the second provider holding in
    /// the given sense.
    Refine {
        op: BinaryOp,
        local_is_lhs: bool,
        sense: bool,
    },
    /// A boolean local narrowed to one value.
    Exactly(bool),
    /// A context: live when the condition may be true, or false, and the
    /// enclosing context is live.
    Then,
    Else,
    /// A branch's value into its `if`, while the branch's context is live.
    Branch,
    /// An argument into a parameter, while the call's context is live.
    /// Rounded to the thresholds when the flow closes a cycle.
    Argument,
    /// A callee's result into a call. Rounded likewise.
    Call,
    /// A context into a class that is unit while the context is live: a
    /// call's into the callee's entry, a block's into its tail-less self.
    Enter,
}

impl Lattice for May {
    type Edge = RangeEdge;
    type Context = Thresholds;

    fn bottom() -> Self {
        Self::NONE
    }

    fn join(&mut self, other: &Self) -> bool {
        let ints = self.ints.join(&other.ints);
        let bools = self.bools.join(other.bools);
        let unit = !self.unit && other.unit;
        self.unit |= other.unit;
        ints | bools | unit
    }

    /// An arithmetic result can outgrow its operands; everything else
    /// copies, narrows, or gates a value, or is a boolean or unit, which
    /// cannot climb.
    fn grows(edge: &RangeEdge) -> bool {
        matches!(
            edge,
            RangeEdge::Unary(UnaryOp::Neg)
                | RangeEdge::Binary(
                    BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Div | BinaryOp::Rem
                )
        )
    }

    /// Integers climb through copies, arithmetic, refinement, branches,
    /// arguments, and calls. A comparison, a lazy operator, and a context
    /// deliver a boolean or liveness, which are finite; the context that
    /// gates a branch or an argument carries nothing of its own; and a
    /// typing-only flow carries nothing at all.
    fn carries(edge: &RangeEdge, second: bool) -> bool {
        match edge {
            RangeEdge::None
            | RangeEdge::Lazy { .. }
            | RangeEdge::Then
            | RangeEdge::Else
            | RangeEdge::Enter
            | RangeEdge::Exactly(_) => false,
            RangeEdge::Unary(op) => *op == UnaryOp::Neg,
            RangeEdge::Binary(op) => matches!(
                op,
                BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Div | BinaryOp::Rem
            ),
            RangeEdge::Copy | RangeEdge::Call | RangeEdge::Refine { .. } => true,
            RangeEdge::Branch | RangeEdge::Argument => !second,
        }
    }

    fn transfer(
        &self,
        edge: &RangeEdge,
        other: Option<&Self>,
        cyclic: bool,
        cx: &Thresholds,
    ) -> Self {
        let second = || other.expect("a two-provider edge has its second provider");
        // Within one body the flow graph is acyclic, so every cycle crosses
        // a call and back: rounding the two interprocedural edges on a cycle
        // is what keeps every ascending chain finite.
        let rounded = |value: &Self| {
            if cyclic {
                Self {
                    ints: value.ints.round(cx),
                    ..value.clone()
                }
            } else {
                value.clone()
            }
        };
        // An operator is read in the may-domain, where it never faults.
        const TOTAL: &str = "the may-domain is total";
        match *edge {
            RangeEdge::None => Self::bottom(),
            RangeEdge::Copy => self.clone(),
            RangeEdge::Unary(UnaryOp::Neg) => self.neg().expect(TOTAL),
            RangeEdge::Unary(UnaryOp::Not) => self.not().expect(TOTAL),
            RangeEdge::Binary(op) => Self::binary(op, self, second()).expect(TOTAL),
            RangeEdge::Lazy { and } => Self::lazy(and, self, second()).expect(TOTAL),
            RangeEdge::Refine {
                op,
                local_is_lhs,
                sense,
            } => self.refine(op, local_is_lhs, sense, second()),
            RangeEdge::Exactly(value) => self.exactly(value),
            RangeEdge::Then => Self::of_unit(self.bools.may_true() && second().live()),
            RangeEdge::Else => Self::of_unit(self.bools.may_false() && second().live()),
            RangeEdge::Branch => {
                if second().live() {
                    self.clone()
                } else {
                    Self::bottom()
                }
            }
            RangeEdge::Argument => {
                if second().live() {
                    rounded(self)
                } else {
                    Self::bottom()
                }
            }
            RangeEdge::Call => rounded(self),
            RangeEdge::Enter => Self::of_unit(self.live()),
        }
    }

    /// The exact recomputation starts from what the class held before its
    /// component moved it, a literal's value or an entry's liveness
    /// included, and adds the flows without rounding, so it is complete:
    /// what rounding widened comes back to what the flows deliver without
    /// it.
    fn narrow(&mut self, exact: &Self) -> bool {
        if *self == *exact {
            return false;
        }
        *self = exact.clone();
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
        let mut band = May::int(Int::from(lo));
        for point in [0, hi] {
            if lo <= point && point <= hi {
                Lattice::join(&mut band, &May::int(Int::from(point)));
            }
        }
        band
    }

    /// The may-values of both booleans.
    fn either() -> May {
        May::bools(Bools::BOTH)
    }

    #[test]
    fn transfers_derive_and_only_cyclic_interprocedural_flows_round() {
        let cx = [15, 2].map(Int::from).into_iter().collect::<Thresholds>();
        let a = band(4, 13);
        let b = May::int(2.into());
        let edge = RangeEdge::Binary(BinaryOp::Mul);
        assert_eq!(a.transfer(&edge, Some(&b), false, &cx), band(8, 26));
        let edge = RangeEdge::Binary(BinaryOp::Lt);
        assert_eq!(
            a.transfer(&edge, Some(&b), false, &cx).bools,
            Bools::from(false)
        );
        let edge = RangeEdge::Lazy { and: true };
        assert_eq!(
            May::bool(false)
                .transfer(&edge, Some(&May::bottom()), false, &cx)
                .bools,
            Bools::from(false)
        );
        assert_eq!(
            May::bool(true)
                .transfer(&RangeEdge::Unary(UnaryOp::Not), None, false, &cx,)
                .bools,
            Bools::from(false)
        );
        assert_eq!(a.transfer(&RangeEdge::Call, None, false, &cx), a);
        assert_eq!(a.transfer(&RangeEdge::Call, None, true, &cx), band(3, 14));
        let live = May::unit();
        assert_eq!(
            a.transfer(&RangeEdge::Argument, Some(&live), true, &cx),
            band(3, 14)
        );
        assert_eq!(a.transfer(&RangeEdge::Copy, None, true, &cx), a);
        assert_eq!(
            a.transfer(&RangeEdge::None, None, false, &cx),
            May::bottom()
        );
    }

    #[test]
    fn contexts_gate_branches_arguments_and_entries() {
        let cx = Thresholds::default();
        let live = May::unit();
        let dead = May::bottom();
        let cond = May::bool(false);
        assert_eq!(
            cond.transfer(&RangeEdge::Then, Some(&live), false, &cx),
            dead
        );
        assert_eq!(
            cond.transfer(&RangeEdge::Else, Some(&live), false, &cx),
            live
        );
        assert_eq!(
            cond.transfer(&RangeEdge::Else, Some(&dead), false, &cx),
            dead
        );
        let value = May::int(3.into());
        assert_eq!(
            value.transfer(&RangeEdge::Branch, Some(&live), false, &cx),
            value
        );
        assert_eq!(
            value.transfer(&RangeEdge::Branch, Some(&dead), false, &cx),
            dead
        );
        let edge = RangeEdge::Argument;
        assert_eq!(value.transfer(&edge, Some(&dead), false, &cx), dead);
        assert_eq!(value.transfer(&edge, Some(&live), false, &cx), value);
        assert_eq!(live.transfer(&RangeEdge::Enter, None, false, &cx), live);
        assert_eq!(dead.transfer(&RangeEdge::Enter, None, false, &cx), dead);
    }

    #[test]
    fn a_boolean_read_is_narrowed_to_its_guard() {
        let flag = either();
        let cx = Thresholds::default();
        assert_eq!(
            flag.transfer(&RangeEdge::Exactly(false), None, false, &cx)
                .bools,
            Bools::from(false)
        );
    }
}
