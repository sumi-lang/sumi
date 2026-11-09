//! The [`May`] values the solver carries, crossing [`Edge`]s, [`Pair`]s, and [`Many`]s. Calls,
//! arguments, and loop backedges round cyclic integer flows to thresholds, so every ascending chain
//! is finite.

use sumi_graph::{
    BinaryOp, Case, CmpOp, Decl, DeclId, Domain, FieldName, Ints, May, Thresholds, Unions,
};

use crate::solver::{Carry, Lattice};

/// A flow from one provider.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Edge {
    /// A callee's result into a call.
    Call,
    /// A copy of the provider's values.
    Values,
    Exactly(bool),
    ShortCircuit(bool),
    Neg,
    Not,
    Enter,
    /// A read of the field from its base, whatever declared type reaches it.
    Field(FieldName),
    /// An arm's binding: the values of the type among the scrutinee's.
    Narrow(sumi_graph::Ty),
}

/// A flow from two providers. The second of `Binary`, `Lazy`, and `Refine` is the other operand;
/// of `Branch`, `Arm`, and `Argument`, the context that gates them.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Pair {
    Refine {
        op: CmpOp,
        local_is_lhs: bool,
        sense: bool,
    },
    /// A value where its context is live.
    Branch,
    Binary(BinaryOp),
    Lazy {
        is_and: bool,
    },
    /// A boolean arm context from its condition and parent: live where the condition may be the
    /// boolean.
    Bool(bool),
    /// An arm context from its scrutinee and parent; `Context::cases[index]` excludes earlier arms.
    Arm(u16),
    Argument,
    Backedge,
    Range,
}

/// A flow from every field of a construction, in declaration order.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Many {
    Make(DeclId),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct Arm {
    pub case: Case,
    pub previous: Option<u16>,
}

/// What every transfer reads: the thresholds, the declared types a field read goes through, the
/// unions a case admits, and the cases the `Arm` pairs index.
pub(crate) struct Context {
    pub thresholds: Thresholds,
    pub decls: Box<[Decl]>,
    pub unions: Unions,
    pub cases: Box<[Arm]>,
}

impl Context {
    fn selects(&self, index: u16, decl: DeclId) -> bool {
        let arm = self.cases[usize::from(index)];
        if !arm.case.selects_decl(decl, &self.unions) {
            return false;
        }
        let mut previous = arm.previous;
        while let Some(index) = previous {
            let arm = self.cases[usize::from(index)];
            if arm.case.selects_decl(decl, &self.unions) {
                return false;
            }
            previous = arm.previous;
        }
        true
    }
}

/// Every value cycle crosses a call, an argument, or a loop backedge; rounding there keeps every
/// ascending chain finite.
fn rounded(values: &May, cyclic: bool, cx: &Context) -> May {
    if cyclic {
        values.rounded(&cx.thresholds)
    } else {
        values.clone()
    }
}

impl Lattice for May {
    type Edge = Edge;
    type Pair = Pair;
    type Many = Many;
    type Context = Context;

    fn bottom() -> Self {
        Self::NONE
    }

    fn join(&mut self, other: &Self) -> bool {
        May::join(self, other)
    }

    /// Only values climb: a finite one, such as a boolean, carries nothing.
    fn carries(edge: &Edge) -> Carry {
        match edge {
            Edge::Not | Edge::Enter | Edge::ShortCircuit(_) | Edge::Exactly(_) => Carry::Nothing,
            Edge::Neg => Carry::Grows,
            Edge::Call | Edge::Values | Edge::Field(_) | Edge::Narrow(_) => Carry::Passes,
        }
    }

    /// Every field passes into the value made.
    fn carries_many(many: &Many) -> Carry {
        match many {
            Many::Make(_) => Carry::Passes,
        }
    }

    /// A gating context carries nothing of its own.
    fn carries_pair(pair: &Pair) -> [Carry; 2] {
        match pair {
            Pair::Lazy { .. } | Pair::Bool(_) | Pair::Arm(_) => [Carry::Nothing; 2],
            Pair::Binary(BinaryOp::Arith(_)) => [Carry::Grows; 2],
            Pair::Binary(BinaryOp::Cmp(_)) => [Carry::Nothing; 2],
            Pair::Refine { .. } | Pair::Range => [Carry::Passes; 2],
            Pair::Branch | Pair::Argument | Pair::Backedge => [Carry::Passes, Carry::Nothing],
        }
    }

    fn transfer(&self, edge: &Edge, cyclic: bool, cx: &Context) -> Self {
        match *edge {
            Edge::Call => rounded(self, cyclic, cx),
            Edge::Values => self.clone(),
            Edge::Neg => {
                let Ok(negated) = self.neg();
                negated
            }
            Edge::Not => {
                let Ok(inverted) = self.not();
                inverted
            }
            Edge::Exactly(value) | Edge::ShortCircuit(value) => self.exactly(value),
            Edge::Enter => Self::of_unit(self.is_live()),
            Edge::Field(name) => {
                let Ok(field) = self.field(name, &cx.decls, &cx.unions);
                field
            }
            Edge::Narrow(ty) => self.narrow(ty, &cx.unions),
        }
    }

    fn widens(edge: &Edge) -> bool {
        matches!(edge, Edge::Call)
    }

    fn widens_pair(pair: &Pair) -> bool {
        matches!(pair, Pair::Argument | Pair::Backedge)
    }

    fn combine(&self, pair: &Pair, second: &Self, cyclic: bool, cx: &Context) -> Self {
        match *pair {
            Pair::Binary(op) => {
                let Ok(combined) = May::binary(op, self, second);
                combined
            }
            Pair::Lazy { is_and } => {
                let Ok(combined) = May::lazy(is_and, self, second);
                combined
            }
            Pair::Refine {
                op,
                local_is_lhs,
                sense,
            } => self.refine(op, local_is_lhs, sense, second),
            Pair::Bool(true) => Self::of_unit(self.bools.may_true() && second.is_live()),
            Pair::Bool(false) => Self::of_unit(self.bools.may_false() && second.is_live()),
            Pair::Arm(case) => Self::of_unit(
                second.is_live() && self.decls.iter().any(|(decl, _)| cx.selects(case, decl)),
            ),
            Pair::Range => Self::ints(Ints::range(&self.ints, &second.ints)),
            Pair::Branch => {
                if second.is_live() {
                    self.clone()
                } else {
                    Self::NONE
                }
            }
            Pair::Argument | Pair::Backedge => {
                if second.is_live() {
                    rounded(self, cyclic, cx)
                } else {
                    Self::NONE
                }
            }
        }
    }

    /// Field types bound nesting even in ill-typed cycles, which integer rounding cannot bound.
    fn combine_many<'a>(
        &'a self,
        many: &Many,
        others: impl Iterator<Item = &'a Self>,
        cyclic: bool,
        cx: &Context,
    ) -> Self {
        let Many::Make(decl) = *many;
        let fields = std::iter::once(self)
            .chain(others)
            .zip(cx.decls[decl.index()].fields())
            .map(|(field, &(_, ty))| {
                let field = ty.map_or(Self::NONE, |ty| field.narrow(ty, &cx.unions));
                if cyclic {
                    field.rounded(&cx.thresholds)
                } else {
                    field
                }
            })
            .collect();
        May::make(decl, fields)
    }

    fn narrow(&mut self, exact: &Self) -> bool {
        if self == exact {
            return false;
        }
        *self = exact.clone();
        true
    }
}

#[cfg(test)]
mod tests {
    use sumi_graph::{ArithOp, Bools, Int};

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

    #[test]
    fn an_edge_is_two_words() {
        assert_eq!(size_of::<Edge>(), 8);
        assert!(size_of::<Pair>() <= 4);
    }

    #[test]
    fn transfers_derive_and_only_cyclic_interprocedural_flows_round() {
        let cx = Context {
            thresholds: [15, 2].map(Int::from).into_iter().collect(),
            decls: Box::new([]),
            unions: Unions::new(),
            cases: Box::new([]),
        };
        let a = band(4, 13);
        let b = May::int(&2.into());
        let edge = Pair::Binary(BinaryOp::Arith(ArithOp::Mul));
        assert_eq!(a.combine(&edge, &b, false, &cx), band(8, 26));
        let edge = Pair::Binary(BinaryOp::Cmp(CmpOp::Lt));
        assert_eq!(a.combine(&edge, &b, false, &cx).bools, Bools::from(false));
        let edge = Pair::Lazy { is_and: true };
        assert_eq!(
            (May::bool(false))
                .combine(&edge, &May::NONE, false, &cx)
                .bools,
            Bools::from(false)
        );
        assert_eq!(
            (May::bool(true)).transfer(&Edge::Not, false, &cx).bools,
            Bools::from(false)
        );
        assert_eq!(a.transfer(&Edge::Call, false, &cx), a);
        assert_eq!(a.transfer(&Edge::Call, true, &cx), band(3, 14));
        let live = May::unit();
        assert_eq!(a.combine(&Pair::Argument, &live, true, &cx), band(3, 14));
        assert_eq!(a.transfer(&Edge::Values, true, &cx), a);
    }

    #[test]
    fn contexts_gate_branches_arguments_and_entries() {
        let cx = Context {
            thresholds: Thresholds::default(),
            decls: Box::new([]),
            unions: Unions::new(),
            cases: Box::new([]),
        };
        let live = May::unit();
        let dead = May::NONE;
        let cond = May::bool(false);
        assert_eq!(cond.combine(&Pair::Bool(true), &live, false, &cx), dead);
        assert_eq!(cond.combine(&Pair::Bool(false), &live, false, &cx), live);
        assert_eq!(cond.combine(&Pair::Bool(false), &dead, false, &cx), dead);
        let value = May::int(&3.into());
        assert_eq!(value.combine(&Pair::Branch, &live, false, &cx), value);
        assert_eq!(value.combine(&Pair::Branch, &dead, false, &cx), dead);
        assert_eq!(value.combine(&Pair::Argument, &dead, false, &cx), dead);
        assert_eq!(value.combine(&Pair::Argument, &live, false, &cx), value);
        assert_eq!(live.transfer(&Edge::Enter, false, &cx), live);
        assert_eq!(dead.transfer(&Edge::Enter, false, &cx), dead);
    }

    #[test]
    fn a_boolean_read_is_narrowed_to_its_guard() {
        let flag = May::bools(Bools::BOTH);
        let cx = Context {
            thresholds: Thresholds::default(),
            decls: Box::new([]),
            unions: Unions::new(),
            cases: Box::new([]),
        };
        assert_eq!(
            flag.transfer(&Edge::Exactly(false), false, &cx).bools,
            Bools::from(false)
        );
    }
}
