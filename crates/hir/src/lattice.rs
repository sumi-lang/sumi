//! The [`Lattice`] the solver carries: per class, the best claim of each type and the [`May`]
//! values, crossing the same [`Edge`]s, [`Pair`]s, and [`Many`]s. Calls, arguments, and loop
//! backedges round cyclic integer flows to thresholds, so every ascending chain is finite.

use std::num::NonZeroU32;

use sumi_graph::{
    BinaryOp, CmpOp, Decl, DeclId, Domain, FieldName, Ints, May, Thresholds, Ty, TyKind,
};

use crate::solver::{Carry, Lattice};

/// A claim that a class has a type, as its rank: its one-based index in the walk, `IMPORTED` once
/// it crossed a flow, `DEMANDED` when a read asked for it. Lower wins: a demand yields to the rest.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct Claim(NonZeroU32);

const DEMANDED: u32 = 1 << 31;
const IMPORTED: u32 = 1 << 30;
/// In the first slot when a hole decided the class: the best rank there is, which no claim takes,
/// so the join that keeps the best claim keeps it over any claim of the first type.
const UNKNOWN: Claim = Claim(NonZeroU32::new(1).unwrap());
const FIRST: u32 = 2;

impl Claim {
    pub fn local(index: usize) -> Self {
        let rank = u32::try_from(index).expect("claim count fits u32") + FIRST;
        assert!(rank < IMPORTED, "claim count fits below the flag bits");
        Self(NonZeroU32::new(rank).unwrap())
    }

    /// The claim a replay makes once a demand held: the type is settled from then on, so it is
    /// no demand, and it has no origin, since a replay reports nothing.
    pub const REPLAYED: Self = Self(NonZeroU32::new(u32::MAX >> 1).unwrap());

    pub fn demanded(self) -> Self {
        Self(self.0 | DEMANDED)
    }

    fn is_imported(self) -> bool {
        self.0.get() & IMPORTED != 0
    }

    fn is_demanded(self) -> bool {
        self.0.get() & DEMANDED != 0
    }

    pub fn index(self) -> usize {
        ((self.0.get() & !(DEMANDED | IMPORTED)) - FIRST) as usize
    }
}

/// Per type, the best claim that the class has it, or the fact that a hole decided it. A class
/// holding the unknown resolves to no type, so no demand on it disagrees, and it crosses every
/// flow a claim does, so nothing a hole reaches is blamed for what the hole might have been.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Evidence {
    /// By scalar, in `Ty::SCALARS` order.
    scalars: [Option<Claim>; Ty::SCALARS.len()],
    /// The best claim of each declared type, at most two: a class rarely claims one, and a
    /// second shows a conflict whatever a third would add, so the evidence stays a copy.
    decls: [Option<(DeclId, Claim)>; 2],
}

fn scalar_slot(ty: Ty) -> Result<usize, DeclId> {
    match ty.kind() {
        TyKind::Int => Ok(0),
        TyKind::Bool => Ok(1),
        TyKind::Unit => Ok(2),
        TyKind::Decl(decl) => Err(decl),
    }
}

impl Evidence {
    pub const NONE: Self = Self {
        scalars: [None; Ty::SCALARS.len()],
        decls: [None; 2],
    };

    pub const UNKNOWN: Self = {
        let mut evidence = Self::NONE;
        evidence.scalars[0] = Some(UNKNOWN);
        evidence
    };

    #[inline]
    pub fn single(ty: Ty, claim: Claim) -> Self {
        let mut evidence = Self::NONE;
        match scalar_slot(ty) {
            Ok(slot) => evidence.scalars[slot] = Some(claim),
            Err(decl) => evidence.decls[0] = Some((decl, claim)),
        }
        evidence
    }

    #[inline]
    pub fn join(&mut self, other: &Self) -> bool {
        let mut grew = false;
        for (mine, theirs) in self.scalars.iter_mut().zip(&other.scalars) {
            if let Some(claim) = theirs
                && mine.is_none_or(|existing| *claim < existing)
            {
                *mine = Some(*claim);
                grew = true;
            }
        }
        if other.decls[0].is_some() {
            for (decl, claim) in other.decls.into_iter().flatten() {
                grew |= self.offer(decl, claim);
            }
        }
        grew
    }

    /// `join` with one claim. True if it grew.
    #[inline]
    pub fn claim(&mut self, ty: Ty, claim: Claim) -> bool {
        match scalar_slot(ty) {
            Ok(slot) => {
                let mine = &mut self.scalars[slot];
                if mine.is_none_or(|existing| claim < existing) {
                    *mine = Some(claim);
                    return true;
                }
                false
            }
            Err(decl) => self.offer(decl, claim),
        }
    }

    /// Keeps `claim` for `decl` if it beats the one held, or in a free slot. True if it did.
    fn offer(&mut self, decl: DeclId, claim: Claim) -> bool {
        for slot in &mut self.decls {
            match slot {
                Some((held, best)) if *held == decl => {
                    if claim < *best {
                        *best = claim;
                        return true;
                    }
                    return false;
                }
                Some(_) => {}
                None => {
                    *slot = Some((decl, claim));
                    return true;
                }
            }
        }
        false
    }

    /// What a call delivers: every claim as the call's, a demand staying one, so the transfer
    /// is monotone and a callee's demands yield to the caller's facts as its own would.
    pub fn imported(&self, claim: Claim) -> Self {
        let imported = Claim(claim.0 | IMPORTED);
        let relabel = |claim: Claim| match claim {
            UNKNOWN => claim,
            _ if claim.is_demanded() => imported.demanded(),
            _ => imported,
        };
        Self {
            scalars: self.scalars.map(|claim| claim.map(relabel)),
            decls: self
                .decls
                .map(|slot| slot.map(|(decl, claim)| (decl, relabel(claim)))),
        }
    }

    /// What a read of field `name` delivers: each claim of a declared type with the field becomes
    /// a claim of the field's type, and the rest claim nothing, which the demand on the read
    /// reports.
    pub fn field(&self, name: FieldName, decls: &[Decl]) -> Self {
        let mut evidence = Self::NONE;
        if self.is_unknown() {
            evidence.scalars[0] = Some(UNKNOWN);
        }
        for (decl, claim) in self.decl_claims() {
            let decl = &decls[decl.index()];
            if let Some(index) = decl.index_of(name)
                && let (_, Some(ty)) = decl.fields()[index]
            {
                evidence.join(&Self::single(ty, claim));
            }
        }
        evidence
    }

    pub fn is_unknown(&self) -> bool {
        self.scalars[0] == Some(UNKNOWN)
    }

    fn decl_claims(&self) -> impl Iterator<Item = (DeclId, Claim)> + '_ {
        self.decls.iter().flatten().copied()
    }

    fn entries(&self) -> impl Iterator<Item = (Ty, Claim)> + '_ {
        let scalars = Ty::SCALARS
            .iter()
            .zip(&self.scalars)
            .filter_map(|(ty, claim)| claim.map(|claim| (*ty, claim)));
        let decls = self
            .decl_claims()
            .map(|(decl, claim)| (Ty::decl(decl), claim));
        scalars.chain(decls)
    }

    /// The types the class resolves among: demands count only where nothing else claims a type.
    fn types(&self) -> impl Iterator<Item = (Ty, Claim)> + '_ {
        let demands_only = self
            .entries()
            .all(|(_, claim)| claim == UNKNOWN || claim.is_demanded());
        self.entries()
            .filter(move |&(_, claim)| claim != UNKNOWN && (demands_only || !claim.is_demanded()))
    }

    /// The type claimed, if exactly one is and no hole decided the class.
    #[inline]
    pub fn ty(&self) -> Option<Ty> {
        if self.is_unknown() {
            return None;
        }
        let mut types = self.types();
        let (ty, _) = types.next()?;
        types.next().is_none().then_some(ty)
    }

    /// Never for a class a hole decided: the claims beside the unknown are not a disagreement.
    pub fn is_conflict(&self) -> bool {
        !self.is_unknown() && self.types().count() > 1
    }

    /// A conflict whose every claim crossed a flow; it is reported where it arose.
    pub fn is_inherited(&self) -> bool {
        self.is_conflict() && self.types().all(|(_, claim)| claim.is_imported())
    }

    /// Every claim, best first.
    pub fn claims(&self) -> Vec<(Ty, Claim)> {
        let mut claims: Vec<_> = self.types().collect();
        claims.sort_by_key(|(_, claim)| *claim);
        claims
    }
}

/// A flow from one provider.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Edge {
    /// A callee's result into a call, its types relabeled to the call site's claim.
    Call(Claim),
    /// An unannotated `let` from its initializer.
    Bind,
    /// Carries type evidence but no abstract values.
    Types,
    /// A mutable SSA version has its declaration's type but not its original value.
    TypeBind,
    Values,
    Exactly(bool),
    /// One operand of `==` or `!=` typing the other.
    Peer,
    Neg,
    Not,
    Enter,
    /// A read of the field from its base, whatever declared type reaches it.
    Field(FieldName),
}

impl Edge {
    /// Whether the consumer is one class with its provider in the replay.
    pub fn aliases(self) -> bool {
        matches!(self, Self::Bind | Self::TypeBind | Self::Exactly(_))
    }
}

/// A flow from two providers. The second of `Binary`, `Lazy`, and `Refine` is the other operand;
/// of `Branch`, `Forward`, `Then`, `Else`, and `Argument`, the context that gates them.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Pair {
    Refine {
        op: CmpOp,
        local_is_lhs: bool,
        sense: bool,
    },
    Branch,
    Forward,
    Outcome,
    Binary(BinaryOp),
    Lazy {
        is_and: bool,
    },
    Then,
    Else,
    Argument,
    Backedge,
    Range,
}

impl Pair {
    /// Whether the consumer is one class with its first provider in the replay.
    pub fn aliases(self) -> bool {
        matches!(self, Self::Refine { .. } | Self::Forward)
    }
}

/// A flow from every field of a construction, in declaration order.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Many {
    Make(DeclId),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Product {
    pub types: Evidence,
    pub values: May,
}

/// What every transfer reads: the thresholds, and the declared types a field read goes through.
pub(crate) struct Context {
    pub thresholds: Thresholds,
    pub decls: Box<[Decl]>,
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

impl Lattice for Product {
    type Edge = Edge;
    type Pair = Pair;
    type Many = Many;
    type Context = Context;

    fn bottom() -> Self {
        Self {
            types: Evidence::NONE,
            values: May::NONE,
        }
    }

    fn join(&mut self, other: &Self) -> bool {
        self.types.join(&other.types) | self.values.join(&other.values)
    }

    /// Only values climb: type claims are finite, so `Peer` carries nothing.
    fn carries(edge: &Edge) -> Carry {
        match edge {
            Edge::Peer
            | Edge::Types
            | Edge::TypeBind
            | Edge::Not
            | Edge::Enter
            | Edge::Exactly(_) => Carry::Nothing,
            Edge::Neg => Carry::Grows,
            Edge::Call(_) | Edge::Bind | Edge::Values | Edge::Field(_) => Carry::Passes,
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
            Pair::Lazy { .. } | Pair::Then | Pair::Else => [Carry::Nothing; 2],
            Pair::Binary(BinaryOp::Arith(_)) => [Carry::Grows; 2],
            Pair::Binary(BinaryOp::Cmp(_)) => [Carry::Nothing; 2],
            Pair::Refine { .. } | Pair::Range => [Carry::Passes; 2],
            Pair::Branch | Pair::Forward | Pair::Outcome | Pair::Argument | Pair::Backedge => {
                [Carry::Passes, Carry::Nothing]
            }
        }
    }

    fn transfer(&self, edge: &Edge, cyclic: bool, cx: &Context) -> Self {
        let types = match *edge {
            Edge::Call(claim) => self.types.imported(claim),
            Edge::Bind | Edge::Types | Edge::TypeBind | Edge::Exactly(_) | Edge::Peer => self.types,
            Edge::Field(name) => self.types.field(name, &cx.decls),
            Edge::Values | Edge::Neg | Edge::Not | Edge::Enter => Evidence::NONE,
        };
        let values = &self.values;
        let values = match *edge {
            Edge::Call(_) => rounded(values, cyclic, cx),
            Edge::Bind | Edge::Values => values.clone(),
            Edge::Types | Edge::TypeBind => May::NONE,
            Edge::Peer => May::NONE,
            Edge::Neg => {
                let Ok(negated) = values.neg();
                negated
            }
            Edge::Not => {
                let Ok(inverted) = values.not();
                inverted
            }
            Edge::Exactly(value) => values.exactly(value),
            Edge::Enter => May::of_unit(values.is_live()),
            Edge::Field(name) => {
                let Ok(field) = values.field(name, &cx.decls);
                field
            }
        };
        Self { types, values }
    }

    fn widens(edge: &Edge) -> bool {
        matches!(edge, Edge::Call(_))
    }

    fn widens_pair(pair: &Pair) -> bool {
        matches!(pair, Pair::Argument | Pair::Backedge)
    }

    fn combine(&self, pair: &Pair, other: &Self, cyclic: bool, cx: &Context) -> Self {
        let types = match *pair {
            Pair::Refine { .. } | Pair::Branch | Pair::Forward => self.types,
            Pair::Outcome => Evidence::NONE,
            Pair::Binary(_)
            | Pair::Lazy { .. }
            | Pair::Then
            | Pair::Else
            | Pair::Argument
            | Pair::Backedge
            | Pair::Range => Evidence::NONE,
        };
        let (values, second) = (&self.values, &other.values);
        let values = match *pair {
            Pair::Binary(op) => {
                let Ok(combined) = May::binary(op, values, second);
                combined
            }
            Pair::Lazy { is_and } => {
                let Ok(combined) = May::lazy(is_and, values, second);
                combined
            }
            Pair::Refine {
                op,
                local_is_lhs,
                sense,
            } => values.refine(op, local_is_lhs, sense, second),
            Pair::Then => May::of_unit(values.bools.may_true() && second.is_live()),
            Pair::Else => May::of_unit(values.bools.may_false() && second.is_live()),
            Pair::Range => May::ints(Ints::range(&values.ints, &second.ints)),
            Pair::Branch | Pair::Forward | Pair::Outcome => {
                if second.is_live() {
                    values.clone()
                } else {
                    May::NONE
                }
            }
            Pair::Argument | Pair::Backedge => {
                if second.is_live() {
                    rounded(values, cyclic, cx)
                } else {
                    May::NONE
                }
            }
        };
        Self { types, values }
    }

    /// The value made is a fact of its own type, so only the fields' values flow.
    fn combine_many(&self, many: &Many, others: &[&Self], cyclic: bool, cx: &Context) -> Self {
        let Many::Make(decl) = *many;
        let fields = std::iter::once(self)
            .chain(others.iter().copied())
            .map(|field| rounded(&field.values, cyclic, cx))
            .collect();
        Self {
            types: Evidence::NONE,
            values: May::make(decl, fields),
        }
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

    fn values(values: May) -> Product {
        Product {
            types: Evidence::NONE,
            values,
        }
    }

    #[test]
    fn evidence_is_seven_words_and_an_edge_two() {
        assert_eq!(size_of::<Evidence>(), 28);
        assert_eq!(size_of::<Option<Claim>>(), 4);
        assert_eq!(size_of::<Edge>(), 8);
    }

    #[test]
    fn transfers_derive_and_only_cyclic_interprocedural_flows_round() {
        let cx = Context {
            thresholds: [15, 2].map(Int::from).into_iter().collect(),
            decls: Box::new([]),
        };
        let a = values(band(4, 13));
        let b = values(May::int(&2.into()));
        let edge = Pair::Binary(BinaryOp::Arith(ArithOp::Mul));
        assert_eq!(a.combine(&edge, &b, false, &cx).values, band(8, 26));
        let edge = Pair::Binary(BinaryOp::Cmp(CmpOp::Lt));
        assert_eq!(
            a.combine(&edge, &b, false, &cx).values.bools,
            Bools::from(false)
        );
        let edge = Pair::Lazy { is_and: true };
        assert_eq!(
            values(May::bool(false))
                .combine(&edge, &Product::bottom(), false, &cx)
                .values
                .bools,
            Bools::from(false)
        );
        assert_eq!(
            values(May::bool(true))
                .transfer(&Edge::Not, false, &cx)
                .values
                .bools,
            Bools::from(false)
        );
        let call = Edge::Call(Claim::local(0));
        assert_eq!(a.transfer(&call, false, &cx).values, a.values);
        assert_eq!(a.transfer(&call, true, &cx).values, band(3, 14));
        let live = values(May::unit());
        assert_eq!(
            a.combine(&Pair::Argument, &live, true, &cx).values,
            band(3, 14)
        );
        assert_eq!(a.transfer(&Edge::Values, true, &cx).values, a.values);
        assert_eq!(a.transfer(&Edge::Peer, false, &cx).values, May::NONE);
    }

    #[test]
    fn contexts_gate_branches_arguments_and_entries() {
        let cx = Context {
            thresholds: Thresholds::default(),
            decls: Box::new([]),
        };
        let live = values(May::unit());
        let dead = Product::bottom();
        let cond = values(May::bool(false));
        assert_eq!(cond.combine(&Pair::Then, &live, false, &cx), dead);
        assert_eq!(cond.combine(&Pair::Else, &live, false, &cx), live);
        assert_eq!(cond.combine(&Pair::Else, &dead, false, &cx), dead);
        let value = values(May::int(&3.into()));
        assert_eq!(value.combine(&Pair::Branch, &live, false, &cx), value);
        assert_eq!(value.combine(&Pair::Branch, &dead, false, &cx), dead);
        assert_eq!(value.combine(&Pair::Argument, &dead, false, &cx), dead);
        assert_eq!(value.combine(&Pair::Argument, &live, false, &cx), value);
        assert_eq!(live.transfer(&Edge::Enter, false, &cx), live);
        assert_eq!(dead.transfer(&Edge::Enter, false, &cx), dead);
    }

    #[test]
    fn types_cross_aliasing_edges_and_are_relabeled_by_calls() {
        let cx = Context {
            thresholds: Thresholds::default(),
            decls: Box::new([]),
        };
        let int = Product {
            types: Evidence::single(Ty::INT, Claim::local(3)),
            values: May::int(&1.into()),
        };
        let live = values(May::unit());
        for edge in [
            Edge::Bind,
            Edge::Types,
            Edge::TypeBind,
            Edge::Exactly(true),
            Edge::Peer,
        ] {
            assert_eq!(int.transfer(&edge, false, &cx).types, int.types);
        }
        assert_eq!(Product::carries(&Edge::Types), Carry::Nothing);
        assert_eq!(int.transfer(&Edge::Types, false, &cx).values, May::NONE);
        assert_eq!(int.transfer(&Edge::TypeBind, false, &cx).values, May::NONE);
        assert_eq!(
            int.combine(&Pair::Branch, &Product::bottom(), false, &cx)
                .types,
            int.types
        );
        for edge in [Edge::Values, Edge::Neg, Edge::Enter] {
            assert_eq!(int.transfer(&edge, false, &cx).types, Evidence::NONE);
        }
        assert_eq!(
            int.combine(&Pair::Argument, &live, false, &cx).types,
            Evidence::NONE
        );
        assert_eq!(
            int.combine(&Pair::Outcome, &live, false, &cx).types,
            Evidence::NONE
        );
        let called = int.transfer(&Edge::Call(Claim::local(7)), false, &cx);
        assert_eq!(called.types.ty(), Some(Ty::INT));
        assert!(called.types.claims()[0].1.is_imported());
        assert_eq!(called.types.claims()[0].1.index(), 7);
    }

    #[test]
    fn a_boolean_read_is_narrowed_to_its_guard() {
        let flag = values(May::bools(Bools::BOTH));
        let cx = Context {
            thresholds: Thresholds::default(),
            decls: Box::new([]),
        };
        assert_eq!(
            flag.transfer(&Edge::Exactly(false), false, &cx)
                .values
                .bools,
            Bools::from(false)
        );
    }
}
