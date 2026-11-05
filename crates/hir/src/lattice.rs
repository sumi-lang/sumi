//! The [`Lattice`] the solver carries: per class, the best claim of each type and the [`May`]
//! values, crossing the same [`Edge`]s, [`Pair`]s, and [`Many`]s. Calls, arguments, and loop
//! backedges round cyclic integer flows to thresholds, so every ascending chain is finite.

use std::num::NonZeroU32;

use sumi_graph::{
    BinaryOp, Case, CmpOp, Decl, DeclId, Domain, FieldName, Ints, May, Thresholds, Ty, TyKind,
    Unions,
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
#[derive(Debug, PartialEq, Eq)]
pub(crate) struct Evidence {
    /// By scalar, in `Ty::SCALARS` order.
    scalars: [Option<Claim>; Ty::SCALARS.len()],
    /// The best claim of each declared type or union: two inline, since a class rarely claims
    /// one, and the rest behind a thin pointer, since every one is a member of the union the class
    /// resolves to.
    decls: [Option<(Ty, Claim)>; 2],
    more: Option<Box<MoreClaims>>,
}

/// Behind a thin pointer so the evidence stays small.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct MoreClaims(Vec<(Ty, Claim)>);

impl Clone for Evidence {
    #[inline(always)]
    fn clone(&self) -> Self {
        Self {
            scalars: self.scalars,
            decls: self.decls,
            more: self.more.clone(),
        }
    }
}

fn scalar_slot(ty: Ty) -> Result<usize, Ty> {
    match ty.kind() {
        TyKind::Int => Ok(0),
        TyKind::Bool => Ok(1),
        TyKind::Unit => Ok(2),
        TyKind::Decl(_) | TyKind::Union(_) => Err(ty),
    }
}

impl Evidence {
    pub const NONE: Self = Self {
        scalars: [None; Ty::SCALARS.len()],
        decls: [None; 2],
        more: None,
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
            for (decl, claim) in other.decl_claims() {
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
    fn offer(&mut self, decl: Ty, claim: Claim) -> bool {
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
        let more = &mut self.more.get_or_insert_with(Box::default).0;
        match more.iter_mut().find(|(held, _)| *held == decl) {
            Some((_, best)) => {
                if claim < *best {
                    *best = claim;
                    return true;
                }
                false
            }
            None => {
                more.push((decl, claim));
                true
            }
        }
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
            more: self.more.as_ref().map(|more| {
                Box::new(MoreClaims(
                    more.0
                        .iter()
                        .map(|&(decl, claim)| (decl, relabel(claim)))
                        .collect(),
                ))
            }),
        }
    }

    /// What a read of field `name` delivers: each claim of a declared type with the field becomes
    /// a claim of the field's type, and the rest, a union among them, claim nothing, which the
    /// demand on the read reports.
    pub fn field(&self, name: FieldName, decls: &[Decl]) -> Self {
        let mut evidence = Self::NONE;
        if self.is_unknown() {
            evidence.scalars[0] = Some(UNKNOWN);
        }
        for (ty, claim) in self.decl_claims() {
            let Some(decl) = ty.as_decl() else {
                continue;
            };
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

    fn decl_claims(&self) -> impl Iterator<Item = (Ty, Claim)> + '_ {
        let more = self
            .more
            .as_deref()
            .map_or(&[][..], |more| more.0.as_slice());
        self.decls.iter().flatten().chain(more).copied()
    }

    fn entries(&self) -> impl Iterator<Item = (Ty, Claim)> + '_ {
        let scalars = Ty::SCALARS
            .iter()
            .zip(&self.scalars)
            .filter_map(|(ty, claim)| claim.map(|claim| (*ty, claim)));
        scalars.chain(self.decl_claims())
    }

    /// The types the class resolves among: demands count only where nothing else claims a type.
    fn types(&self) -> impl Iterator<Item = (Ty, Claim)> + '_ {
        let demands_only = self
            .entries()
            .all(|(_, claim)| claim == UNKNOWN || claim.is_demanded());
        self.entries()
            .filter(move |&(_, claim)| claim != UNKNOWN && (demands_only || !claim.is_demanded()))
    }

    /// The type claimed: the one claim, or the union of claims that are all of declared types,
    /// which `unions` interns. None for a class a hole decided or a conflict.
    #[inline]
    pub fn ty(&self, unions: &mut Unions) -> Option<Ty> {
        if self.is_unknown() {
            return None;
        }
        if self.decls[0].is_none() {
            let mut scalars = self
                .scalars
                .iter()
                .enumerate()
                .filter(|(_, claim)| claim.is_some());
            if let Some((slot, _)) = scalars.next()
                && scalars.next().is_none()
            {
                return Some(Ty::SCALARS[slot]);
            }
        }
        let mut types = self.types();
        let (ty, _) = types.next()?;
        if types.next().is_none() {
            return Some(ty);
        }
        if !self.types().all(|(ty, _)| ty.is_declared()) {
            return None;
        }
        let mut members: Vec<DeclId> = Vec::new();
        for (ty, _) in self.types() {
            match ty.kind() {
                TyKind::Decl(decl) => members.push(decl),
                TyKind::Union(id) => members.extend_from_slice(unions.get(id)),
                TyKind::Int | TyKind::Bool | TyKind::Unit => unreachable!("declared types only"),
            }
        }
        let union = unions.intern(members.iter().copied());
        Some(union.map_or_else(|| Ty::decl(members[0]), Ty::union))
    }

    /// Never for a class a hole decided: the claims beside the unknown are not a disagreement.
    /// Claims of declared types alone are not one either: they are a union.
    pub fn is_conflict(&self) -> bool {
        !self.is_unknown()
            && self.types().count() > 1
            && !self.types().all(|(ty, _)| ty.is_declared())
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
    /// An arm's binding: the values of the type among the scrutinee's.
    Narrow(Ty),
}

impl Edge {
    /// Whether the consumer is one class with its provider in the replay.
    pub fn aliases(self) -> bool {
        matches!(self, Self::Bind | Self::TypeBind | Self::Exactly(_))
    }

    /// Whether the provider's type claims reach the consumer.
    pub fn delivers_types(self) -> bool {
        match self {
            Self::Call(_)
            | Self::Bind
            | Self::Types
            | Self::TypeBind
            | Self::Exactly(_)
            | Self::Peer
            | Self::Field(_) => true,
            Self::Values | Self::Neg | Self::Not | Self::Enter | Self::Narrow(_) => false,
        }
    }

    /// Whether the consumer's values depend on the provider's.
    pub fn delivers_values(self) -> bool {
        !matches!(self, Self::Types | Self::TypeBind | Self::Peer)
    }
}

/// A flow from two providers. The second of `Binary`, `Lazy`, and `Refine` is the other operand;
/// of `Branch`, `Forward`, `Arm`, and `Argument`, the context that gates them.
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
    /// A boolean arm context from its condition and parent: live where the condition may be the
    /// boolean.
    Bool(bool),
    /// An arm context from its scrutinee and parent; `Context::cases[index]` excludes earlier arms.
    Arm(u16),
    Argument,
    Backedge,
    Range,
}

impl Pair {
    /// Whether the consumer is one class with its first provider in the replay.
    pub fn aliases(self) -> bool {
        matches!(self, Self::Refine { .. } | Self::Forward)
    }

    /// Whether the first provider's type claims reach the consumer; every pair delivers values.
    pub fn delivers_types(self) -> bool {
        matches!(self, Self::Refine { .. } | Self::Branch | Self::Forward)
    }
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

/// Type claims are finite and never widen, so no flow carries, no component grows, and nothing
/// narrows.
impl Lattice for Evidence {
    type Edge = Edge;
    type Pair = Pair;
    type Many = Many;
    type Context = Context;

    const WIDENS: bool = false;

    fn bottom() -> Self {
        Self::NONE
    }

    fn join(&mut self, other: &Self) -> bool {
        Evidence::join(self, other)
    }

    fn carries(_: &Edge) -> Carry {
        Carry::Nothing
    }

    fn carries_many(_: &Many) -> Carry {
        Carry::Nothing
    }

    fn carries_pair(_: &Pair) -> [Carry; 2] {
        [Carry::Nothing; 2]
    }

    fn transfer(&self, edge: &Edge, _: bool, cx: &Context) -> Self {
        match *edge {
            Edge::Call(claim) => self.imported(claim),
            Edge::Bind | Edge::Types | Edge::TypeBind | Edge::Exactly(_) | Edge::Peer => {
                self.clone()
            }
            Edge::Field(name) => self.field(name, &cx.decls),
            Edge::Values | Edge::Neg | Edge::Not | Edge::Enter | Edge::Narrow(_) => Self::NONE,
        }
    }

    fn widens(_: &Edge) -> bool {
        false
    }

    fn widens_pair(_: &Pair) -> bool {
        false
    }

    fn combine(&self, pair: &Pair, _: &Self, _: bool, _: &Context) -> Self {
        match *pair {
            Pair::Refine { .. } | Pair::Branch | Pair::Forward => self.clone(),
            Pair::Outcome
            | Pair::Binary(_)
            | Pair::Lazy { .. }
            | Pair::Bool(_)
            | Pair::Arm(_)
            | Pair::Argument
            | Pair::Backedge
            | Pair::Range => Self::NONE,
        }
    }

    fn combine_many(&self, _: &Many, _: &[&Self], _: bool, _: &Context) -> Self {
        Self::NONE
    }

    fn narrow(&mut self, _: &Self) -> bool {
        false
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
            Edge::Peer
            | Edge::Types
            | Edge::TypeBind
            | Edge::Not
            | Edge::Enter
            | Edge::Exactly(_) => Carry::Nothing,
            Edge::Neg => Carry::Grows,
            Edge::Call(_) | Edge::Bind | Edge::Values | Edge::Field(_) | Edge::Narrow(_) => {
                Carry::Passes
            }
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
            Pair::Branch | Pair::Forward | Pair::Outcome | Pair::Argument | Pair::Backedge => {
                [Carry::Passes, Carry::Nothing]
            }
        }
    }

    fn transfer(&self, edge: &Edge, cyclic: bool, cx: &Context) -> Self {
        match *edge {
            Edge::Call(_) => rounded(self, cyclic, cx),
            Edge::Bind | Edge::Values => self.clone(),
            Edge::Types | Edge::TypeBind | Edge::Peer => Self::NONE,
            Edge::Neg => {
                let Ok(negated) = self.neg();
                negated
            }
            Edge::Not => {
                let Ok(inverted) = self.not();
                inverted
            }
            Edge::Exactly(value) => self.exactly(value),
            Edge::Enter => Self::of_unit(self.is_live()),
            Edge::Field(name) => {
                let Ok(field) = self.field(name, &cx.decls, &cx.unions);
                field
            }
            Edge::Narrow(ty) => self.narrow(ty, &cx.unions),
        }
    }

    fn widens(edge: &Edge) -> bool {
        matches!(edge, Edge::Call(_))
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
            Pair::Branch | Pair::Forward | Pair::Outcome => {
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

    /// The value made is a fact of its own type, so only the fields' values flow.
    fn combine_many(&self, many: &Many, others: &[&Self], cyclic: bool, cx: &Context) -> Self {
        let Many::Make(decl) = *many;
        let fields = std::iter::once(self)
            .chain(others.iter().copied())
            .map(|field| rounded(field, cyclic, cx))
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
    fn evidence_is_five_words_and_an_edge_two() {
        assert_eq!(size_of::<Evidence>(), 40);
        assert_eq!(size_of::<Option<Claim>>(), 4);
        assert_eq!(size_of::<Edge>(), 8);
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
        let call = Edge::Call(Claim::local(0));
        assert_eq!(a.transfer(&call, false, &cx), a);
        assert_eq!(a.transfer(&call, true, &cx), band(3, 14));
        let live = May::unit();
        assert_eq!(a.combine(&Pair::Argument, &live, true, &cx), band(3, 14));
        assert_eq!(a.transfer(&Edge::Values, true, &cx), a);
        assert_eq!(a.transfer(&Edge::Peer, false, &cx), May::NONE);
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
    fn types_cross_aliasing_edges_and_are_relabeled_by_calls() {
        let cx = Context {
            thresholds: Thresholds::default(),
            decls: Box::new([]),
            unions: Unions::new(),
            cases: Box::new([]),
        };
        let int = Evidence::single(Ty::INT, Claim::local(3));
        let one = May::int(&1.into());
        for edge in [
            Edge::Bind,
            Edge::Types,
            Edge::TypeBind,
            Edge::Exactly(true),
            Edge::Peer,
        ] {
            assert!(edge.delivers_types());
            assert_eq!(int.transfer(&edge, false, &cx), int);
        }
        assert_eq!(<May as Lattice>::carries(&Edge::Types), Carry::Nothing);
        assert!(!Edge::Types.delivers_values());
        assert!(!Edge::TypeBind.delivers_values());
        assert_eq!(one.transfer(&Edge::Types, false, &cx), May::NONE);
        assert_eq!(int.combine(&Pair::Branch, &Evidence::NONE, false, &cx), int);
        for edge in [Edge::Values, Edge::Neg, Edge::Enter] {
            assert!(!edge.delivers_types());
            assert_eq!(int.transfer(&edge, false, &cx), Evidence::NONE);
        }
        assert!(!Pair::Argument.delivers_types());
        assert!(!Pair::Outcome.delivers_types());
        assert_eq!(
            int.combine(&Pair::Argument, &int, false, &cx),
            Evidence::NONE
        );
        let called = int.transfer(&Edge::Call(Claim::local(7)), false, &cx);
        assert_eq!(called.ty(&mut Unions::new()), Some(Ty::INT));
        assert!(called.claims()[0].1.is_imported());
        assert_eq!(called.claims()[0].1.index(), 7);
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
