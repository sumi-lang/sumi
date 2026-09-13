//! May-values: the set of values that may reach a class, as the second
//! component of the evidence beside the type claims.
//!
//! A [`May`] is a product of one set per scalar type: a band of integers
//! over ℤ ∪ {±∞} with an optional hole at zero, a set of booleans, and a
//! unit bit. A well-typed class populates one of them, and a class with none
//! populated has no values: it is unreachable, or nothing flows into it.
//! Reachability is therefore not a separate bit: a context class, opened
//! for a branch or the right operand of a lazy operator, is a unit-valued
//! class that is live exactly when that point can run.
//!
//! Values arrive by flows only. A literal and a known-unit class are facts;
//! everything else is derived along a [`RangeEdge`] from one or two
//! providers. Hull is the join, and a recursion would climb forever, so an
//! edge that closes a cycle in the call graph rounds its endpoints to the
//! program's [`Thresholds`], which keeps every ascending chain finite
//! without a widening operator in the solver.

use std::cmp::Ordering;
use std::fmt;

use sumi_syntax::NodeIdx;

use crate::solver::Lattice;
use crate::{BinaryOp, Int, Ty};

/// An endpoint over ℤ ∪ {±∞}. Ordered as the extended integers are.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Bound {
    NegInf,
    Finite(Int),
    PosInf,
}

impl Bound {
    fn finite(value: i64) -> Self {
        Self::Finite(value.into())
    }

    fn zero() -> Self {
        Self::finite(0)
    }

    fn sign(&self) -> Ordering {
        match self {
            Self::NegInf => Ordering::Less,
            Self::Finite(value) => value.cmp(&Int::from(0)),
            Self::PosInf => Ordering::Greater,
        }
    }

    fn neg(&self) -> Self {
        match self {
            Self::NegInf => Self::PosInf,
            Self::Finite(value) => Self::Finite(-value),
            Self::PosInf => Self::NegInf,
        }
    }

    /// Never asked to add opposite infinities: every use adds two lower or
    /// two upper endpoints.
    fn add(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Finite(a), Self::Finite(b)) => Self::Finite(a + b),
            (Self::NegInf, Self::PosInf) | (Self::PosInf, Self::NegInf) => {
                unreachable!("endpoints of one side never mix infinities")
            }
            (Self::NegInf, _) | (_, Self::NegInf) => Self::NegInf,
            (Self::PosInf, _) | (_, Self::PosInf) => Self::PosInf,
        }
    }

    fn sub(&self, other: &Self) -> Self {
        self.add(&other.neg())
    }

    fn succ(&self) -> Self {
        self.add(&Self::finite(1))
    }

    fn pred(&self) -> Self {
        self.sub(&Self::finite(1))
    }

    /// With `0 · ±∞ = 0`, which is what a hull of products needs.
    fn mul(&self, other: &Self) -> Self {
        let sign = self.sign().then(Ordering::Equal);
        match (self, other) {
            (Self::Finite(a), Self::Finite(b)) => Self::Finite(a * b),
            _ if self.sign() == Ordering::Equal || other.sign() == Ordering::Equal => Self::zero(),
            _ => {
                let positive =
                    (self.sign() == Ordering::Greater) == (other.sign() == Ordering::Greater);
                let _ = sign;
                if positive { Self::PosInf } else { Self::NegInf }
            }
        }
    }

    /// Truncating division by a non-zero `other`. An infinite dividend
    /// stays infinite with the combined sign; a finite one over an infinite
    /// divisor is zero.
    fn div(&self, other: &Self) -> Self {
        debug_assert_ne!(other.sign(), Ordering::Equal);
        match (self, other) {
            (Self::Finite(a), Self::Finite(b)) => {
                Self::Finite(a.checked_div(b).expect("a non-zero divisor"))
            }
            (Self::Finite(_), _) => Self::zero(),
            _ => {
                let positive =
                    (self.sign() == Ordering::Greater) == (other.sign() == Ordering::Greater);
                if positive { Self::PosInf } else { Self::NegInf }
            }
        }
    }

    fn abs(&self) -> Self {
        if self.sign() == Ordering::Less {
            self.neg()
        } else {
            self.clone()
        }
    }

    fn is_finite(&self) -> bool {
        matches!(self, Self::Finite(_))
    }
}

impl fmt::Display for Bound {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NegInf => f.write_str("-∞"),
            Self::Finite(value) => write!(f, "{value}"),
            Self::PosInf => f.write_str("+∞"),
        }
    }
}

/// The integers that may reach a class: nothing, or a band with an optional
/// hole at zero. The hole is canonical: it is set only when `lo < 0 < hi`,
/// and a zero at an endpoint is removed by moving the endpoint, so equal
/// sets have equal representations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ints {
    Empty,
    Band { lo: Bound, hi: Bound, hole: bool },
}

impl Ints {
    pub fn point(value: Int) -> Self {
        let bound = Bound::Finite(value);
        Self::Band {
            lo: bound.clone(),
            hi: bound,
            hole: false,
        }
    }

    /// Every integer: what an input from outside the program would be.
    pub fn all() -> Self {
        Self::Band {
            lo: Bound::NegInf,
            hi: Bound::PosInf,
            hole: false,
        }
    }

    /// The canonical band, or nothing when it is empty.
    fn band(mut lo: Bound, mut hi: Bound, hole: bool) -> Self {
        if hole {
            if lo.sign() == Ordering::Equal {
                lo = lo.succ();
            }
            if hi.sign() == Ordering::Equal {
                hi = hi.pred();
            }
        }
        if lo > hi {
            return Self::Empty;
        }
        let hole = hole && lo.sign() == Ordering::Less && hi.sign() == Ordering::Greater;
        Self::Band { lo, hi, hole }
    }

    fn parts(&self) -> Option<(&Bound, &Bound, bool)> {
        match self {
            Self::Empty => None,
            Self::Band { lo, hi, hole } => Some((lo, hi, *hole)),
        }
    }

    pub fn is_empty(&self) -> bool {
        matches!(self, Self::Empty)
    }

    pub fn contains_zero(&self) -> bool {
        self.parts().is_some_and(|(lo, hi, hole)| {
            !hole && lo.sign() != Ordering::Greater && hi.sign() != Ordering::Less
        })
    }

    /// Exactly `[0, 0]`.
    pub fn is_zero(&self) -> bool {
        self.parts()
            .is_some_and(|(lo, hi, _)| lo.sign() == Ordering::Equal && hi.sign() == Ordering::Equal)
    }

    fn is_point(&self) -> bool {
        self.parts().is_some_and(|(lo, hi, _)| lo == hi)
    }

    /// The endpoints, when the set is bounded on that side.
    pub fn lo(&self) -> Option<&Int> {
        match self.parts()?.0 {
            Bound::Finite(value) => Some(value),
            _ => None,
        }
    }

    pub fn hi(&self) -> Option<&Int> {
        match self.parts()?.1 {
            Bound::Finite(value) => Some(value),
            _ => None,
        }
    }

    /// The smallest band containing both. Reports growth.
    pub fn join(&mut self, other: &Self) -> bool {
        let Some((lo2, hi2, _)) = other.parts() else {
            return false;
        };
        let joined = match self.parts() {
            None => other.clone(),
            Some((lo1, hi1, _)) => {
                let hole = !self.contains_zero() && !other.contains_zero();
                Self::band(lo1.min(lo2).clone(), hi1.max(hi2).clone(), hole)
            }
        };
        let grew = joined != *self;
        *self = joined;
        grew
    }

    fn intersect(&self, other: &Self) -> Self {
        match (self.parts(), other.parts()) {
            (Some((lo1, hi1, hole1)), Some((lo2, hi2, hole2))) => {
                Self::band(lo1.max(lo2).clone(), hi1.min(hi2).clone(), hole1 || hole2)
            }
            _ => Self::Empty,
        }
    }

    fn without(&self, point: &Bound) -> Self {
        let Some((lo, hi, hole)) = self.parts() else {
            return Self::Empty;
        };
        if lo == point {
            Self::band(lo.succ(), hi.clone(), hole)
        } else if hi == point {
            Self::band(lo.clone(), hi.pred(), hole)
        } else if point.sign() == Ordering::Equal {
            Self::band(lo.clone(), hi.clone(), true)
        } else {
            self.clone()
        }
    }

    fn neg(&self) -> Self {
        match self.parts() {
            None => Self::Empty,
            Some((lo, hi, hole)) => Self::band(hi.neg(), lo.neg(), hole),
        }
    }

    pub(crate) fn add(&self, other: &Self) -> Self {
        match (self.parts(), other.parts()) {
            (Some((lo1, hi1, _)), Some((lo2, hi2, _))) => {
                Self::band(lo1.add(lo2), hi1.add(hi2), false)
            }
            _ => Self::Empty,
        }
    }

    pub(crate) fn sub(&self, other: &Self) -> Self {
        match (self.parts(), other.parts()) {
            (Some((lo1, hi1, _)), Some((lo2, hi2, _))) => {
                Self::band(lo1.sub(hi2), hi1.sub(lo2), false)
            }
            _ => Self::Empty,
        }
    }

    fn mul(&self, other: &Self) -> Self {
        match (self.parts(), other.parts()) {
            (Some((lo1, hi1, _)), Some((lo2, hi2, _))) => {
                let corners = [lo1.mul(lo2), lo1.mul(hi2), hi1.mul(lo2), hi1.mul(hi2)];
                let lo = corners.iter().min().unwrap().clone();
                let hi = corners.iter().max().unwrap().clone();
                // A product of non-zeros is non-zero over ℤ.
                Self::band(lo, hi, !self.contains_zero() && !other.contains_zero())
            }
            _ => Self::Empty,
        }
    }

    /// The divisor's non-zero halves, each a band with one sign.
    fn halves(&self) -> Vec<(Bound, Bound)> {
        let Some((lo, hi, _)) = self.parts() else {
            return Vec::new();
        };
        let mut halves = Vec::with_capacity(2);
        if lo.sign() == Ordering::Less {
            halves.push((lo.clone(), hi.clone().min(Bound::finite(-1))));
        }
        if hi.sign() == Ordering::Greater {
            halves.push((lo.clone().max(Bound::finite(1)), hi.clone()));
        }
        halves
    }

    /// Truncating quotient: exact on the corners of each non-zero half of
    /// the divisor, so an error at one division does not cascade.
    fn div(&self, other: &Self) -> Self {
        let Some((lo1, hi1, _)) = self.parts() else {
            return Self::Empty;
        };
        let mut result = Self::Empty;
        for (lo2, hi2) in other.halves() {
            let corners = [lo1.div(&lo2), lo1.div(&hi2), hi1.div(&lo2), hi1.div(&hi2)];
            let lo = corners.iter().min().unwrap().clone();
            let hi = corners.iter().max().unwrap().clone();
            result.join(&Self::band(lo, hi, false));
        }
        result
    }

    /// Truncating remainder: the dividend's sign, bounded by the largest
    /// divisor magnitude minus one.
    fn rem(&self, other: &Self) -> Self {
        let (Some((lo1, hi1, _)), Some((lo2, hi2, _))) = (self.parts(), other.parts()) else {
            return Self::Empty;
        };
        let magnitude = lo2.abs().max(hi2.abs());
        if magnitude.sign() == Ordering::Equal {
            return Self::Empty;
        }
        let limit = magnitude.pred();
        let lo = if lo1.sign() != Ordering::Less {
            Bound::zero()
        } else {
            lo1.clone().max(limit.neg())
        };
        let hi = if hi1.sign() != Ordering::Greater {
            Bound::zero()
        } else {
            hi1.clone().min(limit)
        };
        Self::band(lo, hi, false)
    }

    /// The booleans `self op other` may be.
    fn compare(&self, op: BinaryOp, other: &Self) -> Bools {
        let (Some((lo1, hi1, _)), Some((lo2, hi2, _))) = (self.parts(), other.parts()) else {
            return Bools::EMPTY;
        };
        let (may_true, may_false) = match op {
            BinaryOp::Lt => (lo1 < hi2, hi1 >= lo2),
            BinaryOp::Le => (lo1 <= hi2, hi1 > lo2),
            BinaryOp::Gt => (hi1 > lo2, lo1 <= hi2),
            BinaryOp::Ge => (hi1 >= lo2, lo1 < hi2),
            BinaryOp::Eq | BinaryOp::Ne => {
                let equal = !self.intersect(other).is_empty();
                let unequal = !(self.is_point() && self == other);
                if op == BinaryOp::Eq {
                    (equal, unequal)
                } else {
                    (unequal, equal)
                }
            }
            _ => unreachable!("a comparison"),
        };
        Bools::of(may_true, may_false)
    }

    /// `self` narrowed by `self op other` holding, with `self` on the left.
    fn refine(&self, op: BinaryOp, other: &Self) -> Self {
        let Some((lo, hi, hole)) = self.parts() else {
            return Self::Empty;
        };
        let Some((lo2, hi2, _)) = other.parts() else {
            return Self::Empty;
        };
        match op {
            BinaryOp::Lt => Self::band(lo.clone(), hi.clone().min(hi2.pred()), hole),
            BinaryOp::Le => Self::band(lo.clone(), hi.clone().min(hi2.clone()), hole),
            BinaryOp::Gt => Self::band(lo.clone().max(lo2.succ()), hi.clone(), hole),
            BinaryOp::Ge => Self::band(lo.clone().max(lo2.clone()), hi.clone(), hole),
            BinaryOp::Eq => self.intersect(other),
            BinaryOp::Ne => {
                if other.is_point() {
                    self.without(lo2)
                } else {
                    self.clone()
                }
            }
            _ => unreachable!("a comparison"),
        }
    }

    /// Endpoints moved outward to the thresholds; a point is left exact.
    fn round(&self, thresholds: &Thresholds) -> Self {
        let Some((lo, hi, hole)) = self.parts() else {
            return Self::Empty;
        };
        if lo == hi {
            return self.clone();
        }
        let lo = match lo {
            Bound::Finite(value) => thresholds.below(value),
            _ => lo.clone(),
        };
        let hi = match hi {
            Bound::Finite(value) => thresholds.above(value),
            _ => hi.clone(),
        };
        Self::band(lo, hi, hole)
    }
}

impl fmt::Display for Ints {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Empty => f.write_str("∅"),
            Self::Band { lo, hi, hole } => {
                let open = if lo.is_finite() { '[' } else { '(' };
                let close = if hi.is_finite() { ']' } else { ')' };
                write!(f, "{open}{lo}, {hi}{close}")?;
                if *hole {
                    f.write_str(" \\ 0")?;
                }
                Ok(())
            }
        }
    }
}

/// The booleans that may reach a class.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Bools(u8);

impl Bools {
    pub const EMPTY: Self = Self(0);
    const FALSE: Self = Self(1);
    const TRUE: Self = Self(2);
    pub const BOTH: Self = Self(3);

    pub fn single(value: bool) -> Self {
        if value { Self::TRUE } else { Self::FALSE }
    }

    fn of(may_true: bool, may_false: bool) -> Self {
        Self(u8::from(may_false) | (u8::from(may_true) << 1))
    }

    pub fn is_empty(self) -> bool {
        self.0 == 0
    }

    pub fn may_true(self) -> bool {
        self.0 & Self::TRUE.0 != 0
    }

    pub fn may_false(self) -> bool {
        self.0 & Self::FALSE.0 != 0
    }

    fn not(self) -> Self {
        Self::of(self.may_false(), self.may_true())
    }

    /// `self && other`: the right operand runs only when the left is true,
    /// so an empty right side still leaves `false` from the left.
    fn and(self, other: Self) -> Self {
        Self::of(
            self.may_true() && other.may_true(),
            self.may_false() || (self.may_true() && other.may_false()),
        )
    }

    /// `self || other`, likewise.
    fn or(self, other: Self) -> Self {
        Self::of(
            self.may_true() || (self.may_false() && other.may_true()),
            self.may_false() && other.may_false(),
        )
    }

    fn eq(self, other: Self) -> Self {
        if self.is_empty() || other.is_empty() {
            return Self::EMPTY;
        }
        let same = self.0 & other.0 != 0;
        let differ =
            (self.may_true() && other.may_false()) || (self.may_false() && other.may_true());
        Self::of(same, differ)
    }

    fn intersect(self, other: Self) -> Self {
        Self(self.0 & other.0)
    }

    fn join(&mut self, other: Self) -> bool {
        let before = self.0;
        self.0 |= other.0;
        before != self.0
    }
}

impl fmt::Display for Bools {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match (self.may_true(), self.may_false()) {
            (false, false) => f.write_str("∅"),
            (true, false) => f.write_str("{true}"),
            (false, true) => f.write_str("{false}"),
            (true, true) => f.write_str("{true, false}"),
        }
    }
}

/// The values that may reach a class, one set per scalar type. Empty in
/// every component means no value ever does.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct May {
    pub ints: Ints,
    pub bools: Bools,
    pub unit: bool,
}

impl May {
    pub fn int(value: Int) -> Self {
        Self::ints(Ints::point(value))
    }

    pub fn bool(value: bool) -> Self {
        Self::bools(Bools::single(value))
    }

    pub fn unit() -> Self {
        Self::of_unit(true)
    }

    fn ints(ints: Ints) -> Self {
        Self {
            ints,
            bools: Bools::EMPTY,
            unit: false,
        }
    }

    fn bools(bools: Bools) -> Self {
        Self {
            ints: Ints::Empty,
            bools,
            unit: false,
        }
    }

    fn of_unit(unit: bool) -> Self {
        Self {
            ints: Ints::Empty,
            bools: Bools::EMPTY,
            unit,
        }
    }

    /// Whether any value at all may reach the class.
    pub fn live(&self) -> bool {
        !self.ints.is_empty() || !self.bools.is_empty() || self.unit
    }

    /// `self` narrowed by a comparison with `other` holding, from the
    /// local's side of it.
    fn refine(&self, op: BinaryOp, local_is_lhs: bool, sense: bool, other: &Self) -> Self {
        let op = if local_is_lhs { op } else { flip(op) };
        let op = if sense { op } else { negate(op) };
        let bools = match op {
            BinaryOp::Eq => self.bools.intersect(other.bools),
            BinaryOp::Ne
                if other.bools == Bools::single(true) || other.bools == Bools::single(false) =>
            {
                self.bools.intersect(other.bools.not())
            }
            _ => self.bools,
        };
        Self {
            ints: self.ints.refine(op, &other.ints),
            bools,
            unit: false,
        }
    }

    /// The set as a type reads it, for snapshots and reports.
    pub fn shown(&self, ty: Ty) -> Shown<'_> {
        Shown(self, ty)
    }
}

/// `a op b` read as `b op' a`.
fn flip(op: BinaryOp) -> BinaryOp {
    match op {
        BinaryOp::Lt => BinaryOp::Gt,
        BinaryOp::Le => BinaryOp::Ge,
        BinaryOp::Gt => BinaryOp::Lt,
        BinaryOp::Ge => BinaryOp::Le,
        other => other,
    }
}

/// The comparison that holds when `op` does not.
fn negate(op: BinaryOp) -> BinaryOp {
    match op {
        BinaryOp::Lt => BinaryOp::Ge,
        BinaryOp::Le => BinaryOp::Gt,
        BinaryOp::Gt => BinaryOp::Le,
        BinaryOp::Ge => BinaryOp::Lt,
        BinaryOp::Eq => BinaryOp::Ne,
        BinaryOp::Ne => BinaryOp::Eq,
        other => other,
    }
}

/// A [`May`] displayed as one type's set.
pub struct Shown<'a>(&'a May, Ty);

impl fmt::Display for Shown<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.1 {
            Ty::Int => write!(f, "{}", self.0.ints),
            Ty::Bool => write!(f, "{}", self.0.bools),
            Ty::Unit => f.write_str(if self.0.unit { "unit" } else { "∅" }),
        }
    }
}

/// The finite set an endpoint may round to: the file's constants and their
/// neighbors, always including `-1`, `0`, and `1`, so a band keeps its sign
/// however far it travels around a recursion.
#[derive(Clone, Debug, Default)]
pub struct Thresholds(Vec<Int>);

impl Thresholds {
    pub fn new(constants: impl IntoIterator<Item = Int>) -> Self {
        let one = Int::from(1);
        let mut values: Vec<Int> = [-1, 0, 1].map(Int::from).into_iter().collect();
        for constant in constants {
            values.push(&constant - &one);
            values.push(&constant + &one);
            values.push(constant);
        }
        values.sort();
        values.dedup();
        Self(values)
    }

    /// The greatest threshold not above `value`, or `-∞`.
    fn below(&self, value: &Int) -> Bound {
        let index = self.0.partition_point(|threshold| threshold <= value);
        match index.checked_sub(1) {
            Some(index) => Bound::Finite(self.0[index].clone()),
            None => Bound::NegInf,
        }
    }

    /// The least threshold not below `value`, or `+∞`.
    fn above(&self, value: &Int) -> Bound {
        let index = self.0.partition_point(|threshold| threshold < value);
        match self.0.get(index) {
            Some(threshold) => Bound::Finite(threshold.clone()),
            None => Bound::PosInf,
        }
    }
}

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
    /// The value unchanged: an annotated binding's initializer, a declared
    /// result's body.
    Copy,
    Unary {
        op: UnaryOp,
        origin: NodeIdx,
    },
    /// An eager operator over its operands.
    Binary {
        op: BinaryOp,
        origin: NodeIdx,
    },
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
    Argument(NodeIdx),
    /// A callee's result into a call. Rounded likewise.
    Call,
    /// A call's context into the callee's entry.
    Enter,
}

impl Lattice for May {
    type Edge = RangeEdge;
    type Context = Thresholds;

    fn bottom() -> Self {
        Self::of_unit(false)
    }

    fn join(&mut self, other: &Self) -> bool {
        let ints = self.ints.join(&other.ints);
        let bools = self.bools.join(other.bools);
        let unit = !self.unit && other.unit;
        self.unit |= other.unit;
        ints | bools | unit
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
        match *edge {
            RangeEdge::None => Self::bottom(),
            RangeEdge::Copy => self.clone(),
            RangeEdge::Unary {
                op: UnaryOp::Neg, ..
            } => Self::ints(self.ints.neg()),
            RangeEdge::Unary {
                op: UnaryOp::Not, ..
            } => Self::bools(self.bools.not()),
            RangeEdge::Binary { op, .. } => {
                let rhs = second();
                match op {
                    BinaryOp::Add => Self::ints(self.ints.add(&rhs.ints)),
                    BinaryOp::Sub => Self::ints(self.ints.sub(&rhs.ints)),
                    BinaryOp::Mul => Self::ints(self.ints.mul(&rhs.ints)),
                    BinaryOp::Div => Self::ints(self.ints.div(&rhs.ints)),
                    BinaryOp::Rem => Self::ints(self.ints.rem(&rhs.ints)),
                    BinaryOp::Eq | BinaryOp::Ne => {
                        let mut bools = self.ints.compare(op, &rhs.ints);
                        let of_bools = self.bools.eq(rhs.bools);
                        bools.join(if op == BinaryOp::Eq {
                            of_bools
                        } else {
                            of_bools.not()
                        });
                        Self::bools(bools)
                    }
                    BinaryOp::Lt | BinaryOp::Le | BinaryOp::Gt | BinaryOp::Ge => {
                        Self::bools(self.ints.compare(op, &rhs.ints))
                    }
                }
            }
            RangeEdge::Lazy { and } => {
                let rhs = second();
                Self::bools(if and {
                    self.bools.and(rhs.bools)
                } else {
                    self.bools.or(rhs.bools)
                })
            }
            RangeEdge::Refine {
                op,
                local_is_lhs,
                sense,
            } => self.refine(op, local_is_lhs, sense, second()),
            RangeEdge::Exactly(value) => Self::bools(self.bools.intersect(Bools::single(value))),
            RangeEdge::Then => Self::of_unit(self.bools.may_true() && second().live()),
            RangeEdge::Else => Self::of_unit(self.bools.may_false() && second().live()),
            RangeEdge::Branch => {
                if second().live() {
                    self.clone()
                } else {
                    Self::bottom()
                }
            }
            RangeEdge::Argument(_) => {
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
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    fn ints(text: &str) -> Ints {
        // `[lo, hi]`, `[lo, hi] \ 0`, `∅`, with `-inf` and `inf` as the
        // infinite endpoints.
        if text == "∅" {
            return Ints::Empty;
        }
        let (band, hole) = match text.strip_suffix(" \\ 0") {
            Some(band) => (band, true),
            None => (text, false),
        };
        let inner = &band[1..band.len() - 1];
        let (lo, hi) = inner.split_once(", ").unwrap();
        let bound = |text: &str| match text {
            "-inf" => Bound::NegInf,
            "inf" => Bound::PosInf,
            _ => Bound::Finite(text.parse().unwrap()),
        };
        Ints::band(bound(lo), bound(hi), hole)
    }

    #[test]
    fn bands_are_canonical() {
        assert_eq!(ints("[0, 0] \\ 0"), Ints::Empty);
        assert_eq!(ints("[0, 5] \\ 0"), ints("[1, 5]"));
        assert_eq!(ints("[-5, 0] \\ 0"), ints("[-5, -1]"));
        assert_eq!(ints("[-5, 5] \\ 0").to_string(), "[-5, 5] \\ 0");
        assert_eq!(ints("[3, 2]"), Ints::Empty);
        assert_eq!(ints("[-inf, inf]").to_string(), "(-∞, +∞)");
        assert_eq!(ints("[0, inf]").to_string(), "[0, +∞)");
        assert!(ints("[-5, 5]").contains_zero());
        assert!(!ints("[-5, 5] \\ 0").contains_zero());
        assert!(ints("[0, 0]").is_zero());
        assert!(!ints("[0, 1]").is_zero());
    }

    #[test]
    fn join_is_the_hull_with_the_hole_only_when_neither_has_zero() {
        let mut a = ints("[-5, -1]");
        assert!(a.join(&ints("[1, 5]")));
        assert_eq!(a, ints("[-5, 5] \\ 0"));
        assert!(!a.join(&ints("[2, 3]")));
        assert!(a.join(&ints("[0, 0]")));
        assert_eq!(a, ints("[-5, 5]"));
        let mut empty = Ints::Empty;
        assert!(!empty.join(&Ints::Empty));
        assert!(empty.join(&ints("[7, 7]")));
        assert_eq!(empty, ints("[7, 7]"));
    }

    #[test]
    fn arithmetic_over_the_extended_integers() {
        assert_eq!(ints("[1, 2]").add(&ints("[10, inf]")), ints("[11, inf]"));
        assert_eq!(ints("[1, 2]").sub(&ints("[-inf, 5]")), ints("[-4, inf]"));
        assert_eq!(ints("[-2, 3]").mul(&ints("[-4, 5]")), ints("[-12, 15]"));
        assert_eq!(ints("[1, 3]").mul(&ints("[-inf, -1]")), ints("[-inf, -1]"));
        assert_eq!(
            ints("[0, 3]").mul(&ints("[-inf, inf]")),
            ints("[-inf, inf]")
        );
        assert_eq!(
            ints("[-5, 5] \\ 0").mul(&ints("[2, 2]")),
            ints("[-10, 10] \\ 0")
        );
        assert_eq!(ints("[2, 3]").neg(), ints("[-3, -2]"));
        assert_eq!(ints("[7, 7]").div(&ints("[2, 2]")), ints("[3, 3]"));
        assert_eq!(ints("[-7, 7]").div(&ints("[-2, 2]")), ints("[-7, 7]"));
        assert_eq!(ints("[10, 20]").div(&ints("[0, 0]")), Ints::Empty);
        assert_eq!(ints("[10, 20]").div(&ints("[1, inf]")), ints("[0, 20]"));
        assert_eq!(ints("[-7, 7]").rem(&ints("[3, 3]")), ints("[-2, 2]"));
        assert_eq!(ints("[0, 100]").rem(&ints("[-4, 5]")), ints("[0, 4]"));
        assert_eq!(ints("[-3, 100]").rem(&ints("[1, inf]")), ints("[-3, 100]"));
        assert_eq!(ints("[5, 9]").rem(&ints("[0, 0]")), Ints::Empty);
    }

    #[test]
    fn comparisons_and_refinements_agree() {
        let n = ints("[0, 15]");
        assert_eq!(n.compare(BinaryOp::Lt, &ints("[2, 2]")), Bools::BOTH);
        assert_eq!(
            ints("[0, 1]").compare(BinaryOp::Lt, &ints("[2, 2]")),
            Bools::single(true)
        );
        assert_eq!(
            ints("[2, 9]").compare(BinaryOp::Lt, &ints("[2, 2]")),
            Bools::single(false)
        );
        assert_eq!(
            ints("[-5, 5] \\ 0").compare(BinaryOp::Eq, &ints("[0, 0]")),
            Bools::single(false)
        );
        assert_eq!(
            ints("[3, 3]").compare(BinaryOp::Ne, &ints("[3, 3]")),
            Bools::single(false)
        );
        assert_eq!(n.refine(BinaryOp::Lt, &ints("[2, 2]")), ints("[0, 1]"));
        assert_eq!(n.refine(BinaryOp::Ge, &ints("[2, 2]")), ints("[2, 15]"));
        assert_eq!(n.refine(BinaryOp::Ne, &ints("[0, 0]")), ints("[1, 15]"));
        assert_eq!(
            ints("[-5, 5]").refine(BinaryOp::Ne, &ints("[0, 0]")),
            ints("[-5, 5] \\ 0")
        );
        assert_eq!(n.refine(BinaryOp::Eq, &ints("[10, 20]")), ints("[10, 15]"));
        assert_eq!(n.refine(BinaryOp::Gt, &ints("[20, 20]")), Ints::Empty);
        assert_eq!(n.refine(BinaryOp::Ne, &ints("[1, 2]")), n);
        let may = May::ints(n.clone());
        let two = May::int(2.into());
        // `2 > n` reads as `n < 2`; its false sense is `n >= 2`.
        assert_eq!(
            may.refine(BinaryOp::Gt, false, true, &two).ints,
            ints("[0, 1]")
        );
        assert_eq!(
            may.refine(BinaryOp::Gt, false, false, &two).ints,
            ints("[2, 15]")
        );
    }

    #[test]
    fn rounding_keeps_points_signs_and_holes() {
        let t = Thresholds::new([15, 2].map(Int::from));
        assert_eq!(ints("[7, 7]").round(&t), ints("[7, 7]"));
        assert_eq!(ints("[4, 13]").round(&t), ints("[3, 14]"));
        assert_eq!(ints("[4, 20]").round(&t), ints("[3, inf]"));
        assert_eq!(ints("[-20, 1]").round(&t), ints("[-inf, 1]"));
        assert_eq!(ints("[5, 100]").round(&t), ints("[3, inf]"));
        assert_eq!(ints("[-7, 7] \\ 0").round(&t), ints("[-inf, 14] \\ 0"));
        assert_eq!(ints("[-3, -2]").round(&t), ints("[-inf, -1]"));
        assert_eq!(Ints::Empty.round(&t), Ints::Empty);
    }

    #[test]
    fn booleans_and_display() {
        assert_eq!(Bools::single(false).and(Bools::BOTH), Bools::single(false));
        assert_eq!(Bools::BOTH.and(Bools::single(false)), Bools::single(false));
        assert_eq!(Bools::single(true).and(Bools::BOTH), Bools::BOTH);
        assert_eq!(Bools::single(true).or(Bools::EMPTY), Bools::single(true));
        assert_eq!(Bools::single(false).and(Bools::EMPTY), Bools::single(false));
        assert_eq!(Bools::single(true).and(Bools::EMPTY), Bools::EMPTY);
        assert_eq!(Bools::EMPTY.and(Bools::BOTH), Bools::EMPTY);
        assert_eq!(
            Bools::single(false).or(Bools::single(true)),
            Bools::single(true)
        );
        assert_eq!(Bools::BOTH.eq(Bools::single(true)), Bools::BOTH);
        assert_eq!(
            Bools::single(true).eq(Bools::single(true)),
            Bools::single(true)
        );
        assert_eq!(Bools::BOTH.to_string(), "{true, false}");
        assert_eq!(May::unit().shown(Ty::Unit).to_string(), "unit");
        assert_eq!(May::bottom().shown(Ty::Unit).to_string(), "∅");
        assert_eq!(May::bool(true).shown(Ty::Bool).to_string(), "{true}");
        assert_eq!(May::int(5.into()).shown(Ty::Int).to_string(), "[5, 5]");
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
        let edge = RangeEdge::Argument(NodeIdx::new(0));
        assert_eq!(value.transfer(&edge, Some(&dead), false, &cx), dead);
        assert_eq!(value.transfer(&edge, Some(&live), false, &cx), value);
        assert_eq!(live.transfer(&RangeEdge::Enter, None, false, &cx), live);
        assert_eq!(dead.transfer(&RangeEdge::Enter, None, false, &cx), dead);
        // Only a cyclic interprocedural flow rounds.
        let band = May::ints(ints("[4, 13]"));
        let cx = Thresholds::new([15, 2].map(Int::from));
        assert_eq!(band.transfer(&RangeEdge::Call, None, false, &cx), band);
        assert_eq!(
            band.transfer(&RangeEdge::Call, None, true, &cx).ints,
            ints("[3, 14]")
        );
        assert_eq!(
            band.transfer(&edge, Some(&live), true, &cx).ints,
            ints("[3, 14]")
        );
        assert_eq!(band.transfer(&RangeEdge::Copy, None, true, &cx), band);
    }

    fn band() -> impl Strategy<Value = Ints> {
        (-20i64..20, 0i64..25, any::<bool>()).prop_map(|(lo, len, hole)| {
            Ints::band(Bound::finite(lo), Bound::finite(lo + len), hole)
        })
    }

    fn members(band: &Ints) -> Vec<i64> {
        let Some((lo, hi, hole)) = band.parts() else {
            return Vec::new();
        };
        let (Bound::Finite(lo), Bound::Finite(hi)) = (lo, hi) else {
            unreachable!("finite test bands");
        };
        let (lo, hi) = (
            lo.to_string().parse::<i64>().unwrap(),
            hi.to_string().parse::<i64>().unwrap(),
        );
        (lo..=hi).filter(|v| !(hole && *v == 0)).collect()
    }

    fn contains(band: &Ints, value: i64) -> bool {
        band.parts().is_some_and(|(lo, hi, hole)| {
            let value = Bound::finite(value);
            *lo <= value && value <= *hi && !(hole && value.sign() == Ordering::Equal)
        })
    }

    proptest! {
        /// Every transfer over-approximates the concrete operation on every
        /// member of its operands, which is soundness.
        #[test]
        fn transfers_are_sound(a in band(), b in band()) {
            let xs = members(&a);
            let ys = members(&b);
            let sum = a.add(&b);
            let difference = a.sub(&b);
            let product = a.mul(&b);
            let quotient = a.div(&b);
            let remainder = a.rem(&b);
            let negated = a.neg();
            for &x in &xs {
                prop_assert!(contains(&negated, -x));
                for &y in &ys {
                    prop_assert!(contains(&sum, x + y), "{a} + {b} ∌ {x} + {y}");
                    prop_assert!(contains(&difference, x - y));
                    prop_assert!(contains(&product, x * y), "{a} * {b} ∌ {x} * {y}");
                    if y != 0 {
                        prop_assert!(contains(&quotient, x / y), "{a} / {b} ∌ {x} / {y}");
                        prop_assert!(contains(&remainder, x % y), "{a} % {b} ∌ {x} % {y}");
                    }
                    for op in [BinaryOp::Lt, BinaryOp::Le, BinaryOp::Gt, BinaryOp::Ge, BinaryOp::Eq, BinaryOp::Ne] {
                        let holds = match op {
                            BinaryOp::Lt => x < y,
                            BinaryOp::Le => x <= y,
                            BinaryOp::Gt => x > y,
                            BinaryOp::Ge => x >= y,
                            BinaryOp::Eq => x == y,
                            _ => x != y,
                        };
                        let bools = a.compare(op, &b);
                        let seen = if holds { bools.may_true() } else { bools.may_false() };
                        prop_assert!(seen, "{a} {op:?} {b} misses {x} {op:?} {y}");
                        if holds {
                            prop_assert!(contains(&a.refine(op, &b), x), "{a} refined by {op:?} {b} ∌ {x}");
                        }
                    }
                }
            }
        }

        /// Join is a least upper bound, and rounding only widens.
        #[test]
        fn join_and_rounding_widen(a in band(), b in band(), constants in prop::collection::vec(-20i64..20, 0..4)) {
            let mut joined = a.clone();
            joined.join(&b);
            for x in members(&a).into_iter().chain(members(&b)) {
                prop_assert!(contains(&joined, x));
            }
            let thresholds = Thresholds::new(constants.into_iter().map(Int::from));
            let rounded = a.round(&thresholds);
            for x in members(&a) {
                prop_assert!(contains(&rounded, x));
            }
            prop_assert_eq!(a.contains_zero(), rounded.contains_zero());
        }
    }
}
