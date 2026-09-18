//! May-values: the set of values that may reach a node, one set per
//! scalar type, and the may-domain they make.
//!
//! A [`May`] is a product of one set per scalar type: a band of integers
//! over ℤ ∪ {±∞} with an optional hole at zero, a set of booleans, and a
//! unit bit. A well-typed node populates one of them, and a node with
//! none populated has no values: it is unreachable, or nothing flows into
//! it. Reachability is therefore not a separate bit: a context node is a
//! unit-valued node that is live exactly when its region can run.
//!
//! The band with a hole is the shape a guard leaves: `d != 0` on a signed
//! `d` excludes one point from the middle, and a product of two such bands
//! keeps the hole. Every operation is total and sound: the result of an
//! operation on two bands contains the result of the operation on any two
//! of their members, which a property test checks against the concrete
//! integers, through the one [`Domain`] every operator is read in.
//!
//! Hull is the join, and a recursion would climb forever, so the solver
//! above rounds the endpoints of a band that travels around a cycle to
//! the program's [`Thresholds`], which keeps every ascending chain finite
//! without a widening operator.

use std::cmp::Ordering;
use std::fmt;
use std::ops::{Add, BitAnd, Div, Mul, Neg, Rem, Sub};

use crate::{BinaryOp, Domain, Fault, Int, Ty};

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

    fn succ(&self) -> Self {
        self + &Self::finite(1)
    }

    fn pred(&self) -> Self {
        self - &Self::finite(1)
    }

    fn abs(&self) -> Self {
        if self.sign() == Ordering::Less {
            -self
        } else {
            self.clone()
        }
    }

    fn is_finite(&self) -> bool {
        matches!(self, Self::Finite(_))
    }
}

impl Neg for &Bound {
    type Output = Bound;
    fn neg(self) -> Bound {
        match self {
            Bound::NegInf => Bound::PosInf,
            Bound::Finite(value) => Bound::Finite(-value),
            Bound::PosInf => Bound::NegInf,
        }
    }
}

/// Never asked to add opposite infinities: every use adds two lower or two
/// upper endpoints.
impl Add<&Bound> for &Bound {
    type Output = Bound;
    fn add(self, other: &Bound) -> Bound {
        match (self, other) {
            (Bound::Finite(a), Bound::Finite(b)) => Bound::Finite(a + b),
            (Bound::NegInf, Bound::PosInf) | (Bound::PosInf, Bound::NegInf) => {
                unreachable!("endpoints of one side never mix infinities")
            }
            (Bound::NegInf, _) | (_, Bound::NegInf) => Bound::NegInf,
            (Bound::PosInf, _) | (_, Bound::PosInf) => Bound::PosInf,
        }
    }
}

impl Sub<&Bound> for &Bound {
    type Output = Bound;
    fn sub(self, other: &Bound) -> Bound {
        self + &-other
    }
}

/// With `0 · ±∞ = 0`, which is what a hull of products needs.
impl Mul<&Bound> for &Bound {
    type Output = Bound;
    fn mul(self, other: &Bound) -> Bound {
        match (self, other) {
            (Bound::Finite(a), Bound::Finite(b)) => Bound::Finite(a * b),
            _ if self.sign() == Ordering::Equal || other.sign() == Ordering::Equal => Bound::zero(),
            _ => {
                let positive =
                    (self.sign() == Ordering::Greater) == (other.sign() == Ordering::Greater);
                if positive {
                    Bound::PosInf
                } else {
                    Bound::NegInf
                }
            }
        }
    }
}

/// Truncating division by a non-zero divisor. An infinite dividend stays
/// infinite with the combined sign; a finite one over an infinite divisor
/// is zero.
impl Div<&Bound> for &Bound {
    type Output = Bound;
    fn div(self, other: &Bound) -> Bound {
        debug_assert_ne!(other.sign(), Ordering::Equal);
        match (self, other) {
            (Bound::Finite(a), Bound::Finite(b)) => {
                Bound::Finite(a.checked_div(b).expect("a non-zero divisor"))
            }
            (Bound::Finite(_), _) => Bound::zero(),
            _ => {
                let positive =
                    (self.sign() == Ordering::Greater) == (other.sign() == Ordering::Greater);
                if positive {
                    Bound::PosInf
                } else {
                    Bound::NegInf
                }
            }
        }
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

/// A set of integers: nothing, or a band with an optional hole at zero.
/// The hole is canonical: it is set only when `lo < 0 < hi`, and a zero at
/// an endpoint is removed by moving the endpoint, so equal sets have equal
/// representations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ints(Option<Band>);

#[derive(Clone, Debug, PartialEq, Eq)]
struct Band {
    lo: Bound,
    hi: Bound,
    hole: bool,
}

/// The set of one value.
impl From<Int> for Ints {
    fn from(value: Int) -> Self {
        let bound = Bound::Finite(value);
        Self::band(bound.clone(), bound, false)
    }
}

impl Ints {
    pub const EMPTY: Self = Self(None);

    /// Every integer.
    pub fn all() -> Self {
        Self::band(Bound::NegInf, Bound::PosInf, false)
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
        // No integer sits at or past an infinity, so a band that starts at
        // `+∞` or ends at `-∞` holds none.
        if lo > hi || lo == Bound::PosInf || hi == Bound::NegInf {
            return Self::EMPTY;
        }
        let hole = hole && lo.sign() == Ordering::Less && hi.sign() == Ordering::Greater;
        Self(Some(Band { lo, hi, hole }))
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.0.is_none()
    }

    #[inline]
    pub fn contains_zero(&self) -> bool {
        self.0.as_ref().is_some_and(|band| {
            !band.hole && band.lo.sign() != Ordering::Greater && band.hi.sign() != Ordering::Less
        })
    }

    /// Exactly `[0, 0]`.
    pub fn is_zero(&self) -> bool {
        self.0.as_ref().is_some_and(|band| {
            band.lo.sign() == Ordering::Equal && band.hi.sign() == Ordering::Equal
        })
    }

    fn is_point(&self) -> bool {
        self.0.as_ref().is_some_and(|band| band.lo == band.hi)
    }

    /// The endpoints, when the set is bounded on that side.
    pub fn lo(&self) -> Option<Int> {
        match &self.0 {
            Some(Band {
                lo: Bound::Finite(value),
                ..
            }) => Some(value.clone()),
            _ => None,
        }
    }

    pub fn hi(&self) -> Option<Int> {
        match &self.0 {
            Some(Band {
                hi: Bound::Finite(value),
                ..
            }) => Some(value.clone()),
            _ => None,
        }
    }

    /// The smallest band containing both. Reports growth.
    #[inline]
    pub fn join(&mut self, other: &Self) -> bool {
        let joined = match (&self.0, &other.0) {
            (_, None) => return false,
            (None, Some(_)) => other.clone(),
            (Some(a), Some(b)) => {
                let hole = !self.contains_zero() && !other.contains_zero();
                Self::band((&a.lo).min(&b.lo).clone(), (&a.hi).max(&b.hi).clone(), hole)
            }
        };
        let grew = joined != *self;
        *self = joined;
        grew
    }

    fn without(&self, point: &Bound) -> Self {
        let Some(Band { lo, hi, hole }) = &self.0 else {
            return Self::EMPTY;
        };
        if lo == point {
            Self::band(lo.succ(), hi.clone(), *hole)
        } else if hi == point {
            Self::band(lo.clone(), hi.pred(), *hole)
        } else if point.sign() == Ordering::Equal {
            Self::band(lo.clone(), hi.clone(), true)
        } else {
            self.clone()
        }
    }

    /// The divisor's non-zero halves, each a band with one sign.
    fn halves(&self) -> Vec<(Bound, Bound)> {
        let Some(Band { lo, hi, .. }) = &self.0 else {
            return Vec::new();
        };
        let mut halves = Vec::with_capacity(2);
        if lo.sign() == Ordering::Less {
            halves.push((lo.clone(), hi.min(&Bound::finite(-1)).clone()));
        }
        if hi.sign() == Ordering::Greater {
            halves.push((lo.max(&Bound::finite(1)).clone(), hi.clone()));
        }
        halves
    }

    /// The booleans `self op other` may be.
    fn compare(&self, op: BinaryOp, other: &Self) -> Bools {
        let (Some(a), Some(b)) = (&self.0, &other.0) else {
            return Bools::EMPTY;
        };
        let (may_true, may_false) = match op {
            BinaryOp::Lt => (a.lo < b.hi, a.hi >= b.lo),
            BinaryOp::Le => (a.lo <= b.hi, a.hi > b.lo),
            BinaryOp::Gt => (a.hi > b.lo, a.lo <= b.hi),
            BinaryOp::Ge => (a.hi >= b.lo, a.lo < b.hi),
            BinaryOp::Eq | BinaryOp::Ne => {
                let equal = !(self & other).is_empty();
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
        let (Some(Band { lo, hi, hole }), Some(b)) = (&self.0, &other.0) else {
            return Self::EMPTY;
        };
        match op {
            BinaryOp::Lt => Self::band(lo.clone(), hi.min(&b.hi.pred()).clone(), *hole),
            BinaryOp::Le => Self::band(lo.clone(), hi.min(&b.hi).clone(), *hole),
            BinaryOp::Gt => Self::band(lo.max(&b.lo.succ()).clone(), hi.clone(), *hole),
            BinaryOp::Ge => Self::band(lo.max(&b.lo).clone(), hi.clone(), *hole),
            BinaryOp::Eq => self & other,
            BinaryOp::Ne => {
                if other.is_point() {
                    self.without(&b.lo)
                } else {
                    self.clone()
                }
            }
            _ => unreachable!("a comparison"),
        }
    }

    /// Endpoints moved outward to the thresholds; a point is left exact.
    pub fn round(&self, thresholds: &Thresholds) -> Self {
        let Some(Band { lo, hi, hole }) = &self.0 else {
            return Self::EMPTY;
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
        Self::band(lo, hi, *hole)
    }
}

/// Intersection.
impl BitAnd<&Ints> for &Ints {
    type Output = Ints;
    fn bitand(self, other: &Ints) -> Ints {
        match (&self.0, &other.0) {
            (Some(a), Some(b)) => Ints::band(
                (&a.lo).max(&b.lo).clone(),
                (&a.hi).min(&b.hi).clone(),
                a.hole || b.hole,
            ),
            _ => Ints::EMPTY,
        }
    }
}

impl Neg for &Ints {
    type Output = Ints;
    fn neg(self) -> Ints {
        match &self.0 {
            None => Ints::EMPTY,
            Some(Band { lo, hi, hole }) => Ints::band(-hi, -lo, *hole),
        }
    }
}

impl Add<&Ints> for &Ints {
    type Output = Ints;
    fn add(self, other: &Ints) -> Ints {
        match (&self.0, &other.0) {
            (Some(a), Some(b)) => Ints::band(&a.lo + &b.lo, &a.hi + &b.hi, false),
            _ => Ints::EMPTY,
        }
    }
}

impl Sub<&Ints> for &Ints {
    type Output = Ints;
    fn sub(self, other: &Ints) -> Ints {
        match (&self.0, &other.0) {
            (Some(a), Some(b)) => Ints::band(&a.lo - &b.hi, &a.hi - &b.lo, false),
            _ => Ints::EMPTY,
        }
    }
}

impl Mul<&Ints> for &Ints {
    type Output = Ints;
    fn mul(self, other: &Ints) -> Ints {
        match (&self.0, &other.0) {
            (Some(a), Some(b)) => {
                let corners = [&a.lo * &b.lo, &a.lo * &b.hi, &a.hi * &b.lo, &a.hi * &b.hi];
                let lo = corners.iter().min().unwrap().clone();
                let hi = corners.iter().max().unwrap().clone();
                // A product of non-zeros is non-zero over ℤ.
                Ints::band(lo, hi, !self.contains_zero() && !other.contains_zero())
            }
            _ => Ints::EMPTY,
        }
    }
}

/// Truncating quotient: exact on the corners of each non-zero half of the
/// divisor, so an error at one division does not cascade, and empty over a
/// divisor that is only zero.
impl Div<&Ints> for &Ints {
    type Output = Ints;
    fn div(self, other: &Ints) -> Ints {
        let Some(Band {
            lo: lo1, hi: hi1, ..
        }) = &self.0
        else {
            return Ints::EMPTY;
        };
        let mut result = Ints::EMPTY;
        for (lo2, hi2) in other.halves() {
            let corners = [lo1 / &lo2, lo1 / &hi2, hi1 / &lo2, hi1 / &hi2];
            let lo = corners.iter().min().unwrap().clone();
            let hi = corners.iter().max().unwrap().clone();
            result.join(&Ints::band(lo, hi, false));
        }
        result
    }
}

/// Truncating remainder: exact over two points, otherwise the dividend's
/// sign, bounded by the largest divisor magnitude minus one, and empty
/// over a divisor that is only zero.
impl Rem<&Ints> for &Ints {
    type Output = Ints;
    fn rem(self, other: &Ints) -> Ints {
        if self.is_point()
            && other.is_point()
            && let (Some(a), Some(b)) = (self.lo(), other.lo())
        {
            return a.checked_rem(&b).map_or(Ints::EMPTY, Ints::from);
        }
        let (Some(a), Some(b)) = (&self.0, &other.0) else {
            return Ints::EMPTY;
        };
        let magnitude = b.lo.abs().max(b.hi.abs());
        if magnitude.sign() == Ordering::Equal {
            return Ints::EMPTY;
        }
        let limit = magnitude.pred();
        let lo = if a.lo.sign() != Ordering::Less {
            Bound::zero()
        } else {
            (&a.lo).max(&-&limit).clone()
        };
        let hi = if a.hi.sign() != Ordering::Greater {
            Bound::zero()
        } else {
            (&a.hi).min(&limit).clone()
        };
        Ints::band(lo, hi, false)
    }
}

impl fmt::Display for Ints {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.0 {
            None => f.write_str("∅"),
            Some(Band { lo, hi, hole }) => {
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

/// A set of booleans.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Bools(u8);

impl Bools {
    pub const EMPTY: Self = Self(0);
    const FALSE: Self = Self(1);
    const TRUE: Self = Self(2);
    pub const BOTH: Self = Self(3);

    fn of(may_true: bool, may_false: bool) -> Self {
        Self(u8::from(may_false) | (u8::from(may_true) << 1))
    }

    #[inline]
    pub fn is_empty(self) -> bool {
        self.0 == 0
    }

    #[inline]
    pub fn may_true(self) -> bool {
        self.0 & Self::TRUE.0 != 0
    }

    #[inline]
    pub fn may_false(self) -> bool {
        self.0 & Self::FALSE.0 != 0
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

    #[inline]
    pub fn join(&mut self, other: Self) -> bool {
        let before = self.0;
        self.0 |= other.0;
        before != self.0
    }
}

/// Intersection.
impl BitAnd for Bools {
    type Output = Self;
    fn bitand(self, other: Self) -> Self {
        Self(self.0 & other.0)
    }
}

/// The set of one value.
impl From<bool> for Bools {
    fn from(value: bool) -> Self {
        if value { Self::TRUE } else { Self::FALSE }
    }
}

impl std::ops::Not for Bools {
    type Output = Self;
    fn not(self) -> Self {
        Self::of(self.may_false(), self.may_true())
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

/// The values that may reach a node, one set per scalar type. Empty in
/// every component means no value ever does.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct May {
    pub ints: Ints,
    pub bools: Bools,
    pub unit: bool,
}

impl May {
    /// No value of any type: nothing reaches, or nothing flows in.
    pub const NONE: Self = Self {
        ints: Ints::EMPTY,
        bools: Bools::EMPTY,
        unit: false,
    };

    pub fn int(value: Int) -> Self {
        Self::ints(Ints::from(value))
    }

    pub fn bool(value: bool) -> Self {
        Self::bools(Bools::from(value))
    }

    pub fn unit() -> Self {
        Self::of_unit(true)
    }

    pub fn ints(ints: Ints) -> Self {
        Self {
            ints,
            bools: Bools::EMPTY,
            unit: false,
        }
    }

    pub fn bools(bools: Bools) -> Self {
        Self {
            ints: Ints::EMPTY,
            bools,
            unit: false,
        }
    }

    pub fn of_unit(unit: bool) -> Self {
        Self { unit, ..Self::NONE }
    }

    /// Whether any value at all may reach the node.
    #[inline]
    pub fn live(&self) -> bool {
        !self.ints.is_empty() || !self.bools.is_empty() || self.unit
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
#[derive(Clone, Debug)]
pub struct Thresholds(Vec<Int>);

/// The thresholds of no constants: `-1`, `0`, and `1` alone.
impl Default for Thresholds {
    fn default() -> Self {
        std::iter::empty().collect()
    }
}

/// The thresholds of a file's constants.
impl FromIterator<Int> for Thresholds {
    fn from_iter<I: IntoIterator<Item = Int>>(constants: I) -> Self {
        let one = Int::from(1);
        let constants: Vec<Int> = constants.into_iter().collect();
        // The constants arrive in the order the file spells them, which is
        // nearly sorted more often than not, and the sort merges runs it
        // finds: each shift of the constants is one run, not a descent
        // every third value.
        let mut values: Vec<Int> = Vec::with_capacity(3 * constants.len() + 3);
        values.extend([-1, 0, 1].map(Int::from));
        values.extend(constants.iter().map(|constant| constant - &one));
        values.extend(constants.iter().map(|constant| constant + &one));
        values.extend(constants);
        values.sort();
        values.dedup();
        Self(values)
    }
}

impl Thresholds {
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

/// The may-domain: every operator over-approximates the concrete one on
/// every member of its operands, which a property test checks, and none
/// faults, since what the checker asks of a value it reads off the sets
/// after the solve.
impl Domain for May {
    #[inline]
    fn int(value: &Int) -> Self {
        Self::int(value.clone())
    }

    #[inline]
    fn bool(value: bool) -> Self {
        Self::bool(value)
    }

    #[inline]
    fn unit() -> Self {
        Self::unit()
    }

    #[inline]
    fn neg(&self) -> Result<Self, Fault> {
        Ok(Self::ints(-&self.ints))
    }

    #[inline]
    fn not(&self) -> Result<Self, Fault> {
        Ok(Self::bools(!self.bools))
    }

    #[inline]
    fn binary(op: BinaryOp, lhs: &Self, rhs: &Self) -> Result<Self, Fault> {
        Ok(match op {
            BinaryOp::Add => Self::ints(&lhs.ints + &rhs.ints),
            BinaryOp::Sub => Self::ints(&lhs.ints - &rhs.ints),
            BinaryOp::Mul => Self::ints(&lhs.ints * &rhs.ints),
            BinaryOp::Div => Self::ints(&lhs.ints / &rhs.ints),
            BinaryOp::Rem => Self::ints(&lhs.ints % &rhs.ints),
            BinaryOp::Eq | BinaryOp::Ne => {
                let mut bools = lhs.ints.compare(op, &rhs.ints);
                let of_bools = lhs.bools.eq(rhs.bools);
                bools.join(if op == BinaryOp::Eq {
                    of_bools
                } else {
                    !of_bools
                });
                Self::bools(bools)
            }
            BinaryOp::Lt | BinaryOp::Le | BinaryOp::Gt | BinaryOp::Ge => {
                Self::bools(lhs.ints.compare(op, &rhs.ints))
            }
        })
    }

    #[inline]
    fn lazy(and: bool, lhs: &Self, rhs: &Self) -> Result<Self, Fault> {
        Ok(Self::bools(if and {
            lhs.bools.and(rhs.bools)
        } else {
            lhs.bools.or(rhs.bools)
        }))
    }

    /// The local's side of the comparison, narrowed to where it holds.
    #[inline]
    fn refine(&self, op: BinaryOp, local_is_lhs: bool, sense: bool, other: &Self) -> Self {
        let op = if local_is_lhs { op } else { flip(op) };
        let op = if sense { op } else { negate(op) };
        let bools = match op {
            BinaryOp::Eq => self.bools & other.bools,
            BinaryOp::Ne
                if other.bools == Bools::from(true) || other.bools == Bools::from(false) =>
            {
                self.bools & !other.bools
            }
            _ => self.bools,
        };
        Self {
            ints: self.ints.refine(op, &other.ints),
            bools,
            unit: false,
        }
    }

    #[inline]
    fn exactly(&self, value: bool) -> Self {
        Self::bools(self.bools & Bools::from(value))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Op, Value};
    use proptest::prelude::*;

    fn ints(text: &str) -> Ints {
        // `[lo, hi]`, `[lo, hi] \ 0`, `∅`, with `-inf` and `inf` as the
        // infinite endpoints.
        if text == "∅" {
            return Ints::EMPTY;
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
        assert_eq!(ints("[0, 0] \\ 0"), Ints::EMPTY);
        assert_eq!(ints("[0, 5] \\ 0"), ints("[1, 5]"));
        assert_eq!(ints("[-5, 0] \\ 0"), ints("[-5, -1]"));
        assert_eq!(ints("[-5, 5] \\ 0").to_string(), "[-5, 5] \\ 0");
        assert_eq!(ints("[3, 2]"), Ints::EMPTY);
        assert_eq!(ints("[inf, inf]"), Ints::EMPTY);
        assert_eq!(ints("[-inf, -inf]"), Ints::EMPTY);
        assert_eq!(ints("[-inf, inf]").to_string(), "(-∞, +∞)");
        assert_eq!(ints("[0, inf]").to_string(), "[0, +∞)");
        assert!(ints("[-5, 5]").contains_zero());
        assert!(!ints("[-5, 5] \\ 0").contains_zero());
        assert!(ints("[0, 0]").is_zero());
        assert!(!ints("[0, 1]").is_zero());
    }

    #[test]
    fn endpoints_past_the_words_round_trip() {
        let max = Ints::from(Int::from(i64::MAX));
        let one = Ints::from(Int::from(1));
        let past = &max + &one;
        assert_eq!(
            past.to_string(),
            "[9223372036854775808, 9223372036854775808]"
        );
        assert_eq!(&past - &one, max);
        let min = Ints::from(Int::from(i64::MIN));
        assert_eq!(
            (-&min).to_string(),
            "[9223372036854775808, 9223372036854775808]"
        );
        assert_eq!(-&-&min, min);
        assert_eq!(&ints("[-inf, 5]") + &ints("[1, 2]"), ints("[-inf, 7]"));
        assert_eq!(&ints("[3, inf]") - &ints("[1, 2]"), ints("[1, inf]"));
        assert_eq!(-&ints("[3, inf]"), ints("[-inf, -3]"));
        let mut joined = ints("[20, inf]");
        assert!(!joined.join(&ints("[30, inf]")));
        assert!(joined.join(&ints("[-inf, 30]")));
        assert_eq!(joined, ints("[-inf, inf]"));
        let mut wide = past.clone();
        assert!(wide.join(&one));
        assert_eq!(wide.to_string(), "[1, 9223372036854775808]");
        assert!(!wide.join(&max));
    }

    #[test]
    fn join_is_the_hull_with_the_hole_only_when_neither_has_zero() {
        let mut a = ints("[-5, -1]");
        assert!(a.join(&ints("[1, 5]")));
        assert_eq!(a, ints("[-5, 5] \\ 0"));
        assert!(!a.join(&ints("[2, 3]")));
        assert!(a.join(&ints("[0, 0]")));
        assert_eq!(a, ints("[-5, 5]"));
        let mut empty = Ints::EMPTY;
        assert!(!empty.join(&Ints::EMPTY));
        assert!(empty.join(&ints("[7, 7]")));
        assert_eq!(empty, ints("[7, 7]"));
    }

    #[test]
    fn arithmetic_over_the_extended_integers() {
        assert_eq!(&ints("[1, 2]") + &ints("[10, inf]"), ints("[11, inf]"));
        assert_eq!(&ints("[1, 2]") - &ints("[-inf, 5]"), ints("[-4, inf]"));
        assert_eq!(&ints("[-2, 3]") * &ints("[-4, 5]"), ints("[-12, 15]"));
        assert_eq!(&ints("[1, 3]") * &ints("[-inf, -1]"), ints("[-inf, -1]"));
        assert_eq!(&ints("[0, 3]") * &ints("[-inf, inf]"), ints("[-inf, inf]"));
        assert_eq!(
            &ints("[-5, 5] \\ 0") * &ints("[2, 2]"),
            ints("[-10, 10] \\ 0")
        );
        assert_eq!(-&ints("[2, 3]"), ints("[-3, -2]"));
        assert_eq!(&ints("[7, 7]") / &ints("[2, 2]"), ints("[3, 3]"));
        assert_eq!(&ints("[-7, 7]") / &ints("[-2, 2]"), ints("[-7, 7]"));
        assert_eq!(&ints("[10, 20]") / &ints("[0, 0]"), Ints::EMPTY);
        assert_eq!(&ints("[10, 20]") / &ints("[1, inf]"), ints("[0, 20]"));
        assert_eq!(&ints("[-7, 7]") % &ints("[3, 3]"), ints("[-2, 2]"));
        assert_eq!(&ints("[0, 100]") % &ints("[-4, 5]"), ints("[0, 4]"));
        assert_eq!(&ints("[-3, 100]") % &ints("[1, inf]"), ints("[-3, 100]"));
        assert_eq!(&ints("[5, 9]") % &ints("[0, 0]"), Ints::EMPTY);
        assert_eq!(&ints("[7, 7]") % &ints("[3, 3]"), ints("[1, 1]"));
        assert_eq!(&ints("[-7, -7]") % &ints("[3, 3]"), ints("[-1, -1]"));
        assert_eq!(&ints("[6, 6]") % &ints("[4, 4]"), ints("[2, 2]"));
        assert_eq!(&ints("[6, 6]") % &ints("[0, 0]"), Ints::EMPTY);
    }

    #[test]
    fn comparisons_and_refinements_agree() {
        let n = ints("[0, 15]");
        assert_eq!(n.compare(BinaryOp::Lt, &ints("[2, 2]")), Bools::BOTH);
        assert_eq!(
            ints("[0, 1]").compare(BinaryOp::Lt, &ints("[2, 2]")),
            Bools::from(true)
        );
        assert_eq!(
            ints("[2, 9]").compare(BinaryOp::Lt, &ints("[2, 2]")),
            Bools::from(false)
        );
        assert_eq!(
            ints("[-5, 5] \\ 0").compare(BinaryOp::Eq, &ints("[0, 0]")),
            Bools::from(false)
        );
        assert_eq!(
            ints("[3, 3]").compare(BinaryOp::Ne, &ints("[3, 3]")),
            Bools::from(false)
        );
        assert_eq!(n.refine(BinaryOp::Lt, &ints("[2, 2]")), ints("[0, 1]"));
        assert_eq!(n.refine(BinaryOp::Ge, &ints("[2, 2]")), ints("[2, 15]"));
        assert_eq!(n.refine(BinaryOp::Ne, &ints("[0, 0]")), ints("[1, 15]"));
        assert_eq!(
            ints("[-5, 5]").refine(BinaryOp::Ne, &ints("[0, 0]")),
            ints("[-5, 5] \\ 0")
        );
        assert_eq!(n.refine(BinaryOp::Eq, &ints("[10, 20]")), ints("[10, 15]"));
        assert_eq!(n.refine(BinaryOp::Gt, &ints("[20, 20]")), Ints::EMPTY);
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
        let flag = May::bools(Bools::BOTH);
        assert_eq!(
            flag.refine(BinaryOp::Eq, true, true, &May::bool(true))
                .bools,
            Bools::from(true)
        );
        assert_eq!(
            flag.refine(BinaryOp::Ne, true, true, &May::bool(true))
                .bools,
            Bools::from(false)
        );
    }

    #[test]
    fn booleans_and_display() {
        assert_eq!(Bools::from(false).and(Bools::BOTH), Bools::from(false));
        assert_eq!(Bools::BOTH.and(Bools::from(false)), Bools::from(false));
        assert_eq!(Bools::from(true).and(Bools::BOTH), Bools::BOTH);
        assert_eq!(Bools::from(true).or(Bools::EMPTY), Bools::from(true));
        assert_eq!(Bools::from(false).and(Bools::EMPTY), Bools::from(false));
        assert_eq!(Bools::from(true).and(Bools::EMPTY), Bools::EMPTY);
        assert_eq!(Bools::EMPTY.and(Bools::BOTH), Bools::EMPTY);
        assert_eq!(Bools::from(false).or(Bools::from(true)), Bools::from(true));
        assert_eq!(Bools::BOTH.eq(Bools::from(true)), Bools::BOTH);
        assert_eq!(Bools::from(true).eq(Bools::from(true)), Bools::from(true));
        assert_eq!(Bools::BOTH.to_string(), "{true, false}");
        assert_eq!(May::unit().shown(Ty::Unit).to_string(), "unit");
        assert_eq!(May::NONE.shown(Ty::Unit).to_string(), "∅");
        assert_eq!(May::bool(true).shown(Ty::Bool).to_string(), "{true}");
        assert_eq!(May::int(5.into()).shown(Ty::Int).to_string(), "[5, 5]");
    }

    #[test]
    fn rounding_keeps_points_signs_and_holes() {
        let t = [15, 2].map(Int::from).into_iter().collect::<Thresholds>();
        assert_eq!(ints("[7, 7]").round(&t), ints("[7, 7]"));
        assert_eq!(ints("[4, 13]").round(&t), ints("[3, 14]"));
        assert_eq!(ints("[4, 20]").round(&t), ints("[3, inf]"));
        assert_eq!(ints("[-20, 1]").round(&t), ints("[-inf, 1]"));
        assert_eq!(ints("[5, 100]").round(&t), ints("[3, inf]"));
        assert_eq!(ints("[-7, 7] \\ 0").round(&t), ints("[-inf, 14] \\ 0"));
        assert_eq!(ints("[-3, -2]").round(&t), ints("[-inf, -1]"));
        assert_eq!(Ints::EMPTY.round(&t), Ints::EMPTY);
        // The thresholds of no constants still keep a sign.
        let none = Thresholds::default();
        assert_eq!(ints("[2, 5]").round(&none), ints("[1, inf]"));
        assert_eq!(ints("[-5, -2]").round(&none), ints("[-inf, -1]"));
    }

    fn band() -> impl Strategy<Value = Ints> {
        (-20i64..20, 0i64..25, any::<bool>()).prop_map(|(lo, len, hole)| {
            Ints::band(Bound::finite(lo), Bound::finite(lo + len), hole)
        })
    }

    /// A band with endpoints that may be infinite, with and without a hole.
    fn any_band() -> impl Strategy<Value = (Ints, Ints)> {
        (
            proptest::option::of(-20i64..20),
            proptest::option::of(0i64..25),
        )
            .prop_map(|(lo, len)| {
                let hi = len.map_or(Bound::PosInf, |len| Bound::finite(lo.unwrap_or(0) + len));
                let lo = lo.map_or(Bound::NegInf, Bound::finite);
                (
                    Ints::band(lo.clone(), hi.clone(), false),
                    Ints::band(lo, hi, true),
                )
            })
    }

    fn members(band: &Ints) -> Vec<i64> {
        let Some(Band { lo, hi, hole }) = &band.0 else {
            return Vec::new();
        };
        let (Bound::Finite(lo), Bound::Finite(hi)) = (lo, hi) else {
            unreachable!("finite test bands");
        };
        let (lo, hi) = (i64::try_from(lo).unwrap(), i64::try_from(hi).unwrap());
        (lo..=hi).filter(|v| !(*hole && *v == 0)).collect()
    }

    fn contains(band: &Ints, value: i64) -> bool {
        band.0.as_ref().is_some_and(|band| {
            let value = Bound::finite(value);
            band.lo <= value && value <= band.hi && !(band.hole && value.sign() == Ordering::Equal)
        })
    }

    /// Every operator [`Op::apply`] reads.
    fn data_ops() -> Vec<Op> {
        let mut ops = vec![Op::Neg, Op::Not];
        ops.extend(
            [
                BinaryOp::Add,
                BinaryOp::Sub,
                BinaryOp::Mul,
                BinaryOp::Div,
                BinaryOp::Rem,
                BinaryOp::Eq,
                BinaryOp::Ne,
                BinaryOp::Lt,
                BinaryOp::Le,
                BinaryOp::Gt,
                BinaryOp::Ge,
            ]
            .map(Op::Binary),
        );
        for op in [
            BinaryOp::Lt,
            BinaryOp::Le,
            BinaryOp::Gt,
            BinaryOp::Ge,
            BinaryOp::Eq,
            BinaryOp::Ne,
        ] {
            for local_is_lhs in [false, true] {
                for sense in [false, true] {
                    ops.push(Op::Refine {
                        op,
                        local_is_lhs,
                        sense,
                    });
                }
            }
        }
        ops.extend([Op::Exactly(false), Op::Exactly(true)]);
        ops
    }

    /// Whether `value` is a member of `set`.
    fn member(set: &May, value: &Value) -> bool {
        match value {
            Value::Int(value) => contains(&set.ints, value.to_string().parse().unwrap()),
            Value::Bool(true) => set.bools.may_true(),
            Value::Bool(false) => set.bools.may_false(),
            Value::Unit => set.unit,
        }
    }

    /// Whether the read a narrowing operator guards is reached on `x`
    /// and `y`: the comparison holds in its sense. Any other operator is
    /// reached on anything.
    fn reached(op: &Op, x: &Value, y: &Value) -> bool {
        match *op {
            Op::Refine {
                op,
                local_is_lhs,
                sense,
            } => {
                let (lhs, rhs) = if local_is_lhs { (x, y) } else { (y, x) };
                Value::binary(op, lhs, rhs) == Ok(Value::Bool(sense))
            }
            Op::Exactly(value) => *x == Value::Bool(value),
            _ => true,
        }
    }

    /// An operand and a member of it: every integer of a finite band, and
    /// each boolean in every set that holds it, so every operator sees
    /// both types and the narrowings see a point.
    fn operands(band: &Ints) -> Vec<(May, Value)> {
        let mut pairs: Vec<_> = members(band)
            .into_iter()
            .map(|x| (May::ints(band.clone()), Value::Int(x.into())))
            .collect();
        for value in [false, true] {
            for set in [Bools::from(value), Bools::BOTH] {
                pairs.push((May::bools(set), Value::Bool(value)));
            }
        }
        pairs
    }

    proptest! {
        /// A shift past the words and back returns the hull it started
        /// from, and two negations return the band, hole included.
        #[test]
        fn shifts_past_the_words_round_trip((hull, holed) in any_band(), far in prop::sample::select(vec![i64::MAX, i64::MIN + 1, 1 << 62])) {
            let shift = Ints::from(Int::from(far));
            prop_assert_eq!(&(&(&hull + &shift) - &shift), &hull);
            prop_assert_eq!(&(&(&hull - &shift) + &shift), &hull);
            for band in [&hull, &holed] {
                prop_assert_eq!(&-&-band, band);
                let mut joined = band.clone();
                prop_assert!(!joined.join(band));
                prop_assert_eq!(&joined, band);
            }
        }

        /// Join is an upper bound of both, and rounding only widens.
        #[test]
        fn join_and_rounding_widen(a in band(), b in band(), constants in prop::collection::vec(-20i64..20, 0..4)) {
            let mut joined = a.clone();
            joined.join(&b);
            for x in members(&a).into_iter().chain(members(&b)) {
                prop_assert!(contains(&joined, x));
            }
            let thresholds = constants.into_iter().map(Int::from).collect::<Thresholds>();
            let rounded = a.round(&thresholds);
            for x in members(&a) {
                prop_assert!(contains(&rounded, x));
            }
            prop_assert_eq!(a.contains_zero(), rounded.contains_zero());
        }

        /// Soundness: the may-value of an operator over the sets contains
        /// its concrete value over any members, and where the concrete
        /// operator faults the may-domain still answers. The data
        /// operators are read through [`Op::apply`]; the lazy ones have no
        /// data node, so they are read directly.
        #[test]
        fn every_operator_over_approximates_the_concrete_one(a in band(), b in band()) {
            let ops = data_ops();
            for (set_a, x) in operands(&a) {
                for (set_b, y) in operands(&b) {
                    for op in &ops {
                        let arity = match op {
                            Op::Neg | Op::Not | Op::Exactly(_) => 1,
                            _ => 2,
                        };
                        let may = op.apply::<May>(&[&set_a, &set_b][..arity]).expect("the may-domain is total");
                        if let Ok(value) = op.apply::<Value>(&[&x, &y][..arity])
                            && reached(op, &x, &y)
                        {
                            prop_assert!(member(&may, &value), "{op:?} over {set_a:?}, {set_b:?} ∌ {value} from {x}, {y}");
                        }
                    }
                    for and in [false, true] {
                        let may = May::lazy(and, &set_a, &set_b).expect("the may-domain is total");
                        if let Ok(value) = Value::lazy(and, &x, &y) {
                            prop_assert!(member(&may, &value), "lazy {and} over {set_a:?}, {set_b:?} ∌ {value} from {x}, {y}");
                        }
                    }
                }
            }
        }
    }
}
