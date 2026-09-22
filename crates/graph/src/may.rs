//! The values that may reach a node, one set per scalar type, and the may-domain over them.
//! Reachability is no separate bit: a node with every set empty is unreachable.

use std::cmp::{Ordering, max, min};
use std::convert::Infallible;
use std::fmt;
use std::ops::{Add, BitAnd, Div, Mul, Neg, Rem, Sub};

use crate::{ArithOp, BinaryOp, CmpOp, Domain, Int, Ty};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Bound {
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

/// `0 · ±∞ = 0`; otherwise a corner of `[0, 0] · [1, +∞)` is infinite.
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

/// Integers as one band with an optional hole at zero, or nothing. Canonical: the hole is set only
/// when `lo < 0 < hi`, so equal sets compare equal.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ints(Option<Band>);

#[derive(Clone, Debug, PartialEq, Eq)]
struct Band {
    lo: Bound,
    hi: Bound,
    hole: bool,
}

impl From<Int> for Ints {
    fn from(value: Int) -> Self {
        let bound = Bound::Finite(value);
        Self::band(bound.clone(), bound, false)
    }
}

impl Ints {
    pub const EMPTY: Self = Self(None);
    pub const ALL: Self = Self(Some(Band {
        lo: Bound::NegInf,
        hi: Bound::PosInf,
        hole: false,
    }));

    /// The hull of indices in every start-inclusive, end-exclusive range of the two sets.
    pub fn range(start: &Self, end: &Self) -> Self {
        let (Some(start), Some(end)) = (&start.0, &end.0) else {
            return Self::EMPTY;
        };
        Self::band(start.lo.clone(), end.hi.pred(), false)
    }

    fn band(mut lo: Bound, mut hi: Bound, hole: bool) -> Self {
        if hole {
            if lo.sign() == Ordering::Equal {
                lo = lo.succ();
            }
            if hi.sign() == Ordering::Equal {
                hi = hi.pred();
            }
        }
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

    pub fn is_zero(&self) -> bool {
        self.0.as_ref().is_some_and(|band| {
            band.lo.sign() == Ordering::Equal && band.hi.sign() == Ordering::Equal
        })
    }

    fn is_point(&self) -> bool {
        self.0.as_ref().is_some_and(|band| band.lo == band.hi)
    }

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

    /// True when `self` grew.
    #[inline]
    pub fn join(&mut self, other: &Self) -> bool {
        let joined = match (&self.0, &other.0) {
            (_, None) => return false,
            (None, Some(_)) => other.clone(),
            (Some(a), Some(b))
                if a.lo <= b.lo && b.hi <= a.hi && (!a.hole || !other.contains_zero()) =>
            {
                return false;
            }
            (Some(a), Some(b)) => {
                let hole = !self.contains_zero() && !other.contains_zero();
                Self::band(min(&a.lo, &b.lo).clone(), max(&a.hi, &b.hi).clone(), hole)
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

    fn halves(&self) -> Vec<(Bound, Bound)> {
        let Some(Band { lo, hi, .. }) = &self.0 else {
            return Vec::new();
        };
        let mut halves = Vec::with_capacity(2);
        if lo.sign() == Ordering::Less {
            halves.push((lo.clone(), min(hi, &Bound::finite(-1)).clone()));
        }
        if hi.sign() == Ordering::Greater {
            halves.push((max(lo, &Bound::finite(1)).clone(), hi.clone()));
        }
        halves
    }

    fn compare(&self, op: CmpOp, other: &Self) -> Bools {
        let (Some(a), Some(b)) = (&self.0, &other.0) else {
            return Bools::EMPTY;
        };
        let (may_true, may_false) = match op {
            CmpOp::Lt => (a.lo < b.hi, a.hi >= b.lo),
            CmpOp::Le => (a.lo <= b.hi, a.hi > b.lo),
            CmpOp::Gt => (a.hi > b.lo, a.lo <= b.hi),
            CmpOp::Ge => (a.hi >= b.lo, a.lo < b.hi),
            CmpOp::Eq | CmpOp::Ne => {
                let equal = !(self & other).is_empty();
                let unequal = !(self.is_point() && self == other);
                if op == CmpOp::Eq {
                    (equal, unequal)
                } else {
                    (unequal, equal)
                }
            }
        };
        Bools::of(may_true, may_false)
    }

    fn refine(&self, op: CmpOp, other: &Self) -> Self {
        let (Some(Band { lo, hi, hole }), Some(b)) = (&self.0, &other.0) else {
            return Self::EMPTY;
        };
        match op {
            CmpOp::Lt => Self::band(lo.clone(), min(hi, &b.hi.pred()).clone(), *hole),
            CmpOp::Le => Self::band(lo.clone(), min(hi, &b.hi).clone(), *hole),
            CmpOp::Gt => Self::band(max(lo, &b.lo.succ()).clone(), hi.clone(), *hole),
            CmpOp::Ge => Self::band(max(lo, &b.lo).clone(), hi.clone(), *hole),
            CmpOp::Eq => self & other,
            CmpOp::Ne => {
                if other.is_point() {
                    self.without(&b.lo)
                } else {
                    self.clone()
                }
            }
        }
    }

    /// Each endpoint widened outward to a threshold; a point stays exact.
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

impl BitAnd<&Ints> for &Ints {
    type Output = Ints;
    fn bitand(self, other: &Ints) -> Ints {
        match (&self.0, &other.0) {
            (Some(a), Some(b)) => Ints::band(
                max(&a.lo, &b.lo).clone(),
                min(&a.hi, &b.hi).clone(),
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
                Ints::band(lo, hi, !self.contains_zero() && !other.contains_zero())
            }
            _ => Ints::EMPTY,
        }
    }
}

/// Empty over a divisor that is only zero; a wider divisor's zero is skipped.
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

/// Empty over a divisor that is only zero.
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
            max(&a.lo, &-&limit).clone()
        };
        let hi = if a.hi.sign() != Ordering::Greater {
            Bound::zero()
        } else {
            min(&a.hi, &limit).clone()
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

    /// A left `false` never runs the right side, so an empty right side keeps it.
    fn and(self, other: Self) -> Self {
        Self::of(
            self.may_true() && other.may_true(),
            self.may_false() || (self.may_true() && other.may_false()),
        )
    }

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

impl BitAnd for Bools {
    type Output = Self;
    fn bitand(self, other: Self) -> Self {
        Self(self.0 & other.0)
    }
}

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

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct May {
    pub ints: Ints,
    pub bools: Bools,
    pub unit: bool,
}

impl May {
    pub const NONE: Self = Self {
        ints: Ints::EMPTY,
        bools: Bools::EMPTY,
        unit: false,
    };

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

    pub fn every(ty: Ty) -> Self {
        match ty {
            Ty::Int => Self::ints(Ints::ALL),
            Ty::Bool => Self::bools(Bools::BOTH),
            Ty::Unit => Self::of_unit(true),
        }
    }

    #[inline]
    pub fn live(&self) -> bool {
        !self.ints.is_empty() || !self.bools.is_empty() || self.unit
    }

    /// True when `self` grew.
    pub fn join(&mut self, other: &Self) -> bool {
        let ints = self.ints.join(&other.ints);
        let bools = self.bools.join(other.bools);
        let unit = !self.unit && other.unit;
        self.unit |= other.unit;
        ints | bools | unit
    }

    pub fn shown(&self, ty: Ty) -> Shown<'_> {
        Shown(self, ty)
    }
}

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

/// The values an endpoint rounds to: the constants collected, each ±1, and always `-1`, `0`, and
/// `1`, so rounding keeps a band's sign.
#[derive(Clone, Debug)]
pub struct Thresholds(Vec<Int>);

impl Default for Thresholds {
    fn default() -> Self {
        std::iter::empty().collect()
    }
}

impl FromIterator<Int> for Thresholds {
    fn from_iter<I: IntoIterator<Item = Int>>(constants: I) -> Self {
        let one = Int::from(1);
        let constants: Vec<Int> = constants.into_iter().collect();
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
    fn below(&self, value: &Int) -> Bound {
        let index = self.0.partition_point(|threshold| threshold <= value);
        match index.checked_sub(1) {
            Some(index) => Bound::Finite(self.0[index].clone()),
            None => Bound::NegInf,
        }
    }

    fn above(&self, value: &Int) -> Bound {
        let index = self.0.partition_point(|threshold| threshold < value);
        match self.0.get(index) {
            Some(threshold) => Bound::Finite(threshold.clone()),
            None => Bound::PosInf,
        }
    }
}

/// Every operator over-approximates the concrete one on every member of its operands.
impl Domain for May {
    type Fault = Infallible;

    #[inline]
    fn int(value: &Int) -> Self {
        Self::ints(Ints::from(value.clone()))
    }

    #[inline]
    fn bool(value: bool) -> Self {
        Self::bools(Bools::from(value))
    }

    #[inline]
    fn unit() -> Self {
        Self::of_unit(true)
    }

    #[inline]
    fn neg(&self) -> Result<Self, Infallible> {
        Ok(Self::ints(-&self.ints))
    }

    #[inline]
    fn not(&self) -> Result<Self, Infallible> {
        Ok(Self::bools(!self.bools))
    }

    #[inline]
    fn binary(op: BinaryOp, lhs: &Self, rhs: &Self) -> Result<Self, Infallible> {
        Ok(match op {
            BinaryOp::Arith(op) => Self::ints(match op {
                ArithOp::Add => &lhs.ints + &rhs.ints,
                ArithOp::Sub => &lhs.ints - &rhs.ints,
                ArithOp::Mul => &lhs.ints * &rhs.ints,
                ArithOp::Div => &lhs.ints / &rhs.ints,
                ArithOp::Rem => &lhs.ints % &rhs.ints,
            }),
            BinaryOp::Cmp(op @ (CmpOp::Eq | CmpOp::Ne)) => {
                let mut bools = lhs.ints.compare(op, &rhs.ints);
                let of_bools = lhs.bools.eq(rhs.bools);
                bools.join(if op == CmpOp::Eq { of_bools } else { !of_bools });
                Self::bools(bools)
            }
            BinaryOp::Cmp(op) => Self::bools(lhs.ints.compare(op, &rhs.ints)),
        })
    }

    #[inline]
    fn lazy(and: bool, lhs: &Self, rhs: &Self) -> Result<Self, Infallible> {
        Ok(Self::bools(if and {
            lhs.bools.and(rhs.bools)
        } else {
            lhs.bools.or(rhs.bools)
        }))
    }

    #[inline]
    fn refine(&self, op: CmpOp, local_is_lhs: bool, sense: bool, other: &Self) -> Self {
        let op = if local_is_lhs { op } else { op.flip() };
        let op = if sense { op } else { op.negate() };
        let bools = match op {
            CmpOp::Eq => self.bools & other.bools,
            CmpOp::Ne if other.bools == Bools::from(true) || other.bools == Bools::from(false) => {
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
    fn loop_ranges_use_outer_endpoints_without_zero_holes() {
        for (start, end, expected) in [
            ("[2, 8]", "[4, 12]", "[2, 11]"),
            ("[8, 9]", "[1, 8]", "∅"),
            ("[9, 10]", "[-2, 8]", "∅"),
            ("∅", "[1, 8]", "∅"),
            ("[1, 8]", "∅", "∅"),
            ("[-3, 5] \\ 0", "[-2, 9] \\ 0", "[-3, 8]"),
            ("[-inf, 4]", "[2, inf]", "[-inf, inf]"),
            ("[3, inf]", "[-inf, 7]", "[3, 6]"),
        ] {
            assert_eq!(Ints::range(&ints(start), &ints(end)), ints(expected));
        }
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
    fn every_value_of_a_type_is_admitted() {
        assert_eq!(Ints::ALL, ints("[-inf, inf]"));
        assert!(Ints::ALL.contains_zero());
        assert_eq!(May::every(Ty::Bool).bools, Bools::BOTH);
        assert!(May::every(Ty::Unit).unit);
        for ty in Ty::ALL {
            assert!(May::every(ty).live());
        }
    }

    #[test]
    fn comparisons_and_refinements_agree() {
        let n = ints("[0, 15]");
        assert_eq!(n.compare(CmpOp::Lt, &ints("[2, 2]")), Bools::BOTH);
        assert_eq!(
            ints("[0, 1]").compare(CmpOp::Lt, &ints("[2, 2]")),
            Bools::from(true)
        );
        assert_eq!(
            ints("[2, 9]").compare(CmpOp::Lt, &ints("[2, 2]")),
            Bools::from(false)
        );
        assert_eq!(
            ints("[-5, 5] \\ 0").compare(CmpOp::Eq, &ints("[0, 0]")),
            Bools::from(false)
        );
        assert_eq!(
            ints("[3, 3]").compare(CmpOp::Ne, &ints("[3, 3]")),
            Bools::from(false)
        );
        assert_eq!(n.refine(CmpOp::Lt, &ints("[2, 2]")), ints("[0, 1]"));
        assert_eq!(n.refine(CmpOp::Ge, &ints("[2, 2]")), ints("[2, 15]"));
        assert_eq!(n.refine(CmpOp::Ne, &ints("[0, 0]")), ints("[1, 15]"));
        assert_eq!(
            ints("[-5, 5]").refine(CmpOp::Ne, &ints("[0, 0]")),
            ints("[-5, 5] \\ 0")
        );
        assert_eq!(n.refine(CmpOp::Eq, &ints("[10, 20]")), ints("[10, 15]"));
        assert_eq!(n.refine(CmpOp::Gt, &ints("[20, 20]")), Ints::EMPTY);
        assert_eq!(n.refine(CmpOp::Ne, &ints("[1, 2]")), n);
        let may = May::ints(n.clone());
        let two = May::int(&2.into());
        assert_eq!(
            may.refine(CmpOp::Gt, false, true, &two).ints,
            ints("[0, 1]")
        );
        assert_eq!(
            may.refine(CmpOp::Gt, false, false, &two).ints,
            ints("[2, 15]")
        );
        let flag = May::bools(Bools::BOTH);
        assert_eq!(
            flag.refine(CmpOp::Eq, true, true, &May::bool(true)).bools,
            Bools::from(true)
        );
        assert_eq!(
            flag.refine(CmpOp::Ne, true, true, &May::bool(true)).bools,
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
        assert_eq!(May::int(&5.into()).shown(Ty::Int).to_string(), "[5, 5]");
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
        let none = Thresholds::default();
        assert_eq!(ints("[2, 5]").round(&none), ints("[1, inf]"));
        assert_eq!(ints("[-5, -2]").round(&none), ints("[-inf, -1]"));
    }

    fn band() -> impl Strategy<Value = Ints> {
        (-20i64..20, 0i64..25, any::<bool>()).prop_map(|(lo, len, hole)| {
            Ints::band(Bound::finite(lo), Bound::finite(lo + len), hole)
        })
    }

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

    fn data_ops() -> Vec<Op> {
        let mut ops = vec![Op::Neg, Op::Not];
        ops.extend(ArithOp::ALL.map(BinaryOp::Arith).map(Op::Binary));
        ops.extend(CmpOp::ALL.map(BinaryOp::Cmp).map(Op::Binary));
        for op in CmpOp::ALL {
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

    fn member(set: &May, value: &Value) -> bool {
        match value {
            Value::Int(value) => contains(&set.ints, value.to_string().parse().unwrap()),
            Value::Bool(true) => set.bools.may_true(),
            Value::Bool(false) => set.bools.may_false(),
            Value::Unit => set.unit,
        }
    }

    fn reached(op: &Op, x: &Value, y: &Value) -> bool {
        match *op {
            Op::Refine {
                op,
                local_is_lhs,
                sense,
            } => {
                let (lhs, rhs) = if local_is_lhs { (x, y) } else { (y, x) };
                Value::binary(BinaryOp::Cmp(op), lhs, rhs) == Ok(Value::Bool(sense))
            }
            Op::Exactly(value) => *x == Value::Bool(value),
            _ => true,
        }
    }

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
                        let Ok(may) = op.apply::<May>(&[&set_a, &set_b][..arity]);
                        if let Ok(value) = op.apply::<Value>(&[&x, &y][..arity])
                            && reached(op, &x, &y)
                        {
                            prop_assert!(member(&may, &value), "{op:?} over {set_a:?}, {set_b:?} ∌ {value} from {x}, {y}");
                        }
                    }
                    for and in [false, true] {
                        let Ok(may) = May::lazy(and, &set_a, &set_b);
                        if let Ok(value) = Value::lazy(and, &x, &y) {
                            prop_assert!(member(&may, &value), "lazy {and} over {set_a:?}, {set_b:?} ∌ {value} from {x}, {y}");
                        }
                    }
                }
            }
        }
    }
}
