//! Sets of scalar values, described finitely: a band of integers over
//! ℤ ∪ {±∞} with an optional hole at zero, and a set of booleans.
//!
//! The band with a hole is the shape a guard leaves: `d != 0` on a signed
//! `d` excludes one point from the middle, and a product of two such bands
//! keeps the hole, so a division by either side stays provably safe. Every
//! operation is total and sound: the result of an operation on two bands
//! contains the result of the operation on any two of their members, which
//! a property test checks against the concrete integers.

use std::cmp::Ordering;
use std::fmt;

use crate::{BinaryOp, Int};

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

/// A set of integers: nothing, or a band with an optional hole at zero. The hole is canonical: it is set only when `lo < 0 < hi`,
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

    /// Every integer.
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

    pub fn neg(&self) -> Self {
        match self.parts() {
            None => Self::Empty,
            Some((lo, hi, hole)) => Self::band(hi.neg(), lo.neg(), hole),
        }
    }

    pub fn add(&self, other: &Self) -> Self {
        match (self.parts(), other.parts()) {
            (Some((lo1, hi1, _)), Some((lo2, hi2, _))) => {
                Self::band(lo1.add(lo2), hi1.add(hi2), false)
            }
            _ => Self::Empty,
        }
    }

    pub fn sub(&self, other: &Self) -> Self {
        match (self.parts(), other.parts()) {
            (Some((lo1, hi1, _)), Some((lo2, hi2, _))) => {
                Self::band(lo1.sub(hi2), hi1.sub(lo2), false)
            }
            _ => Self::Empty,
        }
    }

    pub fn mul(&self, other: &Self) -> Self {
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
    pub fn div(&self, other: &Self) -> Self {
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
    pub fn rem(&self, other: &Self) -> Self {
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
    pub fn compare(&self, op: BinaryOp, other: &Self) -> Bools {
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

/// A set of booleans.
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

    /// `self && other`: the right operand runs only when the left is true,
    /// so an empty right side still leaves `false` from the left.
    pub fn and(self, other: Self) -> Self {
        Self::of(
            self.may_true() && other.may_true(),
            self.may_false() || (self.may_true() && other.may_false()),
        )
    }

    /// `self || other`, likewise.
    pub fn or(self, other: Self) -> Self {
        Self::of(
            self.may_true() || (self.may_false() && other.may_true()),
            self.may_false() && other.may_false(),
        )
    }

    pub fn eq(self, other: Self) -> Self {
        if self.is_empty() || other.is_empty() {
            return Self::EMPTY;
        }
        let same = self.0 & other.0 != 0;
        let differ =
            (self.may_true() && other.may_false()) || (self.may_false() && other.may_true());
        Self::of(same, differ)
    }

    pub fn join(&mut self, other: Self) -> bool {
        let before = self.0;
        self.0 |= other.0;
        before != self.0
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
    fn comparisons_over_bands() {
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
        /// Every operation over-approximates the concrete operation on every
        /// member of its operands, which is soundness.
        #[test]
        fn operations_are_sound(a in band(), b in band()) {
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
                    }
                }
            }
        }

        /// Join is an upper bound of both.
        #[test]
        fn join_is_a_hull(a in band(), b in band()) {
            let mut joined = a.clone();
            joined.join(&b);
            for x in members(&a).into_iter().chain(members(&b)) {
                prop_assert!(contains(&joined, x));
            }
        }
    }
}
