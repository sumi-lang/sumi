//! Mathematical integers: the value of every `int` literal and, in the
//! interpreter, of every `int` expression.
//!
//! `int` denotes ℤ. There is no width to overflow, so `+`, `-`, `*`, and
//! negation are total, and division fails only on a zero divisor. The
//! representation is the compiler's concern, not the language's: a value
//! that fits a machine word stays in one, so the common program never
//! allocates, and past that the magnitude is a boxed run of limbs.

use std::borrow::Cow;
use std::cmp::Ordering;
use std::fmt;
use std::ops::{Add, Mul, Neg, Sub};
use std::str::FromStr;

/// An integer of any size: two words, one of them a pointer only past the
/// word-sized range.
#[derive(Clone, PartialEq, Eq)]
pub struct Int(Repr);

/// `Big` holds only what `Small` cannot, so equal values have equal
/// representations and the derived equality is the mathematical one.
#[derive(Clone, PartialEq, Eq)]
enum Repr {
    Small(i64),
    /// A value outside `i64`.
    Big(Box<Big>),
}

/// A sign and a magnitude's limbs, least significant first, the last one
/// non-zero.
#[derive(Clone, PartialEq, Eq)]
struct Big {
    negative: bool,
    limbs: Box<[u64]>,
}

/// A sign and a magnitude, the form the slow paths compute in. Zero is
/// non-negative with no limbs; otherwise the last limb is non-zero.
struct Parts<'a> {
    negative: bool,
    limbs: Cow<'a, [u64]>,
}

impl Int {
    fn parts(&self) -> Parts<'_> {
        match &self.0 {
            Repr::Small(0) => Parts {
                negative: false,
                limbs: Cow::Borrowed(&[]),
            },
            Repr::Small(value) => Parts {
                negative: *value < 0,
                limbs: Cow::Owned(vec![value.unsigned_abs()]),
            },
            Repr::Big(big) => Parts {
                negative: big.negative,
                limbs: Cow::Borrowed(&big.limbs),
            },
        }
    }

    /// The one way to build a value from its parts: it lands in `Small`
    /// whenever it fits there.
    fn from_parts(negative: bool, limbs: Vec<u64>) -> Self {
        let limbs = trim(limbs);
        match limbs.as_slice() {
            [] => Self(Repr::Small(0)),
            &[limb] if negative && limb <= 1 << 63 => {
                // `1 << 63` is `i64::MIN` reinterpreted, and its wrapping
                // negation is itself: exactly the value wanted.
                Self(Repr::Small((limb as i64).wrapping_neg()))
            }
            &[limb] if !negative && limb <= i64::MAX as u64 => Self(Repr::Small(limb as i64)),
            _ => Self(Repr::Big(Box::new(Big {
                negative,
                limbs: limbs.into_boxed_slice(),
            }))),
        }
    }

    /// `self ± rhs`, past the word-sized fast path.
    fn combine(&self, rhs: &Self, subtract: bool) -> Self {
        let (a, mut b) = (self.parts(), rhs.parts());
        b.negative ^= subtract;
        if a.negative == b.negative {
            Self::from_parts(a.negative, add_mag(&a.limbs, &b.limbs))
        } else if cmp_mag(&a.limbs, &b.limbs) == Ordering::Less {
            Self::from_parts(b.negative, sub_mag(&b.limbs, &a.limbs))
        } else {
            Self::from_parts(a.negative, sub_mag(&a.limbs, &b.limbs))
        }
    }

    /// Truncating division: the quotient rounds toward zero and the
    /// remainder takes the dividend's sign. `None` for a zero divisor.
    fn div_rem(&self, rhs: &Self) -> Option<(Self, Self)> {
        if let (Repr::Small(a), Repr::Small(b)) = (&self.0, &rhs.0)
            && let (Some(quotient), Some(remainder)) = (a.checked_div(*b), a.checked_rem(*b))
        {
            return Some((quotient.into(), remainder.into()));
        }
        let (a, b) = (self.parts(), rhs.parts());
        if b.limbs.is_empty() {
            return None;
        }
        let (quotient, remainder) = div_rem_mag(&a.limbs, &b.limbs);
        Some((
            Self::from_parts(a.negative != b.negative, quotient),
            Self::from_parts(a.negative, remainder),
        ))
    }

    /// The quotient rounded toward zero, or `None` for a zero divisor.
    pub fn checked_div(&self, rhs: &Self) -> Option<Self> {
        self.div_rem(rhs).map(|(quotient, _)| quotient)
    }

    /// The remainder of [`Int::checked_div`], with the dividend's sign, or
    /// `None` for a zero divisor.
    pub fn checked_rem(&self, rhs: &Self) -> Option<Self> {
        self.div_rem(rhs).map(|(_, remainder)| remainder)
    }

    /// The value as a machine word, if it fits.
    pub fn to_i64(&self) -> Option<i64> {
        match self.0 {
            Repr::Small(value) => Some(value),
            Repr::Big(_) => None,
        }
    }
}

impl From<i64> for Int {
    fn from(value: i64) -> Self {
        Self(Repr::Small(value))
    }
}

impl Add<&Int> for &Int {
    type Output = Int;
    fn add(self, rhs: &Int) -> Int {
        if let (Repr::Small(a), Repr::Small(b)) = (&self.0, &rhs.0)
            && let Some(sum) = a.checked_add(*b)
        {
            return sum.into();
        }
        self.combine(rhs, false)
    }
}

impl Sub<&Int> for &Int {
    type Output = Int;
    fn sub(self, rhs: &Int) -> Int {
        if let (Repr::Small(a), Repr::Small(b)) = (&self.0, &rhs.0)
            && let Some(difference) = a.checked_sub(*b)
        {
            return difference.into();
        }
        self.combine(rhs, true)
    }
}

impl Mul<&Int> for &Int {
    type Output = Int;
    fn mul(self, rhs: &Int) -> Int {
        if let (Repr::Small(a), Repr::Small(b)) = (&self.0, &rhs.0)
            && let Some(product) = a.checked_mul(*b)
        {
            return product.into();
        }
        let (a, b) = (self.parts(), rhs.parts());
        Int::from_parts(a.negative != b.negative, mul_mag(&a.limbs, &b.limbs))
    }
}

impl Neg for &Int {
    type Output = Int;
    fn neg(self) -> Int {
        if let Repr::Small(value) = self.0
            && let Some(negated) = value.checked_neg()
        {
            return negated.into();
        }
        let parts = self.parts();
        Int::from_parts(!parts.negative, parts.limbs.into_owned())
    }
}

impl Ord for Int {
    fn cmp(&self, other: &Self) -> Ordering {
        if let (Repr::Small(a), Repr::Small(b)) = (&self.0, &other.0) {
            return a.cmp(b);
        }
        let (a, b) = (self.parts(), other.parts());
        match (a.negative, b.negative) {
            (false, true) => Ordering::Greater,
            (true, false) => Ordering::Less,
            (false, false) => cmp_mag(&a.limbs, &b.limbs),
            (true, true) => cmp_mag(&b.limbs, &a.limbs),
        }
    }
}

impl PartialOrd for Int {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Decimal digits, as source spells them.
impl fmt::Display for Int {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (negative, limbs) = match &self.0 {
            Repr::Small(value) => return fmt::Display::fmt(value, f),
            Repr::Big(big) => (big.negative, &big.limbs),
        };
        // Peel groups of nineteen digits, the most a limb's division can
        // deliver at once, least significant first.
        let mut groups = Vec::new();
        let mut magnitude = limbs.to_vec();
        while !magnitude.is_empty() {
            let (quotient, group) = div_rem_limb(&magnitude, DIGIT_GROUP);
            groups.push(group);
            magnitude = quotient;
        }
        let mut digits = groups.pop().unwrap_or(0).to_string();
        for group in groups.iter().rev() {
            digits.push_str(&format!("{group:019}"));
        }
        f.pad_integral(!negative, "", &digits)
    }
}

impl fmt::Debug for Int {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

/// Ten to the nineteenth: the largest power of ten a limb holds.
const DIGIT_GROUP: u64 = 10_000_000_000_000_000_000;

/// The text was not an optional `-` followed by ASCII digits.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ParseIntError;

impl fmt::Display for ParseIntError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("expected an optional `-` followed by decimal digits")
    }
}

impl std::error::Error for ParseIntError {}

/// Decimal digits with an optional leading `-`, of any length.
impl FromStr for Int {
    type Err = ParseIntError;
    fn from_str(text: &str) -> Result<Self, ParseIntError> {
        let (negative, digits) = match text.strip_prefix('-') {
            Some(digits) => (true, digits),
            None => (false, text),
        };
        if digits.is_empty() || !digits.bytes().all(|byte| byte.is_ascii_digit()) {
            return Err(ParseIntError);
        }
        if let Ok(value) = text.parse::<i64>() {
            return Ok(value.into());
        }
        let mut magnitude = Vec::new();
        for group in digits.as_bytes().chunks(19) {
            let value = group
                .iter()
                .fold(0, |value, byte| value * 10 + u64::from(byte - b'0'));
            let scale = 10u64.pow(u32::try_from(group.len()).expect("at most 19"));
            magnitude = mul_limb_add(&magnitude, scale, value);
        }
        Ok(Self::from_parts(negative, magnitude))
    }
}

// Magnitude arithmetic over little-endian limbs. Every argument and result
// is trimmed: no trailing zero limb, and zero is the empty run.

fn trim(mut limbs: Vec<u64>) -> Vec<u64> {
    while limbs.last() == Some(&0) {
        limbs.pop();
    }
    limbs
}

fn cmp_mag(a: &[u64], b: &[u64]) -> Ordering {
    a.len()
        .cmp(&b.len())
        .then_with(|| a.iter().rev().cmp(b.iter().rev()))
}

fn add_mag(a: &[u64], b: &[u64]) -> Vec<u64> {
    let (long, short) = if a.len() >= b.len() { (a, b) } else { (b, a) };
    let mut out = Vec::with_capacity(long.len() + 1);
    let mut carry = 0;
    for (index, &x) in long.iter().enumerate() {
        let y = short.get(index).copied().unwrap_or(0);
        let (sum, first) = x.overflowing_add(y);
        let (sum, second) = sum.overflowing_add(carry);
        out.push(sum);
        carry = u64::from(first) + u64::from(second);
    }
    out.push(carry);
    trim(out)
}

/// `a - b`, for `a >= b`.
fn sub_mag(a: &[u64], b: &[u64]) -> Vec<u64> {
    debug_assert!(cmp_mag(a, b) != Ordering::Less);
    let mut out = Vec::with_capacity(a.len());
    let mut borrow = 0;
    for (index, &x) in a.iter().enumerate() {
        let y = b.get(index).copied().unwrap_or(0);
        let (difference, first) = x.overflowing_sub(y);
        let (difference, second) = difference.overflowing_sub(borrow);
        out.push(difference);
        borrow = u64::from(first) + u64::from(second);
    }
    debug_assert_eq!(borrow, 0);
    trim(out)
}

fn mul_mag(a: &[u64], b: &[u64]) -> Vec<u64> {
    if a.is_empty() || b.is_empty() {
        return Vec::new();
    }
    let mut out = vec![0; a.len() + b.len()];
    for (i, &x) in a.iter().enumerate() {
        let mut carry = 0;
        for (j, &y) in b.iter().enumerate() {
            let term = u128::from(x) * u128::from(y) + u128::from(out[i + j]) + carry;
            out[i + j] = term as u64;
            carry = term >> 64;
        }
        out[i + b.len()] = carry as u64;
    }
    trim(out)
}

/// `a * scale + addend`.
fn mul_limb_add(a: &[u64], scale: u64, addend: u64) -> Vec<u64> {
    let mut out = Vec::with_capacity(a.len() + 1);
    let mut carry = u128::from(addend);
    for &x in a {
        let term = u128::from(x) * u128::from(scale) + carry;
        out.push(term as u64);
        carry = term >> 64;
    }
    out.push(carry as u64);
    trim(out)
}

/// `a / d` and `a % d` for a non-zero limb `d`.
fn div_rem_limb(a: &[u64], d: u64) -> (Vec<u64>, u64) {
    let mut quotient = vec![0; a.len()];
    let mut remainder = 0u128;
    for (index, &x) in a.iter().enumerate().rev() {
        let current = (remainder << 64) | u128::from(x);
        quotient[index] = (current / u128::from(d)) as u64;
        remainder = current % u128::from(d);
    }
    (trim(quotient), remainder as u64)
}

/// `a / b` and `a % b` for non-zero `b`.
fn div_rem_mag(a: &[u64], b: &[u64]) -> (Vec<u64>, Vec<u64>) {
    if cmp_mag(a, b) == Ordering::Less {
        return (Vec::new(), a.to_vec());
    }
    if let &[d] = b {
        let (quotient, remainder) = div_rem_limb(a, d);
        return (quotient, trim(vec![remainder]));
    }
    // Long division one bit at a time: bring the dividend's bits down into
    // the remainder from the top, and subtract the divisor whenever it fits.
    let mut quotient = vec![0; a.len()];
    let mut remainder = Vec::new();
    for bit in (0..a.len() * 64).rev() {
        shift_in(&mut remainder, (a[bit / 64] >> (bit % 64)) & 1);
        if cmp_mag(&remainder, b) != Ordering::Less {
            remainder = sub_mag(&remainder, b);
            quotient[bit / 64] |= 1 << (bit % 64);
        }
    }
    (trim(quotient), remainder)
}

/// Double `limbs` and add `bit`.
fn shift_in(limbs: &mut Vec<u64>, bit: u64) {
    let mut carry = bit;
    for limb in limbs.iter_mut() {
        let next = *limb >> 63;
        *limb = (*limb << 1) | carry;
        carry = next;
    }
    if carry != 0 {
        limbs.push(carry);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    fn int(text: &str) -> Int {
        text.parse().unwrap()
    }

    /// The value as the host computes it; every test value fits.
    fn i128_of(value: &Int) -> i128 {
        value.to_string().parse().unwrap()
    }

    fn is_small(value: &Int) -> bool {
        matches!(value.0, Repr::Small(_))
    }

    #[test]
    fn an_int_is_two_words() {
        assert_eq!(size_of::<Int>(), 16);
        assert_eq!(Int::from(7).to_i64(), Some(7));
        assert_eq!(int("9223372036854775808").to_i64(), None);
    }

    #[test]
    fn parsing_and_display_round_trip() {
        for text in [
            "0",
            "-1",
            "42",
            "9223372036854775807",
            "-9223372036854775808",
            "9223372036854775808",
            "-9223372036854775809",
            "18446744073709551615",
            "18446744073709551616",
            "100000000000000000000",
            "-100000000000000000000",
            "1234567890123456789012345678901234567890",
            "340282366920938463463374607431768211456",
        ] {
            let value = int(text);
            assert_eq!(value.to_string(), text);
            assert_eq!(format!("{value:?}"), text);
            assert_eq!(
                is_small(&value),
                text.parse::<i64>().is_ok(),
                "{text} lands in the right representation"
            );
        }
        assert_eq!(int("007"), Int::from(7));
        assert_eq!(int("-0"), Int::from(0));
        for text in ["", "-", "+1", "1_000", "1e5", "0x10", " 1", "١"] {
            assert_eq!(text.parse::<Int>(), Err(ParseIntError), "{text:?}");
        }
        assert_eq!(
            format!("{:>25}|{:<25}|", int("-9223372036854775809"), int("5")),
            "     -9223372036854775809|5                        |"
        );
    }

    #[test]
    fn boundaries_move_between_representations() {
        let max = Int::from(i64::MAX);
        let min = Int::from(i64::MIN);
        let one = Int::from(1);
        let past_max = &max + &one;
        assert_eq!(past_max.to_string(), "9223372036854775808");
        assert!(!is_small(&past_max));
        assert!(is_small(&(&past_max - &one)));
        assert_eq!(&past_max - &one, max);
        let past_min = &min - &one;
        assert_eq!(past_min.to_string(), "-9223372036854775809");
        assert!(!is_small(&past_min));
        assert_eq!(&past_min + &one, min);
        assert_eq!((-&min).to_string(), "9223372036854775808");
        assert_eq!(-&(-&min), min);
        assert_eq!(
            min.checked_div(&Int::from(-1)).unwrap().to_string(),
            "9223372036854775808"
        );
        assert_eq!(min.checked_rem(&Int::from(-1)), Some(Int::from(0)));
        assert_eq!((&max * &Int::from(2)).to_string(), "18446744073709551614");
        assert_eq!(
            &int("18446744073709551614") + &int("-9223372036854775807"),
            max
        );
    }

    #[test]
    fn division_is_truncating_and_total_except_for_zero() {
        for (a, b, q, r) in [
            ("7", "2", "3", "1"),
            ("-7", "2", "-3", "-1"),
            ("7", "-2", "-3", "1"),
            ("-7", "-2", "3", "-1"),
            (
                "1234567890123456789012345678901234567890",
                "1000000000000000000000",
                "1234567890123456789",
                "12345678901234567890",
            ),
            (
                "-1234567890123456789012345678901234567890",
                "1000000000000000000000",
                "-1234567890123456789",
                "-12345678901234567890",
            ),
            (
                "340282366920938463463374607431768211456",
                "18446744073709551616",
                "18446744073709551616",
                "0",
            ),
            (
                "340282366920938463463374607431768211457",
                "18446744073709551617",
                "18446744073709551615",
                "2",
            ),
            ("5", "1234567890123456789012345678901234567890", "0", "5"),
        ] {
            let (a, b) = (int(a), int(b));
            assert_eq!(a.checked_div(&b), Some(int(q)), "{a} / {b}");
            assert_eq!(a.checked_rem(&b), Some(int(r)), "{a} % {b}");
        }
        let zero = Int::from(0);
        for a in [
            "0",
            "1",
            "-9223372036854775808",
            "1234567890123456789012345678901234567890",
        ] {
            assert_eq!(int(a).checked_div(&zero), None);
            assert_eq!(int(a).checked_rem(&zero), None);
        }
    }

    #[test]
    fn ordering_spans_both_representations() {
        let sorted = [
            "-1234567890123456789012345678901234567890",
            "-9223372036854775809",
            "-9223372036854775808",
            "-1",
            "0",
            "1",
            "9223372036854775807",
            "9223372036854775808",
            "18446744073709551616",
            "1234567890123456789012345678901234567890",
        ]
        .map(int);
        for (i, a) in sorted.iter().enumerate() {
            for (j, b) in sorted.iter().enumerate() {
                assert_eq!(a.cmp(b), i.cmp(&j), "{a} against {b}");
                assert_eq!(a == b, i == j);
            }
        }
    }

    proptest! {
        /// Every operation agrees with 128-bit host arithmetic wherever the
        /// host can compute it, and lands in `Small` exactly when it fits.
        #[test]
        fn agrees_with_the_host(a in any::<i64>(), b in any::<i64>()) {
            let (x, y) = (Int::from(a), Int::from(b));
            let (wide_a, wide_b) = (i128::from(a), i128::from(b));
            for (name, got, want) in [
                ("+", &x + &y, wide_a + wide_b),
                ("-", &x - &y, wide_a - wide_b),
                ("*", &x * &y, wide_a * wide_b),
                ("neg", -&x, -wide_a),
            ] {
                prop_assert_eq!(i128_of(&got), want, "{}", name);
                prop_assert_eq!(is_small(&got), i64::try_from(want).is_ok(), "{}", name);
            }
            prop_assert_eq!(x.cmp(&y), a.cmp(&b));
            if b != 0 {
                prop_assert_eq!(i128_of(&x.checked_div(&y).unwrap()), wide_a / wide_b);
                prop_assert_eq!(i128_of(&x.checked_rem(&y).unwrap()), wide_a % wide_b);
            } else {
                prop_assert_eq!(x.checked_div(&y), None);
            }
        }

        /// Multi-limb division satisfies the division identity with a
        /// remainder smaller than the divisor.
        #[test]
        fn wide_division_identity(
            a in prop::collection::vec(any::<u64>(), 0..5),
            b in prop::collection::vec(any::<u64>(), 1..4),
            negative_a in any::<bool>(),
            negative_b in any::<bool>(),
        ) {
            let a = Int::from_parts(negative_a, a);
            let b = Int::from_parts(negative_b, b);
            prop_assume!(b != Int::from(0));
            let quotient = a.checked_div(&b).unwrap();
            let remainder = a.checked_rem(&b).unwrap();
            prop_assert_eq!(&(&(&quotient * &b) + &remainder), &a);
            let (dividend, divisor) = (a.parts(), b.parts());
            let (quotient, remainder) = (quotient.parts(), remainder.parts());
            prop_assert_eq!(cmp_mag(&remainder.limbs, &divisor.limbs), Ordering::Less);
            // Zero is never negative; otherwise the remainder takes the
            // dividend's sign and the quotient the operands' combined sign.
            if !remainder.limbs.is_empty() {
                prop_assert_eq!(remainder.negative, dividend.negative);
            }
            if !quotient.limbs.is_empty() {
                prop_assert_eq!(quotient.negative, dividend.negative != divisor.negative);
            }
        }

        /// Parsing is the inverse of display for any digit string.
        #[test]
        fn digits_round_trip(negative in any::<bool>(), digits in "[1-9][0-9]{0,60}") {
            let text = if negative { format!("-{digits}") } else { digits };
            prop_assert_eq!(int(&text).to_string(), text);
        }
    }
}
