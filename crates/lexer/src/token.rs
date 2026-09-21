use std::fmt;
use std::ops::{BitOr, BitOrAssign};

/// A set flag has an entry in the file's `errors()` on the same token, so a consumer reports
/// nothing of its own.
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash)]
pub struct TokenFlags(u16);

impl TokenFlags {
    pub const EMPTY: Self = Self(0);
    pub const UNTERMINATED: Self = Self(1 << 0);
    pub const MALFORMED_NUMBER: Self = Self(1 << 1);

    const NAMES: [(Self, &'static str); 2] = [
        (Self::UNTERMINATED, "UNTERMINATED"),
        (Self::MALFORMED_NUMBER, "MALFORMED_NUMBER"),
    ];

    pub const fn is_empty(self) -> bool {
        self.0 == 0
    }

    pub const fn contains(self, other: Self) -> bool {
        self.0 & other.0 == other.0
    }
}

impl BitOr for TokenFlags {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self {
        Self(self.0 | rhs.0)
    }
}

impl BitOrAssign for TokenFlags {
    fn bitor_assign(&mut self, rhs: Self) {
        self.0 |= rhs.0;
    }
}

impl fmt::Debug for TokenFlags {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "TokenFlags(")?;
        if self.is_empty() {
            write!(f, "EMPTY")?;
        } else {
            let mut separator = "";
            for (flag, name) in Self::NAMES {
                if self.contains(flag) {
                    write!(f, "{separator}{name}")?;
                    separator = " | ";
                }
            }
        }
        write!(f, ")")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn flags_debug_as_names() {
        assert_eq!(format!("{:?}", TokenFlags::EMPTY), "TokenFlags(EMPTY)");
        let combined = TokenFlags::UNTERMINATED | TokenFlags::MALFORMED_NUMBER;
        assert_eq!(
            format!("{combined:?}"),
            "TokenFlags(UNTERMINATED | MALFORMED_NUMBER)"
        );
        let mut assigned = TokenFlags::UNTERMINATED;
        assigned |= TokenFlags::MALFORMED_NUMBER;
        assert_eq!(assigned, combined);
    }
}
