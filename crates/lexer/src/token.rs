use std::fmt;

/// A set flag has an entry in the file's `errors()` on the same token, so a consumer reports
/// nothing of its own.
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash)]
pub struct TokenFlags(u16);

impl TokenFlags {
    pub const EMPTY: Self = Self(0);
    pub const MALFORMED_NUMBER: Self = Self(1 << 0);

    const NAMES: [(Self, &'static str); 1] = [(Self::MALFORMED_NUMBER, "MALFORMED_NUMBER")];

    pub const fn is_empty(self) -> bool {
        self.0 == 0
    }

    pub const fn contains(self, other: Self) -> bool {
        self.0 & other.0 == other.0
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
        assert_eq!(
            format!("{:?}", TokenFlags::MALFORMED_NUMBER),
            "TokenFlags(MALFORMED_NUMBER)"
        );
    }
}
