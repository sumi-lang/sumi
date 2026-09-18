use std::fmt;
use std::ops::{BitOr, BitOrAssign};

/// The shape of a lexical atom, stored beside its [`SyntaxKind`].
///
/// Raw kinds are context-free: keywords are [`Ident`](RawKind::Ident)s,
/// compound operators are sequences of single-character
/// [`Punct`](RawKind::Punct)s, and malformed tokens keep their intended
/// kind, with details in [`TokenFlags`] and the file's error list.
#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RawKind {
    /// A run of spaces and horizontal tabs.
    HorizontalSpace,
    /// One `\n`, `\r\n`, or lone `\r`.
    Newline,

    /// `// ...` up to, not including, the end of the line.
    LineComment,

    /// An identifier or keyword; also plain `_`.
    Ident,

    /// A decimal integer literal, including any suffix.
    Number,
    /// A `"..."` literal, ended by the line if unterminated.
    String,

    /// A single ASCII punctuation character.
    Punct,

    /// Anything not recognized above.
    Unknown,
}

/// Properties discovered while scanning a token.
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash)]
pub struct TokenFlags(u16);

impl TokenFlags {
    pub const EMPTY: Self = Self(0);
    /// The closing delimiter was never found.
    pub const UNTERMINATED: Self = Self(1 << 0);
    /// The literal breaks a rule the file's errors state: a suffix or a
    /// leading zero.
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
