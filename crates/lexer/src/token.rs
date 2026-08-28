use std::fmt;
use std::ops::BitOrAssign;

use jolt_text::TextSize;

/// A transient scanner result: one raw lexical atom.
///
/// Raw tokens never own source text and carry no absolute position; the
/// collector tracks offsets while accumulating a [`LexedFile`](crate::LexedFile).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct RawToken {
    pub(crate) kind: RawKind,
    /// Length in UTF-8 bytes. Always positive; EOF is iterator `None`.
    pub(crate) len: TextSize,
    pub(crate) flags: TokenFlags,
}

/// The shape of a raw lexical atom.
///
/// Raw kinds are context-free and language-version-independent: keywords are
/// [`Ident`](RawKind::Ident)s, compound operators are sequences of
/// single-character [`Punct`](RawKind::Punct)s, and malformed tokens keep
/// their intended kind, with details in [`TokenFlags`] and the file's error
/// list.
#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RawKind {
    /// U+FEFF at byte zero. Anywhere else it is [`Unknown`](RawKind::Unknown).
    Bom,

    /// A run of spaces and horizontal tabs.
    HorizontalSpace,
    /// One `\n`, `\r\n`, or lone `\r` (the latter flagged
    /// [`LONE_CR`](TokenFlags::LONE_CR)).
    Newline,

    /// `// ...` up to, not including, the end of the line.
    LineComment,
    /// `/* ... */`, nesting.
    BlockComment,

    /// An identifier or keyword; also plain `_`.
    Ident,

    /// An integer or float literal of any base, including any suffix.
    Number,
    /// A `"..."` literal, possibly multi-line.
    String,
    /// An `r"..."` or `r#"..."#` literal.
    RawString,
    /// A `'...'` literal, ended by the line if unterminated.
    Char,

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
    /// A string or character literal contains at least one `\` escape.
    pub const HAS_ESCAPE: Self = Self(1 << 1);
    /// An outer doc comment: `///` or `/**`.
    pub const DOC_OUTER: Self = Self(1 << 2);
    /// An inner doc comment: `//!` or `/*!`.
    pub const DOC_INNER: Self = Self(1 << 3);
    /// A lone `\r` not followed by `\n`.
    pub const LONE_CR: Self = Self(1 << 4);
    /// A number with a base prefix but no digits, like `0x`.
    pub const EMPTY_BASE_DIGITS: Self = Self(1 << 5);

    const NAMES: [(Self, &'static str); 6] = [
        (Self::UNTERMINATED, "UNTERMINATED"),
        (Self::HAS_ESCAPE, "HAS_ESCAPE"),
        (Self::DOC_OUTER, "DOC_OUTER"),
        (Self::DOC_INNER, "DOC_INNER"),
        (Self::LONE_CR, "LONE_CR"),
        (Self::EMPTY_BASE_DIGITS, "EMPTY_BASE_DIGITS"),
    ];

    pub const fn is_empty(self) -> bool {
        self.0 == 0
    }

    pub const fn contains(self, other: Self) -> bool {
        self.0 & other.0 == other.0
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
