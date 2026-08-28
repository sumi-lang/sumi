use jolt_lexer::RawKind;

/// The language-level kind of a token and, later, of a CST node.
///
/// One flat vocabulary shared by cooked tokens and syntax tree nodes, kept
/// separate from the raw lexer's shape-only `RawKind`. Every kind occupies a
/// source range: there is deliberately no EOF sentinel (end of input is the
/// end of the token buffer, surfaced as `Option` by lookahead APIs), and
/// compound-operator kinds appear only once the parser glues adjacent
/// punctuation.
#[repr(u16)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SyntaxKind {
    /// Horizontal whitespace, or the byte-order mark.
    Whitespace,
    /// One line break.
    Newline,

    LineComment,
    BlockComment,

    /// An identifier. Keyword classification arrives with the keyword table.
    Ident,

    /// An integer or float literal; the int/float split arrives with number
    /// validation.
    NumberLiteral,
    StringLiteral,
    RawStringLiteral,
    CharLiteral,

    /// A single ASCII punctuation character. Splits into per-character kinds
    /// when the parser's glue table needs them.
    Punct,

    /// A token with no meaning in the language: unrecognized characters and
    /// misplaced byte-order marks.
    Error,
}

/// The context-free base classification of a raw token.
///
/// This is what a raw kind means before any text-sensitive refinement;
/// [`cook`](crate::cook) applies it today and will layer keyword
/// classification and literal validation on top of it.
impl From<RawKind> for SyntaxKind {
    fn from(kind: RawKind) -> Self {
        match kind {
            // The BOM is ignorable trivia to every downstream phase; its
            // identity stays recoverable through the raw kind.
            RawKind::Bom | RawKind::HorizontalSpace => Self::Whitespace,
            RawKind::Newline => Self::Newline,
            RawKind::LineComment => Self::LineComment,
            RawKind::BlockComment => Self::BlockComment,
            RawKind::Ident => Self::Ident,
            RawKind::Number => Self::NumberLiteral,
            RawKind::String => Self::StringLiteral,
            RawKind::RawString => Self::RawStringLiteral,
            RawKind::Char => Self::CharLiteral,
            RawKind::Punct => Self::Punct,
            RawKind::Unknown => Self::Error,
        }
    }
}
