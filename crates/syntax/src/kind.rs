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

    /// An identifier that is not a keyword.
    Ident,

    // Reserved keywords. The v0 set covers functions, bindings, branching,
    // and boolean literals only; the table is
    // [`from_keyword`](SyntaxKind::from_keyword).
    ElseKw,
    FalseKw,
    FnKw,
    IfKw,
    LetKw,
    MutKw,
    ReturnKw,
    TrueKw,

    /// A decimal integer literal.
    IntLiteral,
    /// A float literal: a fraction (`1.5`), an exponent (`1e3`), or both.
    FloatLiteral,
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

impl SyntaxKind {
    /// The keyword kind for `text`, if it is a reserved word.
    pub fn from_keyword(text: &str) -> Option<Self> {
        Some(match text {
            "else" => Self::ElseKw,
            "false" => Self::FalseKw,
            "fn" => Self::FnKw,
            "if" => Self::IfKw,
            "let" => Self::LetKw,
            "mut" => Self::MutKw,
            "return" => Self::ReturnKw,
            "true" => Self::TrueKw,
            _ => return None,
        })
    }
}
