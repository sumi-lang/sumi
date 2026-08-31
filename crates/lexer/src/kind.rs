/// The language-level kind of a token.
///
/// The lexer assigns these while a token's bytes are cache-hot; the
/// shape-only [`RawKind`](crate::RawKind) is stored beside them for phases
/// that reason about lexical shape. Every kind occupies a source range:
/// there is deliberately no EOF sentinel (end of input is the end of the
/// token buffer, surfaced as `Option` by lookahead APIs), and
/// compound-operator kinds appear only once the parser glues adjacent
/// punctuation.
#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SyntaxKind {
    /// Horizontal whitespace, or the byte-order mark.
    Whitespace,
    /// One line break.
    Newline,

    LineComment,

    /// An identifier that is not a keyword.
    Ident,
    /// The identifier `_` on its own, reserved for discards.
    Underscore,

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

    // Punctuation, one kind per character; the table is
    // [`from_punct`](SyntaxKind::from_punct). Compound operators (`==`,
    // `->`) exist only as joint pairs the parser glues.
    LParen,
    RParen,
    LBrace,
    RBrace,
    Comma,
    Colon,
    Dot,
    Eq,
    Lt,
    Gt,
    Bang,
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    Amp,
    Pipe,

    /// A token with no meaning in the language: unrecognized characters,
    /// misplaced byte-order marks, and punctuation without a role.
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

    /// The kind for a punctuation character, if it has a role in the
    /// language. Punctuation without one (`;`, `[`, `@`, …) has no kind and
    /// lexes to [`Error`](Self::Error).
    pub fn from_punct(byte: u8) -> Option<Self> {
        Some(match byte {
            b'(' => Self::LParen,
            b')' => Self::RParen,
            b'{' => Self::LBrace,
            b'}' => Self::RBrace,
            b',' => Self::Comma,
            b':' => Self::Colon,
            b'.' => Self::Dot,
            b'=' => Self::Eq,
            b'<' => Self::Lt,
            b'>' => Self::Gt,
            b'!' => Self::Bang,
            b'+' => Self::Plus,
            b'-' => Self::Minus,
            b'*' => Self::Star,
            b'/' => Self::Slash,
            b'%' => Self::Percent,
            b'&' => Self::Amp,
            b'|' => Self::Pipe,
            _ => return None,
        })
    }
}
