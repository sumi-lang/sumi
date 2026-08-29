/// The language-level kind of a token.
///
/// Kept separate from the raw lexer's shape-only [`RawKind`](sumi_lexer::RawKind)
/// below it and from the tree's [`NodeKind`] above it: nodes cover ranges of
/// tokens rather than sitting among them, so the two vocabularies never share a
/// slot. Every kind occupies a source range: there is deliberately no EOF
/// sentinel (end of input is the end of the token buffer, surfaced as `Option`
/// by lookahead APIs), and compound-operator kinds appear only once the parser
/// glues adjacent punctuation.
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

    /// The kind for a punctuation character, if it has a role in the
    /// language. Punctuation without one (`;`, `[`, `@`, …) has no kind and
    /// cooks to [`Error`](Self::Error).
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

/// The kind of a syntax tree node.
///
/// A node is structure only, so this vocabulary is disjoint from
/// [`SyntaxKind`]: a tree slot never holds a token kind, and a
/// token buffer slot never holds a node kind.
#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum NodeKind {
    SourceFile,
    FnItem,
    ParamList,
    Param,
    Block,
    LetStmt,
    DiscardStmt,
    ReturnStmt,
    NameExpr,
    LiteralExpr,
    PrefixExpr,
    BinaryExpr,
    ParenExpr,
    CallExpr,
    IfExpr,
    /// Covers tokens the parser could not parse.
    Error,
}
