//! The token vocabulary: every kind the lexer assigns, declared once with
//! its shape, its fixed text or how it reads in a diagnostic, and the
//! tables the lexer classifies by, derived from that declaration.

/// Declares [`SyntaxKind`]: one kind per line, in the order `ALL` lists,
/// as `Name: shape literal`. The shapes `trivia`, `ident`, `literal`, and
/// `error` carry how the kind reads after "expected" in a diagnostic;
/// `keyword` carries the reserved word and `punct` the character, and
/// both read as that text in backticks. Each table is one pass over the
/// declaration, so nothing here can disagree with it.
macro_rules! tokens {
    (@keyword $text:ident, keyword $word:literal $name:ident) => {
        if $text == $word {
            return Some(Self::$name);
        }
    };
    (@keyword $text:ident, $shape:ident $lit:literal $name:ident) => {};
    (@punct $char:ident, punct $c:literal $name:ident) => {
        if $char == $c {
            return Some(Self::$name);
        }
    };
    (@punct $char:ident, $shape:ident $lit:literal $name:ident) => {};
    (@text $kind:ident, keyword $word:literal $name:ident) => {
        if $kind == Self::$name {
            return Some($word);
        }
    };
    (@text $kind:ident, punct $c:literal $name:ident) => {
        if $kind == Self::$name {
            return Some(concat!($c));
        }
    };
    (@text $kind:ident, $shape:ident $lit:literal $name:ident) => {};
    (@describe keyword $lit:literal) => {
        concat!("`", $lit, "`")
    };
    (@describe punct $lit:literal) => {
        concat!("`", $lit, "`")
    };
    (@describe $shape:ident $lit:literal) => {
        $lit
    };
    (@trivia $kind:ident, trivia $lit:literal $name:ident) => {
        if $kind == Self::$name {
            return true;
        }
    };
    (@trivia $kind:ident, $shape:ident $lit:literal $name:ident) => {};
    ($($(#[$doc:meta])* $name:ident: $shape:ident $lit:literal,)*) => {
        /// The kind of a token: trivia (`is_trivia`), a kind with fixed text
        /// (`text`), or one whose text varies: `Ident`, the literals, and
        /// `Error`.
        ///
        /// Every kind occupies a source range: there is deliberately no EOF
        /// sentinel (end of input is the end of the token buffer, surfaced as
        /// `Option` by lookahead APIs), and compound operators are not kinds:
        /// the parser glues them from adjacent punctuation.
        #[repr(u8)]
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
        pub enum SyntaxKind {
            $($(#[$doc])* $name,)*
        }

        impl SyntaxKind {
            /// Every kind, in declaration order.
            pub const ALL: &[Self] = &[$(Self::$name,)*];

            /// The keyword kind for `text`, if it is a reserved word.
            pub fn from_keyword(text: &str) -> Option<Self> {
                $(tokens!(@keyword text, $shape $lit $name);)*
                None
            }

            /// The kind for a punctuation character, if it has a role in the
            /// language. Punctuation without one has no kind and lexes as an
            /// error token.
            #[inline(always)]
            pub fn from_punct(byte: u8) -> Option<Self> {
                let char = byte as char;
                $(tokens!(@punct char, $shape $lit $name);)*
                None
            }

            /// The fixed text of a keyword or punctuation kind; `None` for
            /// kinds whose text varies.
            pub fn text(self) -> Option<&'static str> {
                $(tokens!(@text self, $shape $lit $name);)*
                None
            }

            /// Whether the kind is trivia — whitespace, line breaks, and
            /// comments — which the grammar never sees.
            pub fn is_trivia(self) -> bool {
                $(tokens!(@trivia self, $shape $lit $name);)*
                false
            }

            /// How the kind reads as the object of "expected" in a diagnostic.
            pub fn describe(self) -> &'static str {
                match self {
                    $(Self::$name => tokens!(@describe $shape $lit),)*
                }
            }
        }
    };
}

tokens! {
    /// Horizontal whitespace.
    Whitespace: trivia "whitespace",
    /// One line break.
    Newline: trivia "a line break",
    LineComment: trivia "a line comment",

    /// An identifier that is not a keyword: an ASCII letter or `_`, then
    /// ASCII letters, digits, and `_`. Any other character has no meaning in
    /// the language.
    Ident: ident "a name",
    /// The identifier `_` on its own, reserved for discards.
    Underscore: keyword "_",

    // Reserved keywords. The v0 set covers functions, bindings, branching,
    // and boolean literals only.
    ElseKw: keyword "else",
    FalseKw: keyword "false",
    /// A function item, or a closure where an expression is expected: the
    /// same signature and body forms, without a name. Outside every matched
    /// bracket pair a `fn` begins a top-level item, since no expression stands
    /// there.
    FnKw: keyword "fn",
    IfKw: keyword "if",
    LetKw: keyword "let",
    MutKw: keyword "mut",
    ReturnKw: keyword "return",
    TrueKw: keyword "true",

    /// A decimal integer literal: a run of digits. There are no separators,
    /// suffixes, or floats; trailing identifier characters attach as a suffix
    /// for the lexer to reject, so `1_000` and `1e5` are each one error.
    IntLiteral: literal "an integer literal",
    /// A string literal on one line: `"…"`, with escapes. A line break ends an
    /// unterminated one, so a stray quote costs its line and nothing after it.
    StringLiteral: literal "a string literal",

    // Punctuation, one kind per character. Punctuation without a role in the
    // language (`;`, `[`, `@`, …) has no kind and lexes to `Error`.
    LParen: punct '(',
    RParen: punct ')',
    LBrace: punct '{',
    RBrace: punct '}',
    Comma: punct ',',
    Colon: punct ':',
    Dot: punct '.',
    Eq: punct '=',
    /// The comparison, spaced on both sides like every binary operator. Glued
    /// to the identifier before it, `<` opens a list of type arguments, in
    /// types, declarations, and expressions alike, so there is no turbofish:
    /// `Vec<int>` and `parse<int>("3")` instantiate, `a < b` compares, and
    /// `a<b` is an error, an unspaced comparison until generics exist and an
    /// unclosed list after. That pair encloses no statements and suspends the
    /// newline rule for nothing, so it is confined to its statement. Nothing
    /// generic is built yet; the reading is decided so that the glued form
    /// never becomes valid as a comparison.
    Lt: punct '<',
    /// The comparison, or the closer of a list of type arguments, which takes
    /// one `>` at a time, so `>>` closes two. It continues a line as every
    /// binary operator does, which lets a list close on its own line.
    Gt: punct '>',
    Bang: punct '!',
    Plus: punct '+',
    Minus: punct '-',
    /// Multiplication, spaced on both sides. Glued to what follows, `*` is
    /// reserved for a prefix operator, so `a*b` and a line beginning `*b`
    /// stay errors until one exists.
    Star: punct '*',
    Slash: punct '/',
    Percent: punct '%',
    /// No role alone: `&&` is `and`. Glued to what follows, `&` is reserved
    /// for a prefix operator.
    Amp: punct '&',
    Pipe: punct '|',

    /// A token with no meaning in the language: unrecognized characters, a
    /// byte-order mark included, and punctuation without a role.
    Error: error "valid syntax",
}

#[cfg(test)]
mod tests {
    use super::SyntaxKind;

    /// A fixed text classifies back to its kind and reads as itself.
    #[test]
    fn fixed_texts_round_trip() {
        for &kind in SyntaxKind::ALL {
            let Some(text) = kind.text() else {
                continue;
            };
            let back = SyntaxKind::from_keyword(text)
                .or_else(|| SyntaxKind::from_punct(text.as_bytes()[0]));
            assert_eq!(back, Some(kind));
            assert_eq!(kind.describe(), format!("`{text}`"));
        }
        assert_eq!(SyntaxKind::from_keyword("_"), Some(SyntaxKind::Underscore));
        assert_eq!(SyntaxKind::from_punct(b';'), None);
        assert_eq!(SyntaxKind::Ident.describe(), "a name");
        assert!(SyntaxKind::LineComment.is_trivia() && !SyntaxKind::Ident.is_trivia());
    }
}
