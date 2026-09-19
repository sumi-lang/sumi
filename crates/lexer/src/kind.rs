//! The token vocabulary: `SyntaxKind` and its tables, all derived from the one `tokens!`
//! declaration so none can disagree with it.

/// One kind per line as `Name: shape literal`; the literal is the source text of a `keyword` or
/// `punct`, and how any other shape reads after "expected".
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
        /// Every kind spans source text: there is no EOF kind, and no compound operator kind, since
        /// the parser glues adjacent punctuation.
        #[repr(u8)]
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
        pub enum SyntaxKind {
            $($(#[$doc])* $name,)*
        }

        impl SyntaxKind {
            pub const ALL: &[Self] = &[$(Self::$name,)*];

            pub fn from_keyword(text: &str) -> Option<Self> {
                $(tokens!(@keyword text, $shape $lit $name);)*
                None
            }

            #[inline(always)]
            pub fn from_punct(byte: u8) -> Option<Self> {
                let char = byte as char;
                $(tokens!(@punct char, $shape $lit $name);)*
                None
            }

            pub fn text(self) -> Option<&'static str> {
                $(tokens!(@text self, $shape $lit $name);)*
                None
            }

            pub fn is_trivia(self) -> bool {
                $(tokens!(@trivia self, $shape $lit $name);)*
                false
            }

            /// The kind as it reads after "expected" in a diagnostic.
            pub fn describe(self) -> &'static str {
                match self {
                    $(Self::$name => tokens!(@describe $shape $lit),)*
                }
            }
        }
    };
}

tokens! {
    Whitespace: trivia "whitespace",
    Newline: trivia "a line break",
    LineComment: trivia "a line comment",

    Ident: ident "a name",
    Underscore: keyword "_",

    ElseKw: keyword "else",
    FalseKw: keyword "false",
    FnKw: keyword "fn",
    IfKw: keyword "if",
    LetKw: keyword "let",
    MutKw: keyword "mut",
    ReturnKw: keyword "return",
    TrueKw: keyword "true",

    IntLiteral: literal "an integer literal",
    StringLiteral: literal "a string literal",

    LParen: punct '(',
    RParen: punct ')',
    LBrace: punct '{',
    RBrace: punct '}',
    Comma: punct ',',
    Colon: punct ':',
    Dot: punct '.',
    Eq: punct '=',
    Lt: punct '<',
    Gt: punct '>',
    Bang: punct '!',
    Plus: punct '+',
    Minus: punct '-',
    Star: punct '*',
    Slash: punct '/',
    Percent: punct '%',
    Amp: punct '&',
    Pipe: punct '|',

    Error: error "valid syntax",
}

#[cfg(test)]
mod tests {
    use super::SyntaxKind;

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
