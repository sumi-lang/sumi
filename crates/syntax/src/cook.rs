use jolt_lexer::{LexedFile, RawKind};

use crate::kind::SyntaxKind;

/// Cook `lexed` into language-level token kinds. `source` must be the string
/// it was lexed from.
///
/// Cooking is total and strictly 1:1: token `index` in the result classifies
/// token `index` of `lexed`, so ranges, text, and flags stay queryable
/// through the [`LexedFile`].
pub fn cook(source: &str, lexed: &LexedFile) -> CookedFile {
    let kinds = (0..lexed.len())
        .map(|index| match lexed.kind(index) {
            // The BOM is ignorable trivia to every downstream phase; its
            // identity stays recoverable through the raw kind.
            RawKind::Bom | RawKind::HorizontalSpace => SyntaxKind::Whitespace,
            RawKind::Newline => SyntaxKind::Newline,
            RawKind::LineComment => SyntaxKind::LineComment,
            RawKind::Ident => {
                SyntaxKind::from_keyword(lexed.text(source, index)).unwrap_or(SyntaxKind::Ident)
            }
            RawKind::Number => SyntaxKind::NumberLiteral,
            RawKind::String => SyntaxKind::StringLiteral,
            RawKind::RawString => SyntaxKind::RawStringLiteral,
            RawKind::Char => SyntaxKind::CharLiteral,
            RawKind::Punct => SyntaxKind::Punct,
            RawKind::Unknown => SyntaxKind::Error,
        })
        .collect();

    CookedFile { kinds }
}

/// The cooked token kinds for one source file, parallel to its [`LexedFile`].
#[derive(Clone, Debug)]
pub struct CookedFile {
    kinds: Box<[SyntaxKind]>,
}

impl CookedFile {
    /// The number of cooked tokens; always equal to the lexed token count.
    pub fn len(&self) -> usize {
        self.kinds.len()
    }

    pub fn is_empty(&self) -> bool {
        self.kinds.is_empty()
    }

    pub fn kind(&self, index: usize) -> SyntaxKind {
        self.kinds[index]
    }
}
