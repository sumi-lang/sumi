use jolt_lexer::LexedFile;

use crate::kind::SyntaxKind;

/// Cook `lexed` into language-level token kinds.
///
/// Cooking is total and strictly 1:1: token `index` in the result classifies
/// token `index` of `lexed`, so ranges, text, and flags stay queryable
/// through the [`LexedFile`].
pub fn cook(lexed: &LexedFile) -> CookedFile {
    let kinds = (0..lexed.len())
        .map(|index| SyntaxKind::from(lexed.kind(index)))
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
