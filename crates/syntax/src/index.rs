//! Two index newtypes for the parser: [`SigIdx`] and [`NodeIdx`]. Both project into the lexer's raw
//! token index, [`RawIdx`](sumi_lexer::RawIdx).

sumi_text::index! {
    /// A significant token's position in a [`ParserInput`](crate::ParserInput), trivia stripped.
    SigIdx
}

sumi_text::index! {
    /// A node's position in a [`SyntaxTree`](crate::SyntaxTree).
    NodeIdx
}
