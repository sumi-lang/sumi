//! The parser's index spaces, kept apart by type: a significant position in
//! a [`ParserInput`](crate::ParserInput), and a node in a
//! [`SyntaxTree`](crate::SyntaxTree). The lexer's raw token index is the
//! third, [`RawIdx`](sumi_lexer::RawIdx), which both of these project into.

sumi_text::index! {
    /// The index of a significant token in a [`ParserInput`](crate::ParserInput):
    /// the parser's cursor space, trivia stripped. Every significant index
    /// maps to the raw index of its token; the reverse needs a search.
    SigIdx
}

sumi_text::index! {
    /// The index of a node in a [`SyntaxTree`](crate::SyntaxTree): its
    /// position in preorder, so the root is 0 and a node's subtree is the
    /// run of indices from its own.
    NodeIdx
}
