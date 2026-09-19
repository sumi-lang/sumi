sumi_text::index! {
    /// The index of a token in a [`LexedFile`](crate::LexedFile): a position in
    /// the raw token buffer, trivia included.
    ///
    /// The parser's significant index and the tree's node index are other
    /// spaces with other types, so an index is never applied to the wrong
    /// buffer. Ranges of raw tokens are half-open, and the index one past the
    /// last token — [`LexedFile::end`](crate::LexedFile::end) — is where a range
    /// running to the end of the file stops.
    RawIdx
}
