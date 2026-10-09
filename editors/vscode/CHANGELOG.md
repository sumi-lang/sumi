# Changelog

## Unreleased

- Highlight every occurrence of the name under the cursor, its declaration and assignments as
  writes and its reads as reads.
- Continue a comment line on Enter with `//`, unless the comment is empty or follows code.
- Add **Sumi: Restart Language Server**, and restart the server when `sumi.server.path` changes
  instead of asking for a window reload.

## 0.4.0

- Complete the names in scope: the locals a position can read with their types, every function
  with its signature as a call snippet, the keywords the grammar admits there, and the types after
  `:` and `->`. Completion keeps working in a function whose block is not closed yet.
- Go to the definition of a local or a function, find its references, and rename it across them.
  A rename is refused when the new name is not a name, is a function's name, or is a local already
  in scope at one of the occurrences.
- Hover a name for its declaration and type; a function also shows the values the analysis proved
  its call sites pass and it returns.
- Show the inferred type after a `let` without one, with an edit that writes it in, and the
  parameter name before a call argument that is not already that name.
- Keep the statement after a `for` header that still lacks its `..` intact while it is typed.

## 0.3.0

- Report warnings beside errors: a name nothing reads, with a quick fix that prefixes it with `_`;
  a condition or loop range that always decides the same way; code after a statement that never
  completes; and a function nothing calls. A file with only warnings still counts as valid.
- Check and highlight bounded `for` loops.
- Analyze and format files faster.

## 0.2.0

- Bundle the matching `sumi-lsp` with platform-specific extension packages for Linux, macOS, and
  Windows.
- Keep a serverless package and `sumi.server.path` override for unsupported platforms and custom
  builds.

## 0.1.0

- Add syntax and semantic diagnostics for saved and untitled Sumi files through `sumi-lsp`.
- Add compiler quick fixes, full-document formatting, and document symbols.

## 0.0.4

- Recognize `.su` files instead of `.sumi` files.
- Show a Sumi icon beside `.su` files in light and dark editor themes.

## 0.0.3

- Match syntax highlighting and editor behavior to the compiler's current literals, escapes, ASCII
  identifiers, keywords, punctuation, operators, and mutable assignments.
- Synchronize the highlighted keyword and punctuation vocabulary with the compiler's token
  declaration.
- Make the published VSIX checksum directly verifiable beside the downloaded package.

## 0.0.2

- Add the Sumi icon to the Marketplace listing.
- Remove snippets while the language syntax is still evolving.

## 0.0.1

- Recognize `.sumi` files.
- Highlight the initial Sumi syntax, strings, interpolation, and comments.
- Configure comments, brackets, indentation, and auto-closing pairs.
- Add snippets for common declarations and expressions.
