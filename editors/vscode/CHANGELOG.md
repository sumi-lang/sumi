# Changelog

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
