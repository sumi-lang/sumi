# Sumi Language

Language support for the experimental [Sumi programming language](https://sumi-lang.org).

The extension provides:

- `.su` file recognition;
- syntax highlighting for the compiler's current keywords, declarations, operators, literals, and
  comments;
- comment, bracket, indentation, auto-closing, and comment-continuation configuration;
- syntax and semantic diagnostics, quick fixes, formatting, document symbols, completion of the
  names, keywords, and types in scope, go to definition, find references, rename, hover, inlay
  hints, and highlighting of a name's occurrences through `sumi-lsp`.

The extension includes `sumi-lsp` on supported platforms. Set `sumi.server.path` to use a custom
server or to provide one on another platform; the server restarts when the setting changes, and
**Sumi: Restart Language Server** restarts it at any time.

## License

Sumi is available under the [Universal Permissive License, Version 1.0](LICENSE).
