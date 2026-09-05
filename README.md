<h1 align="center"><a href="https://sumi-lang.org">Sumi</a></h1>

<p align="center">
  <strong>More work for the compiler.</strong><br>
  Simpler, more explicit code for everyone else.
</p>

> [!CAUTION]
> **Here be dragons.** Sumi is in early, experimental development. There is no
> usable compiler or stable language yet, and everything described here is
> subject to change. Do not use Sumi for production work.

Sumi is a general-purpose, statically typed, compiled systems language. It aims
for the same broad territory as Rust, Zig, C++, and Ada: predictable
performance, low-level control, memory safety, and suitability for
performance-critical applications.

The central idea is simple: move complexity into the compiler rather than into
the programmer's code. Sumi is being designed from the ground up around:

- whole-program reasoning;
- aggressive compile-time evaluation;
- static verification; and
- precise knowledge of resource behavior.

## CLI

Run syntax diagnostics on one UTF-8 source file:

```sh
cargo run -p sumi-cli -- diagnose path/to/file.sumi
```

The `sumi` binary prints plain diagnostics to stderr as
`path:line:column: severity[group/code]: message`, with one-based lines and
UTF-8 byte columns. File-level errors omit the line and column. Invalid
invocations print plain usage text instead of a coded diagnostic.
Clean input produces no output. Exit status is 0 for no
errors, 1 for source errors, and 2 for usage or input errors. The command
does not modify files or perform name resolution or type checking.
Use `--help` for usage.

## License

Sumi is available under the [Universal Permissive License, Version 1.0](LICENSE).
