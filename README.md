<h1 align="center"><a href="https://sumi-lang.org">Sumi</a></h1>

**More work for the compiler. Simpler, more explicit code for everyone else.**

> [!WARNING]
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

## License

Sumi is available under the [Universal Permissive License, Version 1.0](LICENSE).
