# Sumi Language Core

You're in the core repository for Sumi, a novel statically typed general-purpose programming language.

## Git Style

- Use [Conventional Commits](https://www.conventionalcommits.org/en/v1.0.0/) with the following types: build, chore, ci, docs, feat, fix, perf, refactor, revert, style, test.
- Commits should be self-contained, directed, and easily reviewable.

## Crates

- Dependencies point one way: `sumi-text`, then `sumi-lexer`, `sumi-syntax`, and above them `sumi-format`, `sumi-diagnostics`, and `sumi-frontend`. `sumi-test` (generators and edits, nothing above the parser), `sumi-scorecard` (the recovery scorecard, above everything), and `xtask` (codegen, which depends on no workspace crate so it runs while they do not compile) are leaves that nothing ships.
- A crate's integration tests may use crates above it, which Cargo allows. A library's unit tests never import a crate above it: rust-analyzer's crate graph has no room for that cycle and drops the edge without a word, leaving those tests unresolved in the editor.

## Grammar

- `sumi.grammar` at the workspace root is the one declaration of the token and node vocabularies, the token classes, bracket pairs, and operators. To add or change syntax, edit it — never the generated files it lists — and run `cargo xtask codegen`; CI runs `cargo xtask codegen --check`.

## Tests

- `tests/corpus/` at the workspace root is the file-based corpus: each case is a directory holding `case.sumi` and, beside it, `expected.snap` recording the tree, the parser's evidence, the diagnostics, the fixed source, and the normalized source. The runner is `crates/frontend/tests/corpus.rs`. To add a case, write its `case.sumi` and run `UPDATE_EXPECT=1 cargo test -p sumi-frontend --test corpus`; review every snapshot change as part of the diff.
- Behavior that a snapshot cannot express — invariants, API contracts, properties — stays in the crates' own tests.

## Fuzzing

- `fuzz/` is a libFuzzer package, `sumi-fuzz`, driven by [cargo-fuzz](https://rust-fuzz.github.io/book/cargo-fuzz.html): a leaf above every crate that nothing ships, like `sumi-scorecard`. Its library restates the crates' property-test invariants over arbitrary input; each target under `fuzz_targets/` feeds one layer: `lex` the lexer, `parse` the whole frontend and normalizer, and `edit` the single-edit recovery properties, with the fuzzer's bytes choosing the edit and the source in place of the generators of `sumi-test`. A new invariant goes into the property test first and the fuzz library second; the two must agree. Proptest's pass-through RNG cannot stand in for the generators: it halves its bytes at every nested strategy, and the zeros it yields once they run out send rand's range sampling into an endless rejection loop.
- The crates are safe Rust, so run without a sanitizer, which is what keeps the stable toolchain enough: `cargo xtask fuzz-seed`, then `cargo fuzz run -s none parse -- -dict=fuzz/sumi.dict`. The seeds are the file-based cases; `edit` needs them, since mutation alone never assembles a program the parser accepts without evidence. `fuzz/corpus/` and `fuzz/artifacts/` are untracked, and `fuzz/sumi.dict` is generated from `sumi.grammar`.
- A finding lands in `fuzz/artifacts/<target>/`. Minimize it with `cargo fuzz tmin -s none <target> <artifact>`, then keep it as a corpus case under `tests/corpus/` with the fix, so the regression stays found without the fuzzer.

## Code Style

- Follow YAGNI: don't implement functions which aren't necessary (also helps keep diffs reviewable)
- Prefer making invariants unrepresentable vs. adding asserts or explicit documentation.
