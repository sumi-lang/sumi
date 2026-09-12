# Sumi Language Core

You're in the core repository for Sumi, a novel statically typed general-purpose programming language.

## Git Style

- Use [Conventional Commits](https://www.conventionalcommits.org/en/v1.0.0/) with the following types: build, chore, ci, docs, feat, fix, perf, refactor, revert, style, test.
- Commits should be self-contained, directed, and easily reviewable.

## Crates

- Dependencies point one way: `sumi-text`, then `sumi-lexer`, `sumi-syntax`, and above them `sumi-format`, `sumi-diagnostics`, and `sumi-frontend`. `sumi-hir` sits above the immutable frontend and owns semantic checking. `sumi-test` (generators and edits, nothing above the parser), `sumi-scorecard` (the recovery scorecard, above everything), and `xtask` (codegen, which depends on no workspace crate so it runs while they do not compile) are leaves that nothing ships.
- A crate's integration tests may use crates above it, which Cargo allows. A library's unit tests never import a crate above it: rust-analyzer's crate graph has no room for that cycle and drops the edge without a word, leaving those tests unresolved in the editor.

## Formatting

- `sumi fmt` is `sumi-format`'s `format`: one separator per gap between significant tokens, groups fitted to a width, and the parser's own newline rule deciding where a break is legal. Its contract is `rep`: the formatted text has the layout-free content of the source — the same tokens, tree, comments, and retained blank lines — or the disagreeing item is left as written, or the whole is a `Defect`. Gaps the parser recovered around are frozen. Add a layout rule per node kind in `plan.rs`; the corpus's `== formatted ==` sections and the `fmt` properties are the witnesses.

## Grammar

- `sumi.grammar` at the workspace root is the one declaration of the token and node vocabularies, the token classes, bracket pairs, and operators. To add or change syntax, edit it — never the generated files it lists — and run `cargo xtask codegen`; CI runs `cargo xtask codegen --check`.

## Tests

- `tests/corpus/` at the workspace root is the shared file-based corpus. Every case directory holds `case.sumi` and `frontend.snap`, keeping the tree, parser evidence, frontend diagnostics, fixed source, and formatted source together. `crates/frontend/tests/corpus.rs` runs every case; generate or update snapshots with `UPDATE_FRONTEND=1 cargo test -p sumi-frontend --test corpus`.
- For semantic-focused cases and useful recovery witnesses, not every syntax fixture, add a `stages` file containing exactly `hir` to select an additional `hir.snap`. Snapshot presence does not select a stage. Generate or update HIR snapshots with `UPDATE_HIR=1 cargo test -p sumi-hir --test corpus`. Keep huge stress inputs out of golden snapshots. Review every generated diff.
- Behavior that a snapshot cannot express — invariants, API contracts, properties — stays in the crates' own tests.
- `crates/syntax/tests/coverage.rs` checks that the corpus and `sumi-test`'s program generator each reach every node kind and every child `sumi.grammar` allows, through the witnesses codegen writes to `crates/test/src/generated/mod.rs`. A grammar change therefore needs a corpus case and generator support before CI passes; the failure names what is missing.

## Fuzzing

- `fuzz/` is a libFuzzer package, `sumi-fuzz`, driven by [cargo-fuzz](https://rust-fuzz.github.io/book/cargo-fuzz.html): a leaf above every crate that nothing ships, like `sumi-scorecard`. Its library restates the crates' property-test invariants over arbitrary input; each target under `fuzz_targets/` feeds one layer: `lex` the lexer, `parse` the whole frontend and formatter, `check` semantic acceptance and complete-body invariants, and `edit` the single-edit recovery properties, with the fuzzer's bytes choosing the edit and the source in place of the generators of `sumi-test`. A new invariant goes into the property test first and the fuzz library second; the two must agree. Proptest's pass-through RNG cannot stand in for the generators: it halves its bytes at every nested strategy, and the zeros it yields once they run out send rand's range sampling into an endless rejection loop.
- The crates are safe Rust, so run without a sanitizer, which is what keeps the stable toolchain enough: `cargo xtask fuzz-seed`, then `cargo fuzz run -s none parse -- -dict=fuzz/sumi.dict`. The seeds are the file-based cases; `edit` needs them, since mutation alone never assembles a program the parser accepts without evidence. `fuzz/corpus/` and `fuzz/artifacts/` are untracked, and `fuzz/sumi.dict` is generated from `sumi.grammar`.
- A finding lands in `fuzz/artifacts/<target>/`. Minimize it with `cargo fuzz tmin -s none <target> <artifact>`, then keep it as a corpus case under `tests/corpus/` with the fix, so the regression stays found without the fuzzer.

## Code Style

- Follow YAGNI: don't implement functions which aren't necessary (also helps keep diffs reviewable)
- Prefer making invariants unrepresentable vs. adding asserts or explicit documentation.
