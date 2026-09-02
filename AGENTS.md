# Sumi Language Core

You're in the core repository for Sumi, a novel statically typed general-purpose programming language.

## Git Style

- Use [Conventional Commits](https://www.conventionalcommits.org/en/v1.0.0/) with the following types: build, chore, ci, docs, feat, fix, perf, refactor, revert, style, test.
- Commits should be self-contained, directed, and easily reviewable.

## Crates

- Dependencies point one way: `sumi-text`, then `sumi-lexer`, `sumi-syntax`, and above them `sumi-format`, `sumi-diagnostics`, and `sumi-frontend`. `sumi-test` (generators and edits, nothing above the parser) and `xtask` (codegen and the recovery scorecard) are leaves that nothing ships.
- A crate's integration tests may use crates above it, which Cargo allows. A library's unit tests never import a crate above it: rust-analyzer's crate graph has no room for that cycle and drops the edge without a word, leaving those tests unresolved in the editor.

## Grammar

- `sumi.grammar` at the workspace root is the one declaration of the token and node vocabularies, the token classes, bracket pairs, and operators. To add or change syntax, edit it — never the generated files it lists — and run `cargo xtask codegen`; CI runs `cargo xtask codegen --check`.

## Tests

- `tests/corpus/` at the workspace root is the file-based corpus: each case is a directory holding `case.sumi` and, beside it, `expected.snap` recording the tree, the parser's evidence, the diagnostics, the fixed source, and the normalized source. The runner is `crates/frontend/tests/corpus.rs`. To add a case, write its `case.sumi` and run `UPDATE_EXPECT=1 cargo test -p sumi-frontend --test corpus`; review every snapshot change as part of the diff.
- Behavior that a snapshot cannot express — invariants, API contracts, properties — stays in the crates' own tests.

## Code Style

- Follow YAGNI: don't implement functions which aren't necessary (also helps keep diffs reviewable)
- Prefer making invariants unrepresentable vs. adding asserts or explicit documentation.
