# Sumi Language Core

You're in the core repository for Sumi, a novel statically typed general-purpose programming language.

## Git Style

- Use [Conventional Commits](https://www.conventionalcommits.org/en/v1.0.0/) with the following types: build, chore, ci, docs, feat, fix, perf, refactor, revert, style, test.
- Commits should be self-contained, directed, and easily reviewable.

## Grammar

- `sumi.grammar` at the workspace root is the one declaration of the token and node vocabularies, the token classes, bracket pairs, and operators. To add or change syntax, edit it — never the generated files it lists — and run `cargo xtask codegen`; CI runs `cargo xtask codegen --check`.

## Code Style

- Follow YAGNI: don't implement functions which aren't necessary (also helps keep diffs reviewable)
- Prefer making invariants unrepresentable vs. adding asserts or explicit documentation.
