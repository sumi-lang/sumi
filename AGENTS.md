# Sumi Language Core

You're in the core repository for Sumi, a novel statically typed general-purpose programming language.

## Git Style

- Use [Conventional Commits](https://www.conventionalcommits.org/en/v1.0.0/) with the following types: build, chore, ci, docs, feat, fix, perf, refactor, revert, style, test.
- Commits should be self-contained, directed, and easily reviewable.

## Crates

- Dependencies point one way. Each line names what a crate owns and what it sits on directly; what those sit on follows.
- `sumi-text`: offsets, ranges, edits, and the line index. Depends on nothing.
- `sumi-lexer`: the total, lossless lexer and the token vocabulary. On `sumi-text`.
- `sumi-syntax`: the parser, the flat tree and its reprint, parse evidence, recovery, and the node vocabulary with its typed views. On `sumi-lexer`.
- `sumi-format`: `format` and its contract `rep`. On `sumi-syntax`.
- `sumi-frontend`: the diagnostic type every later phase reports with, and `parse_source`, which owns the source and lowers the lexer's and parser's evidence into diagnostics. On `sumi-syntax`.
- `sumi-graph`: what a program means apart from whether it is valid: the scalar types, `Int`, the `Graph`, the may-domain, and the concrete `Machine`. On `sumi-text` only; nothing here depends on the checker.
- `sumi-hir`: semantic checking: `analyze` builds the graph and decides what is wrong with it, and `Program`, the proof that a file is valid, runs it. On `sumi-frontend` and `sumi-graph`.
- `sumi-cli`: the `sumi` driver. On `sumi-frontend` and `sumi-hir` to check and run, and on `sumi-lexer`, `sumi-syntax`, and `sumi-format` to format, which reads no diagnostic.
- `sumi-test`: the program generator, edits, layout perturbation, the coverage account, the invariant checks the property tests and the fuzz targets share, and the fuzz seeder. On every crate but `sumi-graph`, whose vocabulary it takes through `sumi-hir`; nothing ships it.
- `sumi-scorecard`: the recovery scorecard, a leaf on `sumi-test`; nothing ships it.
- `sumi-fuzz` (`fuzz/`): the fuzz targets, a leaf above every crate; nothing ships it.
- A crate's integration tests may use crates above it, which Cargo allows. A library's unit tests never import a crate above it: rust-analyzer's crate graph has no room for that cycle and drops the edge without a word, leaving those tests unresolved in the editor.

## Formatting

- `sumi fmt` is `sumi-format`'s `format`: one separator per gap between significant tokens, groups fitted to a width, and the parser's own newline rule deciding where a break is legal. Its contract is `rep`: the formatted text has the layout-free content of the source — the same tokens, tree, comments, and retained blank lines — or the disagreeing item is left as written, or the whole is a `Defect`. Gaps the parser recovered around are frozen. Add a layout rule per node kind in `plan.rs`; the corpus's `== formatted ==` sections and the `fmt` properties are the witnesses.

## Grammar and diagnostics

- The token vocabulary is one `tokens!` declaration in `crates/lexer/src/kind.rs`, which derives the keyword and punctuation tables, texts, and descriptions. The node vocabulary and the typed views are one `grammar!` declaration in `crates/syntax/src/ast.rs`: a struct per node kind listing the children the parser records, whose slots are their declaration order, and an enum per category. The token classes, bracket pairs, and operator tables are plain functions in `crates/syntax/src/grammar.rs`. A token a rule holds itself, and each member of an alternation a field admits, is listed in `RULES` in `crates/test/src/coverage.rs`: with the children the views declare and `BinaryOp::ALL`, that is what the coverage check reads.
- Diagnostic codes are one `codes!` declaration per group, in `crates/frontend/src/codes.rs` (`syntax`) and `crates/hir/src/codes.rs` (`semantic`), each code documented where it is declared; the macro derives the constants and the group's `ALL`, so no code goes unlisted. To add a code, declare it there, emit it, and add a corpus case that shows it: `crates/hir/tests/codes.rs` fails on a code no snapshot reports. A code is never renamed or reused for something else.

## Tests

- `tests/corpus/` at the workspace root is the shared file-based corpus. Every case directory holds `case.sumi` and `frontend.snap`, keeping the tree, parser evidence, frontend diagnostics, fixed source, and formatted source together; a case that selects `hir` leaves the tree out, since `hir.snap` anchors the graph the checker built by range, not every parse-tree node, so a case whose parse is the point does not select `hir`. `syntax/a-whole-program` is the tree golden of a large accepted file. `crates/frontend/tests/corpus.rs` runs every case through `sumi_test::corpus`, the runner every stage shares, which also lists the cases for any test that reads them; generate or update snapshots with `UPDATE_FRONTEND=1 cargo test -p sumi-frontend --test corpus`.
- For semantic-focused cases and useful recovery witnesses, not every syntax fixture, add a `stages` file listing `hir` to select an additional `hir.snap`, and `eval` (one name per line) to select an `eval.snap` that runs every parameterless function of an accepted case to its value, with the machine's step count and deepest call nesting beside the depth the analysis proved. Snapshot presence does not select a stage. Generate or update them with `UPDATE_HIR=1 cargo test -p sumi-hir --test corpus` and `UPDATE_EVAL=1 cargo test -p sumi-hir --test corpus`. Keep huge stress inputs out of golden snapshots. Review every generated diff.
- Behavior that a snapshot cannot express — invariants, API contracts, properties — stays in the crates' own tests. Every invariant is stated once, in `sumi-test`'s `check` module: a crate's property test samples it over generated sources, and the fuzz target of the same layer over arbitrary bytes, so a new invariant goes there and both find it. `crates/hir/tests/machine.rs` is the analysis held to the machine: generated programs the checker should accept, each run by `check::run` inside the parameter sets it proved and checked against its claims. A change to what the checker accepts or proves must keep that harness green.
- `crates/syntax/tests/coverage.rs` checks that the corpus and `sumi-test`'s program generator each reach every node kind and every child the grammar allows: the children every view declares, and `RULES` in `crates/test/src/coverage.rs`. A grammar change therefore needs a corpus case and generator support before CI passes; the failure names what is missing.

## Fuzzing

- `fuzz/` is a libFuzzer package, `sumi-fuzz`, driven by [cargo-fuzz](https://rust-fuzz.github.io/book/cargo-fuzz.html): a leaf above every crate that nothing ships, like `sumi-scorecard`. Each target under `fuzz_targets/` feeds one layer's checks from `sumi-test` arbitrary input, the same checks that layer's property tests sample: `lex` the lexer, `parse` the whole frontend and formatter, `check` semantic acceptance and the graph's shape, `run` every accepted file on the machine inside the parameter sets the analysis proved, and `edit` single-edit recovery, with the fuzzer's bytes choosing the edit and the source in place of the generators of `sumi-test`. Proptest's pass-through RNG cannot stand in for the generators: it halves its bytes at every nested strategy, and the zeros it yields once they run out send rand's range sampling into an endless rejection loop.
- The crates are safe Rust, so run without a sanitizer, which is what keeps the stable toolchain enough: `cargo run -p sumi-test --bin fuzz-seed`, then `cargo fuzz run -s none parse -- -dict=fuzz/sumi.dict`. The seeds are the file-based cases; `edit` needs them, since mutation alone never assembles a program the parser accepts without evidence; `edit_seeds` in `sumi-test` writes them and `edit_input` beside it reads them, so the header is stated once. `fuzz/corpus/` and `fuzz/artifacts/` are untracked, and `fuzz/sumi.dict` lists every fixed token text; keep it with the `tokens!` declaration.
- A finding lands in `fuzz/artifacts/<target>/`. Minimize it with `cargo fuzz tmin -s none <target> <artifact>`, then keep it as a corpus case under `tests/corpus/` with the fix, so the regression stays found without the fuzzer.

## Code Style

- Follow YAGNI: don't implement functions which aren't necessary (also helps keep diffs reviewable)
- Prefer making invariants unrepresentable vs. adding asserts or explicit documentation.
