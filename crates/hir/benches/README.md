# Scalar solver benchmarks

The suite measures both the private solver and its integration into HIR. It
uses the same pinned CodSpeed/Criterion compatibility package as the frontend.
No benchmark-only API or instrumentation is added to production HIR.

## Run and reproduce

```sh
# Validate every fixture without collecting timing samples.
cargo bench -p sumi-hir --bench solver -- --test
cargo bench -p sumi-hir --bench analysis -- --test

# Run sequentially, not concurrently with builds, tests, or other benchmarks.
for run in run1 run2; do
  cargo bench -p sumi-hir --bench solver -- \
    --warm-up-time 0.2 --measurement-time 1 --sample-size 30 --save-baseline "$run"
  cargo bench -p sumi-hir --bench analysis -- \
    --warm-up-time 0.2 --measurement-time 1 --sample-size 30 --save-baseline "$run"
done
python3 crates/hir/benches/summarize.py target/criterion run1 run2 > timings.csv

# Separate executable: allocator instrumentation never affects wall-time runs.
cargo bench -p sumi-hir --bench allocations > allocations.csv
```

For more precise timing on a controlled machine, increase warm-up and measurement
times. The initial run used the short settings above and retains all 30 samples;
Criterion automatically extended the largest locals workload beyond one second.
The exporter reports arithmetic means and their 95% bootstrap confidence
intervals, not the regression slope printed by Criterion for some workloads.

CI runs both `solver` and `analysis` under CodSpeed simulation and memory modes,
alongside the existing frontend benchmarks. Allocation CSV output measures
successful `alloc`, `alloc_zeroed`, and `realloc` calls, counting the full requested
size on reallocation. **Requested bytes are allocation traffic, not live heap or
RSS.** The counter delegates unchanged to `System`; its unsafe allocator adapter
exists only in the standalone benchmark executable.

## Measurement boundaries

There are 96 timing cases and 96 allocation observations. Every workload runs at
128, 1,024, and 8,192 logical nodes/functions. Source/graph generation is fixed,
not randomized; validators check concrete results or expected unresolved/conflict
states, including signature and body availability for HIR workloads.

| Group | Included | Excluded |
|---|---|---|
| `solver/solve` | `Inference::solve`, including temporary adjacency/queue allocation and destruction | Graph construction, destruction of the resulting graph |
| `solver/replay-context` | Creation of a fresh context seeded from final imports | Original solving, checker obligation replay, destruction of the returned context |
| `solver/build-solve-replay` | Term/import/equality construction, solve, replay-context creation | Syntax, diagnostics, HIR construction, destruction of returned contexts |
| `hir/analyze` | Headers, resolution, draft bodies, solving, obligation replay, diagnostics, concrete publication | Parsing, `ParsedSource::clone` setup, destruction of returned `Analysis` |

The private benchmark compiles `src/infer.rs` directly, rather than a copy of the
algorithm. Its graph handle vector is included in construction costs. Criterion
batched measurements exclude setup and returned-output destruction. Temporary
objects destroyed *inside* the measured implementation remain included.

Graph workloads:

- Forward/reverse chains: one import per link, one concrete anchor; reverse
  logical variable allocation order without changing the equations.
- Grounded and unresolved cycles: distinguish actual evidence propagation from
  merely constructing the graph. An unresolved cycle must not default to unit.
- Conflict cycle: incompatible anchors on a cycle; conflict must reach all nodes.
- Fan-out/fan-in: same linear edge count, very different adjacency allocation and
  queue patterns.
- Equalities: balanced local unions without imports, exercising rank/compression.

HIR workloads include annotated/inferred chains in both declaration orders,
grounded/unresolved/conflicting cycles, and bodies with 16 sequential locals each.
The locals case has substantially more syntax/work per function; its function
throughput is not directly comparable with the one-call bodies.

## Initial measurements — September 8, 2026

Environment: Linux x86-64 orb, Intel Xeon at 2.60 GHz, two virtual CPUs on one
reported physical core, rustc 1.98.1, release profile, system allocator. Two full
current-suite runs were collected sequentially, with no concurrent benchmark or
build. Production implementation: the return-inference change in
[PR #98](https://github.com/sumi-lang/sumi/pull/98).

The tables show **ranges of the two run means**, not confidence intervals. Some
individual benchmark means drifted by 20–37% between runs, much more than their
within-run bootstrap intervals. Those intervals do not account for host load,
frequency changes, allocator history, or other between-run effects. Small
differences and declaration-order rankings should not be treated as established
performance improvements.

### Solver scaling and topology

At 8,192 logical nodes:

| Graph | Solve, µs | Build + solve + replay-context, µs | Solve allocation calls | Solve requested bytes |
|---|---:|---:|---:|---:|
| Forward chain | 305–327 | 509–560 | 8,193 | 655,336 |
| Reverse chain | 333–334 | 458–560 | 8,193 | 655,336 |
| Grounded cycle | 314–319 | 530–551 | 8,194 | 655,392 |
| Unresolved cycle | 264–268 | 431–476 | 8,193 | 655,360 |
| Conflict cycle | 265–334 | 467–526 | 8,194 | 655,392 |
| Fan-out | 77–100 | 275–356 | 25 | 655,272 |
| Fan-in | 299–323 | 536–541 | 8,204 | 786,344 |
| Local equalities | 31–32 | 110–119 | 2 | 196,640 |

Across a 64× input increase (128 to 8,192), the empirical exponent
\(\log(t_{8192} / t_{128}) / \log(64)\) is 0.913–1.018 for solve and 0.872–0.978
for construction + solve + replay-context. This is consistent with the solver's
near-linear design, not quadratic dependency scheduling. Sublinear endpoints do
not imply a sublinear algorithm: fixed costs and allocator/cache effects are
amortized. Three sizes and finite synthetic graphs are not an asymptotic proof.

Conflicting and grounded cycles stay in the same cost range as chains. Unresolved
cycles remain cheaper, but still allocate adjacency lists even though their work
queue receives no evidence. There is no observed retry explosion on these cycles.

**Allocation topology is a stronger finding than small timing differences.** A
chain allocates an inner `Vec` for almost every provider in `Vec<Vec<usize>>`.
Fan-out instead grows one adjacency vector and its queue. It has nearly identical
requested-byte traffic but over 300× fewer allocation calls and a 3–4× faster
solve in these runs. This strongly motivates testing a contiguous adjacency
representation; it does not prove the entire difference is allocator overhead.

For either chain, creating a replay context at this size costs 58–68 µs and
38 allocations requesting 556,984 bytes. Rebuilding three vectors by repeated
`fresh()` calls accounts for their geometric growth. Exact-size initialization
is a focused candidate for reducing traffic and allocation count. These numbers
exclude the checker's later obligation replay; only `hir/analyze` measures that.

### Cost in the checker

At 8,192 functions:

| HIR program | Analyze, ms | Allocation calls | Requested bytes |
|---|---:|---:|---:|
| Annotated forward | 7.99–8.33 | 73,814 | 11,233,966 |
| Annotated reverse | 8.03–8.65 | 73,814 | 11,233,966 |
| Inferred forward | 7.57–8.78 | 82,107 | 14,878,790 |
| Inferred reverse | 8.83–8.90 | 82,107 | 14,878,790 |
| Grounded cycle | 8.21–8.36 | 82,116 | 16,190,776 |
| Unresolved cycle | 8.73–9.36 | 90,313 | 19,285,472 |
| Conflict cycle | 8.77–9.01 | 90,327 | 20,688,752 |
| 16 locals/function | 111–126 | 843,958 | 199,961,878 |

HIR endpoint exponents are 1.008–1.111. There is modest superlinear wall-time
growth over this range, unlike the isolated solver. This suite does not isolate
its cause; larger working sets, hash tables, allocation, and diagnostic sorting
are candidates, not measured attributions.

An inferred chain requests **32.4% more allocation traffic** than its annotated
control, with about one additional allocation per function. This aligns with the
solver's per-provider adjacency allocations. Timing is less conclusive: the
inferred-forward mean moves by 15.9% between runs and overlaps annotated timings.
Do not use one run to claim inference is free or faster than annotations.

The isolated chain lifecycle is roughly half a millisecond versus roughly eight
milliseconds for complete checking. This suggests graph solving is not the only
important cost, but **the ratio is not a profile-derived percentage**: the two
benchmarks have different setup, batching, and construction work. The much larger
locals workload further shows why optimizing just the fixed point cannot stand
in for measuring the whole checker.

### Regression control against the pre-solver checker

The same annotated-source fixtures and analysis harness were also run twice on
commit [b8f622b](https://github.com/sumi-lang/sumi/commit/b8f622bda50fc4807dbc4a5d6f935b064ca142f2)
(the parent of return inference). Only the benchmark dependency
and harness were added there; no semantic implementation was changed. Use a
separate worktree **and separate target directory** when repeating this comparison.
Select `annotated` as the Criterion filter; inferred cases are intentionally not
accepted by the old checker. Fixture validation caught a stale shared-target
binary during preparation; that failed run was discarded and rebuilt.

At 8,192 functions, old annotated-forward checking took 7.47–7.49 ms and old
annotated-reverse checking 7.57–7.62 ms. Comparing the ranges with current means
gives **6.7–11.6% forward and 5.4–14.2% reverse overhead**. These are empirical
cross-run ranges, not statistical confidence intervals. The 1,024-function
comparisons overlap/noise is larger, so a universal percentage is not justified.

The deterministic allocation comparison is clearer: old annotated checking
requested 8,735,886 bytes in 73,789 calls, versus 11,233,966 bytes in 73,814 calls
now: **28.6% more traffic, but only 25 more calls**. This rules out thousands of
additional output-buffer allocations as the explanation for this control. The
draft representation and extra header/body bookkeeping increase the sizes and
number of retained intermediate arrays even when there are no inference
variables. This recovery/publication architecture has a measurable cost separate
from solving unknown types.

## Follow-up priorities and limits

1. Test compact adjacency storage against chains *and* fan-out/fan-in; preserve
   monotone conflict propagation and avoid replacing it with whole-graph retries.
2. Pre-size replay-context vectors; measure both allocation traffic and HIR cost.
3. Investigate the annotated-control intermediate storage overhead before adding
   a second checker/fast path that duplicates semantic rules.
4. Use CodSpeed's instruction/memory profiles and a controlled wall-time runner
   for smaller changes; orb bootstrap intervals alone are insufficient.

No solver optimization is bundled with this suite. These are scalar synthetic
workloads, not a claim about future closures/generics, arbitrary dense graphs,
production program distributions, end-to-end parse latency, or peak resident
memory. Allocation observations were repeated independently; all 96 rows matched
exactly. Keep the timing, allocation, and semantic validity checks together when
changing the workloads.
