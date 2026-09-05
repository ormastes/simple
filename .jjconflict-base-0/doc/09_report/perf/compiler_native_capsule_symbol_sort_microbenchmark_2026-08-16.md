# Compiler native-capsule symbol-sort microbenchmark — 2026-08-16

**STATUS: PASS (focused Phase 3 evidence; not a release or Phase 4 gate)**

## Scope

This lane measures `native_capsule_sorted_symbol_ids_v1` in
`src/compiler/80.driver/driver_types.spl`. The production change replaces its
quadratic selection sort with a typed bottom-up merge sort: `O(n^2)` becomes
`O(n log n)` comparisons with `O(n)` auxiliary storage. Ordering remains
deterministic by `SymbolId.id`; equal IDs select the left run.

The benchmark is
`test/05_perf/compiler/native_capsule_symbol_sort_bench.spl`: 4,096
reverse-ordered IDs, five sorts per timed sample, one excluded warmup, and seven
optimized samples. Empty, singleton, 4,097-element partial-tail, full ascending
sequence, endpoint, and weighted-checksum checks execute outside the timed
region.

## Provenance

- Source base: `f6cadcc36aff61d16d988651ea36a040d2af6aad`
- Host: `x86_64`, AMD Ryzen Threadripper 1950X 16-Core Processor
- Compiler: admitted pure-Simple Stage 2 at
  `/mnt/data/worktrees/restart12-compiler_perf_b/build/restart12-build11-a-r6/output/stage3/x86_64-unknown-linux-gnu/stage2-admitted/simple`
- Admission: adjacent `stage2-sanity.env` reports `schema=simple-bootstrap-sanity-evidence-v1`, `status=pass`, version `simple-bootstrap 1.0.0-beta`, and unchanged candidate hash
- Compiler SHA-256: `56eef12f581d50aa3e400c2e358db40d3320ebfcd73e54bc150221c740c537b6`
- Backend/runtime: Cranelift, `core-c-bootstrap`, strict no-stub and fabricated-stub ratchet enabled
- Rust seed: excluded from build, execution, and measurement evidence
- Baseline binary SHA-256: `16c7cb5797090b6b846727b94d1b8e4b1239fab833e517c7787ac2ef3ed7ff66`
- Final binary SHA-256: `ca1a228d4970cdc9a4dea2ec6a3e6b8b7dc9e1be9668c374d57bab2e47b8e54f`
- Final harness SHA-256: `74ff21e775cd248f0ae09a14b5f3e5e1caf2a8e7c2bb6e9c7606d5ba7c75f3f5`

Both binaries were built with the same admitted compiler, source roots, entry
closure, target, backend, and runtime bundle. The baseline receipt was `0 reused
/ 313 rebuilt`; the final receipt was also `0 reused / 313 rebuilt` after
cross-module signature invalidation. Build duration is therefore not an
incremental-performance claim.

## Results

| Revision | elapsed_us samples | p50_us | p95_us | checksum |
|---|---:|---:|---:|---:|
| quadratic baseline | `11607363` (retained sample) | n/a | n/a | `20475` endpoint checksum |
| typed merge sort | `16625, 27216, 20338, 19639, 17038, 20467, 16936` | `19639` | `27216` | `22914881536` weighted full-sequence checksum |

The optimized median is **591.04x faster** than the retained baseline sample
(`99.83%` lower elapsed time). Using the optimized p95/max instead of its median
still gives a conservative **426.49x** ratio.

Only one baseline sample was retained after the original multi-sample command's
PTY session detached; no baseline rerun was performed, honoring the scoped
no-repeat guard. The asymptotic improvement and focused correctness pass are
strong; this report does not claim a statistically complete baseline p50/p95,
whole-compiler wall-clock improvement, general test-runner admission, release
readiness, CPU pinning, or Phase 4 completion.

## Focused verification

- Admitted native build: PASS, 313 compiled / 0 failed
- Final native benchmark: PASS, seven of seven samples; exact checksum on every sample
- Optimizer app, `--full --level=O3`, on both touched `.spl` files: PASS
- Generic `array_sort_by` attempt: rejected after a fail-closed native dispatch error; no timing accepted
- Verification cycles: 3/3, converged
