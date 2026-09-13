# `detect_loop_bounds_only` returns nil for `for i in 0..n` (5 specs RED)

- **Status:** open
- **Found:** 2026-09-13
- **Where:** `src/compiler/60.mir_opt/mir_opt/auto_vectorize_analysis.spl`
  (`detect_loop_bounds_only`), exercised by
  `test/01_unit/compiler/mir_opt/auto_vectorize_spec.spl`

## Symptom

Five examples in `auto_vectorize_spec.spl` fail:

```
✗ for-i-in-0..n returns Some(LoopBounds)      expected false to equal true
✗ for-i-in-0..n lower bound is 0
✗ for-i-in-0..n step is 1
✗ for-i-in-0..n upper encodes local 30 as _l30
✗ for-i-in-0..arr.len upper encodes local 31 as _l31
```

`SPEC FILE VERDICT: ... executed=64 passed=59 failed=5`.

## Not caused by the AVX-512 widening

Found while landing `34b96e29837` (auto-vectorizer AVX-512 planning level).
Confirmed pre-existing by re-running the same spec with the widening disabled
(`auto_vectorize_x86_level(detect_capabilities(), false)`, forcing the old
`x86_64-v3` path): **identical** `executed=64 passed=59 failed=5`. The failures
are in dynamic loop-bounds detection, which does not read `chunk_width`.

## Impact

`detect_loop_bounds_only` failing on a dynamic upper bound means every
`for i in 0..n` loop reports an unknown trip count, so the rewriter's
divisibility and too-short guards see `trip_count = -1` and decline. Only
constant-bounded loops are reachable by the auto-vectorizer today. This caps
the real-world reach of auto-vectorization far more than the lane width did.

## Next step

Read the five expectations in `auto_vectorize_spec.spl` (they pin local-id
encoding `_l30`/`_l31`, so the defect may be in operand encoding rather than in
bounds detection itself) and bisect `detect_loop_bounds_only` against them.

## Environment note

Measured on Windows with `bin/simple.cmd run <spec>`; `bin/simple.cmd test`
cannot spawn its child on this host (`reason=child-died-early exit_code=-1`)
and reports `executed=0` for every spec, including untouched upstream ones.
