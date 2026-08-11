# Native Pool Loop Closure Capture Fanout Mismatch

Status: likely-fixed (triaged 2026-06-11, evidence: resolved/fixed content in body)

## Summary

Generated multicore-green fanout workloads that submit escaped runtime-pool
closures from a loop previously captured the loop seed incorrectly in native
builds. This is fixed for the current hosted native path.
The workload shape:

```spl
for seed in 0..1000:
    handles.push(multicore_green_spawn(\: work(seed)))
```

compiled and ran with `pool_used=1000/1000`, but produced checksum mismatches
before the fix.
Wrapping the closure in `spawn_work(seed_copy)` still mismatched, which means the
escaped closure environment is not preserving the per-call value strongly enough
for the runtime-pool handoff.

## Evidence

### Original Failure

- `build/cross_lang_perf/fanout_multicore_green_simple_native` printed
  `multicore_green_pool_used = 1000/1000` followed by checksum mismatch.
- `build/cross_lang_perf/fanout_stress_multicore_green_simple_native` printed
  `multicore_green_pool_used = 512/512` followed by checksum mismatch.

### Fixed Evidence

`SIMPLE_BINARY=./src/compiler_rust/target/debug/simple RUNS=1
REPORT_PATH=doc/09_report/cross_language_perf_parallel_smoke.md sh
scripts/check/check-cross-language-perf.shs` now reports
`profile_report_contract=true` with compact loop-submitted fanout closures:

- `Simple multicore green (native)` fanout: `pool_used=1000/1000`,
  `parallelism=64/64`.
- `Simple multicore green (native)` stress fanout: `pool_used=512/512`,
  `parallelism=64/64`.

## Resolution

Native closure creation now uses runtime heap allocation instead of stack
allocation, and outlined lambda functions materialize captured values as real
capture locals hydrated from the closure context. The profile generator again
uses compact loop submission, so checksum validation covers loop-local capture.
