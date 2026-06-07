# Native Pool Loop Closure Capture Fanout Mismatch

## Summary

Generated multicore-green fanout workloads that submit escaped runtime-pool
closures from a loop can capture the loop seed incorrectly in native builds.
The workload shape:

```spl
for seed in 0..1000:
    handles.push(multicore_green_spawn(\: work(seed)))
```

compiled and ran with `pool_used=1000/1000`, but produced checksum mismatches.
Wrapping the closure in `spawn_work(seed_copy)` still mismatched, which means the
escaped closure environment is not preserving the per-call value strongly enough
for the runtime-pool handoff.

## Evidence

- `build/cross_lang_perf/fanout_multicore_green_simple_native` printed
  `multicore_green_pool_used = 1000/1000` followed by checksum mismatch.
- `build/cross_lang_perf/fanout_stress_multicore_green_simple_native` printed
  `multicore_green_pool_used = 512/512` followed by checksum mismatch.

## Current Mitigation

`scripts/check/check-cross-language-perf.shs` now keeps compact handle-array
joins but emits literal-seed runtime-pool submissions for large fanout rows, so
the profile remains valid without numbered APIs or numbered handle names.

## Required Fix

Fix native escaped closure capture so loop-local and function-parameter captures
are value-stable after the submitting function or loop iteration continues. Once
fixed, restore compact loop submission in the profile generator and keep the
checksum gate enabled.
