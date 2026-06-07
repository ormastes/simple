# SMF Runtime-Pool Closure Lookup Blocker

## Summary

SMF multicore-green workloads previously resolved
`multicore_green_set_parallelism` / `multicore_green_parallelism`, but native
runtime-pool worker threads could not look up the submitted worker function.
This is fixed for the current hosted profile path.

## Evidence

### Original Failure

```text
multicore_green_parallelism = 64/64
rt_interp_call: function not found: worker
Segmentation fault
```

### Fixed Evidence

`SIMPLE_BINARY=./src/compiler_rust/target/debug/simple RUNS=1
REPORT_PATH=doc/09_report/cross_language_perf_parallel_smoke.md sh
scripts/check/check-cross-language-perf.shs` now reports
`profile_report_contract=true` and includes valid SMF multicore-green rows:

- Parallel: `pool_used=100/100`, `parallelism=64/64`.
- Fanout: `pool_used=1000/1000`, `parallelism=64/64`.

## Resolution

Outlined lambda capture materialization now gives runtime-pool closures a stable
heap closure record and hydrated capture locals, so SMF-submitted pool tasks can
run through the same evidence gate as native tasks. The profile-report contract
now rejects SMF multicore-green failure rows instead of accepting this blocker
classification.
