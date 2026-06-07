# SMF Runtime-Pool Closure Lookup Blocker

**Status:** Open

## Summary

SMF multicore-green workloads resolve
`multicore_green_set_parallelism` / `multicore_green_parallelism`, but native
runtime-pool worker threads could not look up the submitted worker function.
Fresh cross-language smoke evidence still shows that failure in the SMF rows, so
only native multicore-green rows are current M:N evidence.

## Evidence

### Current Failure Evidence

```text
multicore_green_parallelism = 64/64
rt_interp_call: function not found: worker
Segmentation fault
```

`REPORT_PATH=build/check/cross_language_perf_parallel_smoke_current.md RUNS=1
WARM_IN_PROCESS=3 CPU_WORKERS=4 OS_THREAD_WORKERS=4
COOPERATIVE_GREEN_WORKERS=4 MULTICORE_GREEN_WORKERS=4 FANOUT_WORKERS=20
FANOUT_COOPERATIVE_GREEN_WORKERS=20 FANOUT_MULTICORE_GREEN_WORKERS=20
FANOUT_ITERS=32 FANOUT_STRESS_WORKERS=32 FANOUT_STRESS_ITERS=1
RUN_TIMEOUT=30 SIMPLE_BINARY=./src/compiler_rust/target/debug/simple sh
scripts/check/check-cross-language-perf.shs` wrote fresh smoke evidence on
2026-06-07. The profile contract rejected the temporary report location because
it was outside `doc/09_report`, but the generated rows still showed:

- Parallel: `Simple multicore green (SMF)` = `fail` with
  `SMF runtime-pool closure lookup blocker`.
- Fanout: `Simple multicore green (SMF)` = `fail` with
  `SMF runtime-pool closure lookup blocker`.
- Native multicore-green rows still passed with `pool_used=N/N`,
  `parallelism=N/N`, and `queue_model=work_stealing`.

## Contract

`test/05_perf/profile_scripts/profile_report_contract_test.shs` may allow this
exact SMF failure classification only while this blocker document exists and is
marked `Status: Open`. The contract still rejects failed native multicore-green
rows, missing runtime-pool evidence, missing parallelism evidence, global-FIFO or
scheduler-owned queue evidence, and ambiguous queue-model markers.

## Exit Criteria

Close this blocker only after a report under `doc/09_report/` passes the profile
contract with valid SMF multicore-green rows for both the parallel and fanout
sections. Those rows must include `pool_used=N/N`, `parallelism=N/N`, and exactly
one `queue_model=work_stealing` marker.
