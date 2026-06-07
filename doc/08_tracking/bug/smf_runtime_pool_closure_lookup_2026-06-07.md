# SMF Runtime-Pool Closure Lookup Blocker

**Status:** Closed

## Summary

SMF multicore-green workloads resolve
`multicore_green_set_parallelism` / `multicore_green_parallelism`, and
wrapper-shaped runtime-pool submissions now execute through compiled SMF code.
The original failure was that the hybrid compilability pass treated closure
arguments as interpreter-only even for runtime-pool spawn APIs, so helper
functions such as `spawn_worker()` were rewritten to `rt_interp_call` and failed
in standalone SMF processes.

## Evidence

### Original Failure Evidence

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

`test/05_perf/profile_scripts/profile_report_contract_test.shs` no longer allows
`SMF runtime-pool closure lookup blocker` as an acceptable report row. The
contract rejects failed native or SMF multicore-green rows, missing runtime-pool
evidence, missing parallelism evidence, global-FIFO or scheduler-owned queue
evidence, and ambiguous queue-model markers.

## Sidecar Audit - 2026-06-07

Focused smoke in `/tmp/cross_lang_perf_probe` with
`SIMPLE_BINARY=src/compiler_rust/target/debug/simple`, `RUNS=1`,
`CPU_WORKERS=4`, and tiny fanout reproduced the blocker without writing a
tracked report. The generated SMF workloads compile, resolve `rt_pool_*`, print
`multicore_green_parallelism = 4/4`, and print
`multicore_green_queue_model = work_stealing`; failure happens after native
runtime-pool worker threads call back through `rt_interp_call`.

The failing generated shapes are:

- `parallel_multicore_green.spl`: `spawn_worker()` calls
  `multicore_green_spawn(\: worker())`; the SMF run fails with
  `rt_interp_call: function not found: spawn_worker`.
- `fanout_multicore_green.spl`: `spawn_work()` calls
  `multicore_green_spawn(\: work())`; the SMF run fails with
  `rt_interp_call: function not found: spawn_work`.

`src/lib/nogc_async_mut/concurrent/multicore_green.spl` is not the narrow
blocker: a direct SMF probe that submits `worker` through
`multicore_green_spawn(\: worker())` passed and returned the expected result.
The narrow lookup issue is in the interpreter callback state used by the SMF
runtime-pool worker thread. In
`src/compiler_rust/compiler/src/interpreter_sffi.rs`, `INTERP_FUNCTIONS` is
thread-local and `interp_call_handler` only checks that thread-local function
map before reporting `function not found`. Runtime-pool workers are native
threads, so they do not inherit the main SMF interpreter function table.

Focused executable regression:
`test/03_system/feature/usage/smf_runtime_pool_closure_regression_spec.spl`
compiles and runs a tiny source equivalent to the generated wrapper shape:
`spawn_worker() -> multicore_green_spawn(\: worker())`, then joins the native
handle. It now requires exit code `0`, `got = 42`, and
`wrapper_smf_pool_pass=true`. A direct `multicore_green_spawn(\: worker())` test
is too weak because it already passed before the wrapper regression was fixed.

Resolution: runtime-pool spawn APIs are now treated as compiled closure
boundaries in `src/compiler_rust/compiler/src/compilability.rs`, preventing the
wrapper helper from entering the non-compilable set. The SMF bridge also keeps a
definition snapshot for in-process native worker callbacks in
`src/compiler_rust/compiler/src/interpreter_sffi.rs`.

## Resolution Evidence

- `test/03_system/feature/usage/smf_runtime_pool_closure_regression_spec.spl`
  requires `wrapper_smf_pool_pass=true`.
- `test/05_perf/profile_scripts/profile_report_contract_test.shs` rejects failed
  SMF multicore-green rows.
- Cross-language reports under `doc/09_report/` must contain valid SMF
  multicore-green rows with `pool_used=N/N`, `parallelism=N/N`, and exactly one
  `queue_model=work_stealing` marker.
