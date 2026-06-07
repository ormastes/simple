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
`test/03_system/feature/usage/smf_runtime_pool_closure_blocker_spec.spl`
compiles and runs a tiny source equivalent to the generated wrapper shape:
`spawn_worker() -> multicore_green_spawn(\: worker())`, then joins the native
handle. It passes today by proving the current blocker failure is explicit as
`function not found: spawn_worker`; it should be flipped to expect
`wrapper_smf_pool_pass=true` when worker-thread `rt_interp_call` can see the SMF
module function table. A direct `multicore_green_spawn(\: worker())` test is too
weak because it already passes on this checkout.

Smallest implementation direction: make `rt_interp_call` on runtime-pool worker
threads resolve against a process-visible snapshot of the SMF module function
table, or otherwise initialize the worker thread's interpreter state from the
main SMF state before invoking submitted closures. Do not change the
`rt_pool_*` facade first; the runtime-pool symbols and closure submission path
are already reached.

## Exit Criteria

Close this blocker only after a report under `doc/09_report/` passes the profile
contract with valid SMF multicore-green rows for both the parallel and fanout
sections. Those rows must include `pool_used=N/N`, `parallelism=N/N`, and exactly
one `queue_model=work_stealing` marker.
