# TODO: test_runner_execute -> composite -> gpu_lane eager imports cost ~40s of seed-interpreter load

Date: 2026-08-17. Lane: Phase D startup-perf (compile-path slice).
Binary: `bin/release/x86_64-unknown-linux-gnu/simple` (Rust seed, per `--version` banner).

## Located cost (measured, warm, /usr/bin/time wall)

| import (one line in a fresh .spl) | wall |
|---|---|
| (empty hello) | 0.06s |
| `std.test_runner.test_runner_types` | 0.07s |
| `compiler.driver.driver.{aot_c_file}` | ~11s |
| `std.test_runner.test_executor_composite.{run_test_file_composite}` | ~37s |
| `std.gc_async_mut.gpu_lane.cuda_jit_lane_executor` | ~40s |
| `std.gc_async_mut.gpu_lane.vulkan_jit_lane_executor` | ~55s |

Chain: `test_runner_execute.spl` -> `test_executor_composite.spl` (lines 13–24)
-> jit HAL + 4 gpu_lane executors -> `compiler.backend.*` / SPIRV / CUDA ->
~300 compiler modules (`src/compiler/70.backend` 71+24 files, `60.mir_opt` 41,
`50.mir` 54, per strace of a single-spec `bin/simple test`). The seed loader is
file-granular (submodule import does NOT load package `__init__`), so the cost
is purely these explicit eager `use` lines.

## Fixed in this slice (one edge)

`src/lib/nogc_sync_mut/test_runner/doctest_runner.spl` imported
`find_simple_binary` VIA `test_runner_execute` although it is defined in
`test_executor_parsing`. That one line put execute+composite+gpu+compiler into
the closure of `test_runner_files` / `test_manifest_scanner` /
`test_executor_parsing` / `test_runner_modes` — i.e. into the single-spec
client lane. Rerouted to the defining module; single-spec
`bin/simple test <spec>` dropped ~37s -> ~12s (same tree, same binary,
identical `Results: 4 total, 4 passed, 0 failed`).

## Remaining (this TODO)

Any lane that genuinely imports `test_runner_execute` (daemon full runs,
`test_runner/main.spl`, qemu/fork/async runners) still pays the ~40s
composite->gpu->compiler load even when no composite/GPU spec is in the run.
Simple has no function-scoped `use` (probed: `use` inside `fn` does not
resolve), so the fix needs a structural cut: split the GPU/JIT lane dispatch
out of `test_executor_composite.spl` behind a lane-registry or a subprocess
boundary so the executors load only when a composite/GPU spec is actually
routed. Secondary: the seed re-reads each `src/lib/nogc_sync_mut/io/*.spl` up
to 16x in one process (1558 opens / 604 unique files per test invocation) —
seed-side (Rust), out of pure-Simple scope, noting for the seed owner.

## Fixed 2026-08-18: three more edges rerouted (fork / async / sequential_container)

Binary: `bin/release/x86_64-unknown-linux-gnu/simple` (Rust seed, 59621024 bytes,
mtime 2026-08-17 20:28). Loaded shared box — treat numbers as an envelope.

Three lib modules imported cheap helpers (`make_result_from_output`,
`find_simple_binary`, `build_child_args`) VIA `test_runner_execute` although all
are defined in `test_executor_parsing` — putting execute→composite→GPU→compiler
into their closures. Rerouted to the defining module (one `use` line each):

- `src/lib/nogc_sync_mut/test_runner/test_runner_fork.spl:33`
- `src/lib/nogc_sync_mut/test_runner/test_runner_async.spl:11`
- `src/lib/nogc_sync_mut/test_runner/sequential_container.spl:16`

Import-closure probe (`bin/simple run` of one-line `use` + hello, 3 runs):

| module | before (3 runs) | after (3 runs) |
|---|---|---|
| test_runner_fork | 41.7 / 53.9 / 61.7s | 2.9 / 2.4 / 2.2s |
| test_runner_async | 39.7 / 34.8 / 85.4s | 1.8 / 3.0 / 3.3s |
| sequential_container | 108.4 / 115.5 / (killed) | 2.4 / 2.2 / 2.6s |

This also breaks the fork→execute import cycle (execute imports fork).

Regression spec (new):
`test/01_unit/lib/test_runner/fork_async_container_parsing_reroute_spec.spl`
— `Results: 2 total, 2 passed, 0 failed`; sabotage cycle verified (renamed the
imported symbol → `Results: 2 total, 1 passed, 1 failed`, restored → green).
`doctest_runner_find_binary_reroute_spec.spl`: `Results: 2 total, 2 passed, 0 failed`.
`profile_aware_execution_spec.spl`: `Results: 20 total, 20 passed, 0 failed`.
`test_runner_result_wrapper_spec.spl`: `Results: 4 total, 3 passed, 1 failed` —
the failure ("fail-closed pure native route") string-asserts on
`src/app/test/font_evidence_runner.spl` content and is unrelated to these
reroutes (that file has concurrent uncommitted edits by another session).

## Still remaining

`test_runner_execute` itself (and thus `main.spl` full runs,
`qemu_test_runner`, `test_runner_main.spl`) still eagerly imports
`test_executor_composite` → GPU/JIT executors. Cutting that needs the
structural lane-registry / subprocess split described above — unchanged.

## 2026-08-18: split-commit INCONCLUSIVE resolved — baseline-identical-red

The `a120359d8a5` caveat ("multi-mode composite spec timed out >570s, not
proven red") is resolved by a foreground A/B on
`test/01_unit/multi_mode_test_runner_spec.spl`:

- **Current tree (post-split):** `SIMPLE_TIMEOUT_SECONDS=900 timeout 880
  bin/simple test ... --no-session-daemon` → rc=1,
  `Results: 34 total, 0 passed, 34 failed`, duration 135ms. All failures are
  `semantic: function/variable ... not found` (`parse_mode_str`,
  `TestFileResult`, `TestRunResult`, `TestModeResult`, `parse_test_args`,
  `TestExecutionMode`, ...) — the spec has only `use std.spec` and relies on
  symbol injection that does not resolve.
- **Pre-split baseline:** temp-restored the four pre-existing files from
  `a120359d8a5~1` (test_runner_main, qemu_test_runner, test_executor_parsing,
  test_runner_execute), same command → rc=1,
  `Results: 34 total, 0 passed, 34 failed`, 186ms, same `not found` class
  (incl. `TestExecutionMode`). Temp files restored; `git diff` on those paths
  empty afterward.

**Verdict: baseline-identical-red.** The lanes split did not break this spec —
it fails identically before and after, fast (no timeout under load 33). The
original >570s observation was box-load, not the spec. The red itself is a
pre-existing missing-import/injection defect in the spec, independent of the
split; track separately if the spec is meant to be green.
