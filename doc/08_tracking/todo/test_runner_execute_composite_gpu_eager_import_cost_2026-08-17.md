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
