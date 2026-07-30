# Hosted Compositor Revision Cache Measurement - 2026-07-30

## Scope

Incremental Linux diagnostics using the cached interpreter binary. These rows
do not replace source-matched native or prepared-host acceptance evidence.

## Results

| Backend | Samples | Forced p50 | Hit p50 | Result |
| --- | ---: | ---: | ---: | --- |
| software | 21 | 4,111,102,510 ns | 4,266,039 ns | PASS; exact pixels and cache counters |
| CUDA | 3 smoke | 6,466,705,755 ns | 7,273,005,377 ns | FAIL; hit slower, source `device_identity_unknown`, handle `0`, identity `nil` |
| Vulkan | 0 | n/a | n/a | FAIL before measurement; cached interpreter lacks `rt_is_interpreter_runtime` |
| Metal | 0 | n/a | n/a | Postponed to prepared macOS host under TODO 588 |
| process/pipe | 0 | n/a | n/a | FAIL before measurement; interpreter executes the example but lacks the sandboxed-process extern, while native mode stops in test-runner compilation |

The CUDA 21-pair run first reached the 300-second bound. The three-pair smoke
mode then completed and failed the strict device-provenance gate. The process
exit was zero because the file was invoked through `simple run`; the embedded
SSpec result (`1 example, 1 failure`) is authoritative.

The response SBRF7 route benchmark did not execute because the cached runtime
reports a parser newline error while importing
`hosted_browser_renderer_worker.spl`. Direct `check` of the same import passes,
so this is not accepted as source or runtime evidence.

The process/pipe smoke was retried after rebasing a remote conflict-marker
repair. Grouping the process redirect condition moved parsing into
`browser_session.spl`; normalizing split assignments and grouping its first
ungrouped header condition did not clear the remaining newline error before the
three-cycle cap. All three runs executed zero examples, so no timing, pipe, or
GPU claim is admitted.

A fresh capped cycle normalized the sole split assignment in
`js/engine/runtime.spl`. Interpreter mode then executed one example and failed
at `rt_browser_renderer_spawn_sandboxed`, which is intentionally implemented by
the native C runtime but is absent from the Rust interpreter dispatch. Native
mode reached compilation and failed on nested `trim_start` calls in the
pure-Simple test runner; those receiver chains are now staged explicitly but
were not rerun after the third cycle. No process/pipe measurement is admitted.

The next native-only cycle cleared the nested-call failure. Its first run
exposed `get_temp_dir()` resolving to `nil` in the flattened test-runner closure.
The stale `src/lib` platform mirror was aligned with the already-correct
`src/std` nil guards, and the focused owner spec passes 2/2. Because the closure
still selected a colliding symbol, the test runner now owns a uniquely named
fail-closed temp adapter; the next run advanced from `nil/...` to `/tmp/...`.
The third run then exposed the SPipe linter rejecting the wrapper's generated,
valid `expect condition` assertions. Both lint implementations now admit
nonempty infix expectations, and the focused Rust regression passes 1/1. The
benchmark was not rerun after the three-cycle cap, so timings remain unproven.

A fresh source-pinned native cycle used absolute `SIMPLE_LIB` and worker
executable paths from commit `a9ee4f425284`. The first run confirmed the
generated wrapper still received source-spec lint under the deployed compiler.
The second retained the wrapper and proved its lowered `expect condition`
assertions were valid but its `_spec.spl` suffix incorrectly triggered that
lint. Generated native wrappers now end in `_native.spl`; the focused
preprocessing regression passed 1/1 before its consecutive-declaration coverage
was strengthened. The third run cleared lint and exposed
`PIPE_PERF_PAIRS` as undefined because the wrapper moved every second
consecutive top-level declaration into `main`. The state transition now
reclassifies the terminating line before body lowering, and the regression pins
both declarations before generated `main`. A direct source check was stopped by
the repository's 60-second CPU monitor (retained output:
`/tmp/check-test-runner-execute-20260730.log`). The strengthened declaration,
class, function, and `describe` placement assertions postdate the earlier 1/1
pass and remain unrun. The benchmark was not rerun after the three-cycle cap.
No timing or process/pipe acceptance is claimed.

The following capped cycle cleared generated declaration placement and reached
the native HIR. All three runs failed before execution because imported class
construction left the renderer receiver as `ANY`, so `started.ok` could not be
lowered even when each method result had an explicit
`HostedBrowserRendererResult` annotation. The retained third wrapper at
`/tmp/spipe_wrapped__home_ormastes_dev_pub_simple-gpu-goal_test_05_perf_browser_hosted_browser_process_pipe_perf_spec_native.spl`
confirms only those earlier method-result annotations survived preprocessing.
Renderer and compositor receivers plus all aggregate render results are now
explicitly typed, but that later strengthening is unrun after the three-cycle
cap. No samples or timing claim were produced.

A subsequent source-matched native lane ran twice with absolute library and
worker paths. It confirmed imported aggregate receivers still erase to `ANY`
in the generated wrapper, most recently at `producer_generation`. Both
attempts produced zero samples. Retained output:
`/tmp/hosted-process-pipe-native-owned-20260730-final.log`.

## Required Follow-up

1. Run the 21-pair CUDA and Vulkan rows with the admitted source-matched
   pure-Simple runtime.
2. Require exact pixels, `device_readback`, positive stable handle and device
   identity, one reuse per forced render, and a hit p50 at least five percent
   below forced-render p50.
3. Run the Metal and Vulkan commands in
   `doc/03_plan/agent_tasks/gpu_backend_mac_host_remaining.md` on macOS.
4. Run `test/05_perf/browser/hosted_browser_process_pipe_perf_spec.spl` with
   the source-matched executable. It covers request encoding, pipe copies,
   process scheduling, worker execution, response decode, and compositor reuse.
