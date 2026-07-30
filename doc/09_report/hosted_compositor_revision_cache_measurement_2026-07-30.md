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
| process/pipe | 0 | n/a | n/a | FAIL before measurement; cached runtime parser rejects `hosted_browser_renderer_process.spl` |

The CUDA 21-pair run first reached the 300-second bound. The three-pair smoke
mode then completed and failed the strict device-provenance gate. The process
exit was zero because the file was invoked through `simple run`; the embedded
SSpec result (`1 example, 1 failure`) is authoritative.

The response SBRF7 route benchmark did not execute because the cached runtime
reports a parser newline error while importing
`hosted_browser_renderer_worker.spl`. Direct `check` of the same import passes,
so this is not accepted as source or runtime evidence.

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
