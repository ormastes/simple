# Native thread detach frees the running worker record

- Date: 2026-09-21
- Severity: P1 (native memory safety)
- Status: FIXED in source; focused macOS native check passes
- Provider: `src/runtime/runtime_thread.c`

`rt_thread_free()` detached a native worker and immediately released its
`RtThreadData`. The worker still used that record to read its closure and write
its result and completion flag. Releasing a handle before completion therefore
caused a use-after-free. `done` was also read and written without synchronization.

The public handle and worker now hold independent atomic references. Detach
releases the public reference without blocking; the worker releases its own
after publishing completion. Join consumes its result and releases the handle
reference. Handle-table exhaustion after native creation also detaches and
releases the otherwise orphaned public reference. Failed native creation still
frees the unpublished record immediately.

## Evidence

On macOS arm64, a probe holds the worker behind a synchronization gate and
observes actual record allocation/free around the production provider. Against
the parent source it aborts at `records_live == 1` immediately after detach:
the worker is blocked but its record has already been freed.

`sh scripts/check/check-runtime-thread-detach.shs` passes for both isolated
spawn signatures, joining a result, detaching a completed worker, and native
creation with an exhausted public handle table. Every case checks final
reclamation. The test uses a fail-fast unused pool-entry provider, not a success
stub. The app environment/process guard also passes.

Executable integration SSpec:
`test/02_integration/runtime/thread_detach_lifetime_spec.spl`. It compiles and
runs the current provider through the native probe, requires a successful
child exit, and checks separate receipts for both detached spawn APIs, join,
completed detach, and handle exhaustion. This exercises live workers rather
than matching implementation source text. Each receipt follows the native
scenario's lifetime and final reclamation assertions.

The updated native probe with all scenario receipts passes. SSpec execution
is pending a refreshed full self-hosted CLI: the admitted Stage 2 has no
`test` command. An attempted released-binary invocation was subsequently
identified as using the Rust seed and is not accepted as verification; it
also failed while parsing the existing `io/process_ops.spl` dependency before
executing the scenario.

AddressSanitizer binaries stalled before emitting output: the baseline was
stopped after a 15-second bounded retry and the fixed check timed out at
25 seconds. The passing evidence is the ordinary native ownership probe;
sanitizer coverage remains unverified on this host.

This fixes record lifetime for a single handle owner. It does not claim that
the legacy handle table permits concurrent free/join/read of the same handle,
nor does it establish safe cross-thread transfer of arbitrary captured values.
The broader transport P0 remains open in
`parallel_runtime_raw_value_transport_2026-08-12.md`.

No bootstrap or deployed runtime replacement was performed. Windows and Linux
were not exercised in this macOS lane.
