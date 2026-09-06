# Stage 4 T32 MCP thread-sleep owner

## Status

Thread and file-read owners fixed; focused native contract PASS; the full
closure crossed the module.

## Symptom

The final current-head x86 Phase 4 cycle crossed the repaired WM access module,
then HIR lowering stopped in `src/app/mcp_t32/session_tools.spl` on unresolved
`thread_sleep`.

## Evidence

- Log: `build/bootstrap-stage4-x86-phase4-llvm23/logs/x86_64-unknown-linux-gnu/simple-access-topology-fresh-cycle3.log`
- Elapsed: 10m48.23s
- Peak RSS: 12,125,480 KiB
- Stub fallback: disabled
- LLVM provider: repository-managed 23.1.0-rc2 prefix

## Repair boundary

Bind `thread_sleep` to its physical synchronous thread owner,
`std.nogc_sync_mut.concurrent.thread`, rather than the broad `std.io_runtime`
facade. Preserve both retry timings and all T32 behavior.

`stage4_mcp_t32_thread_sleep_owner_contract.spl` imports the real session module,
exercises a zero-duration physical-owner sleep and a session helper, compiled
and linked 41 modules, and exited 30. The three-cycle full-closure cap is
exhausted, so no fourth Phase 4 build is permitted in this session.

A fresh full-closure cycle crossed `thread_sleep` and then reported the same
module's two free `rt_file_read_text` calls. Both reads now use the existing
`read_file` facade. The strengthened 41-module contract reads a deliberately
missing CMM path, returns an empty warning set, and exits 30. The following full
cycle crossed the entire T32 module.
