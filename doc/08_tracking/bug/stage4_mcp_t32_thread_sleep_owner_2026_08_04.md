# Stage 4 T32 MCP thread-sleep owner

## Status

Source fixed; focused native contract PASS; exact Phase 4 verification requires
a fresh bounded session.

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
