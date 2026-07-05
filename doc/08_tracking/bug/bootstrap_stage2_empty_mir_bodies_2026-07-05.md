---
id: bootstrap_stage2_empty_mir_bodies_2026-07-05
status: OPEN
severity: critical
discovered: 2026-07-05
discovered_by: Bootstrap stage-2 binary verification
related: src/app/bootstrap/driver_bootstrap.spl
related: src/app/bootstrap/driver_pipeline.spl
related: build/bootstrap/stage2/aarch64-apple-darwin/simple
---

# Stage-2 Bootstrap: All function bodies empty (ret-0 stubs)

## Summary

Stage-2 bootstrap binary (`build/bootstrap/stage2/aarch64-apple-darwin/simple`, 34,904 bytes) compiles and links successfully but contains zero actual function implementations. All 6 function bodies are ret-0 stubs as shown by `[hir-lower] bootstrap-functions:count 0` in the build log, totaling only 48 bytes in the `__TEXT` segment. The binary exits cleanly on `--version` but prints nothing, confirming the stub-only state.

## Evidence

- Binary size: 34,904 bytes (viable link output)
- HIR lowering report: `[hir-lower] bootstrap-functions:count 0` (zero real function bodies)
- Symbol count: 6 functions declared but not implemented
- Total function bytes: 48 bytes across all 6 functions (stub-only)
- Runtime behavior: `bin/release/aarch64-apple-darwin/simple --version` exits 0 with no output

## Impact

Stage-2 binary is unusable for stage-3 self-host verification. Blocks any usable stage-2+ binary and prevents bootstrap progression beyond stage 1 (Rust seed).

## Scope

The defect is in `driver_bootstrap.spl` or `driver_pipeline.spl` lowering path. The stub-fallback policy ("intentionally rejected") is being violated — functions are marked as stubs and never lowered to MIR. This is a pre-existing regression (identical 576-byte object file produced before the `_main` link fix), suggesting the root cause predates recent bootstrap changes.

## Next Steps

Investigate why `driver_bootstrap.spl`/`driver_pipeline.spl` lowering is skipping function bodies entirely. Verify that the HIR-to-MIR lowering for bootstrap entry points is reachable and not short-circuiting. Add detailed logging to trace the path from HIR parsing through MIR emission for bootstrap functions.
