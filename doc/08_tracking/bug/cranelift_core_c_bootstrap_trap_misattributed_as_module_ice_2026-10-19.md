# `--backend cranelift` on a core-c-bootstrap producer: runtime NAMED TRAP misreported as a module ICE (2026-10-19)

Status: attribution fixed (pure Simple, takes effect once a producer is rebuilt
from this source); capability gap itself is by design and remains.

## Symptom

Phase 4 early check, lsp closure (`src/app/simple_lsp_mcp/main.spl`), producer
`scope-producer-3d9d-20261018/strict-link-preparation/simple-scope-diagnostic-strict.exe`,
`--backend cranelift --runtime-bundle core-c-bootstrap`:

```
error: native-build worker exited with code -1073740791.
error: ICE[codegen] module compiler.common.cache_contract.virtual_source_consumer_v1 (attributed): worker died inside this module (worker exit status -1073740791)
[native-build] PRESERVED DIAGNOSTICS: none matched in the full stream.
```

The same entry builds with `--backend llvm`.

## Root cause

Not a Cranelift codegen defect, and nothing in `virtual_source_consumer_v1.spl`.
The full worker stderr (spilled to `cache-lsp-cl/diagnostics/native-build-stderr-44548-1.log`,
quoted in the log's head+tail) contains:

```
simple runtime: unimplemented runtime entrypoint `spl_cranelift_new_aot_module_config_v2` was called.
```

The producer's link map (`strict-link.map`) resolves every `rt_cranelift_*` /
`spl_cranelift_*` symbol to `simple_runtime:runtime_cranelift_bridge_stub.obj`,
and the binary contains no `cranelift_codegen` crate. That stub file is the
deliberate NAMED-TRAP lane for the core-c-bootstrap bundle
(`native_project/tools.rs`, `include_cranelift_stubs`). `rt_trap_unimplemented`
calls `abort()`; the MSVC CRT turns that into a fail-fast, exit `0xC0000409`.
The module named by the ICE is simply the first uncached module codegen reached
(breadcrumb `start codegen ... cranelift` with no `done`).

Three reporting defects hid this:
1. `native_build_range_is_diagnostic` did not match the trap line, so it was
   dropped from PRESERVED DIAGNOSTICS when stderr was truncated.
2. `ice_boundary_attribute_dead_worker` blamed the module in flight with no
   mention of the trap.
3. `native_build_relaunch_past_ice_crashes` would re-launch past the module
   under `SIMPLE_ICE_CRASH_RETRIES`, trapping again in the next module.

## Fix

- `driver_ice_boundary.spl`: `ice_runtime_trap_symbol`, `ice_runtime_trap_detail`,
  `ice_boundary_attribute_dead_worker_with_stderr` — the attributed line now
  names the trapped entrypoint and says it is a producer capability gap.
- `native_build_main.spl`: trap line is a preserved diagnostic; parent prints
  `worker hit runtime NAMED TRAP ...` plus a cranelift hint; no re-launch past
  a trap.
- Tests: `test/01_unit/compiler/driver/ice_boundary_acceptance_spec.spl`
  (three new cases).

## Workaround

None in source is applicable: any module would trap at the same entrypoint.
Operationally, run Phase 4 cranelift checks only with a producer linked with the
Rust Cranelift bridge (hosted / `native_all` / Stage4 backfill lane), or use
`--backend llvm` with the core-c-bootstrap producer.
