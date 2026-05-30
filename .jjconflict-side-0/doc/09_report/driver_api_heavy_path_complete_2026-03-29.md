# Driver API Heavy Path Stabilization — Completion Report

**Date:** 2026-03-29
**Status:** Complete
**Requirements:** `doc/02_requirements/feature/driver_api_heavy_path.md`
**Design:** `doc/05_design/driver_api_heavy_path.md`
**Plan:** `doc/03_plan/driver_api_heavy_path_stabilization_plan_2026-03-29.md`

## Summary

Stabilized the internal "heavy path" of `compiler.driver.driver_api` by splitting the monolithic `driver_api_core.spl` into 6 dependency tiers, generalizing the Rust loader's selective import filtering, adding opt-in loader diagnostics, cleaning up package `__init__.spl` exports, and establishing structural regression tests.

## Workstreams Completed

### WS1: Loader Diagnostics
- Added `SIMPLE_LOADER_TRACE=1` env var for opt-in structured tracing
- Traces: module resolution, init redirects, sibling preload/skip, selective filtering, circular imports, cache hits, load timing
- Implemented via `OnceLock<bool>` + `loader_trace!` macro in `module_loader.rs`

### WS2: Generalized Selective Import
- Removed hardcoded `driver_api.spl` / `driver/__init__.spl` path checks
- Generalized selective filtering to all modules under `src/compiler/` when a Group import provides requested names
- Renamed `should_keep_driver_init_export` → `should_keep_selective_export`
- Added early termination in sibling preloading when all requested names are found

### WS3: Package __init__.spl Cleanup
- Refactored `src/compiler/80.driver/__init__.spl` from bare exports to explicit `export use` statements
- Each export now points to the specific child module that defines the symbol
- No sibling preloading required for driver package imports

### WS4: Driver API Core Tier Split
Split `driver_api_core.spl` (370 lines) into 6 dependency tiers:

| Tier | File | Symbols | Compiler Graph |
|------|------|---------|----------------|
| 0 | `driver_api_types.spl` | `find_runtime_lib_dir`, externs | None |
| 1 | `driver_api_interpret.spl` | `interpret_file`, `try_load_smf_cached` | `use lazy CompilerDriver` |
| 2 | `driver_api_compile_single.spl` | `compile_file`, `compile_files`, `jit_file`, `check_file`, `parse_sdn_file`, `compile_to_smf` | `use lazy CompilerDriver` |
| 3 | `driver_api_codegen_backends.spl` | `aot_file`, `aot_c_file`, `aot_llvm_file`, `aot_cuda_file`, `aot_vhdl_file` | `use lazy CompilerDriver` |
| 4 | `driver_api_native_single.spl` | `aot_native_file_with_backend`, `aot_llvm_native_file` | `use lazy CompilerDriver` |
| 5 | `driver_api_project_build.spl` | `aot_native_project_with_backend`, `generate_headers`, `aot_shared_library` | Heavy (header_gen, linker) |

`driver_api_core.spl` reduced to 17-line re-export facade for backward compatibility.

### WS5: Cycle Breaking
- Tier split eliminated cycles: each tier has downward-only dependencies
- Tier 0 has zero compiler graph imports (verified by structural tests)
- All heavy imports use `use lazy` to avoid eager evaluation

### WS6: Policy Guardrails
- 11 structural regression tests in `driver_api_tier_policy_spec.spl`
- Enforces: no compiler graph in tier 0, no upward tier deps, facade doesn't import core, __init__ uses explicit exports, core re-exports all tiers

## Test Results

| Suite | Tests | Status |
|-------|-------|--------|
| Tier policy guardrails | 11 | All pass |
| Heavy path tiers | 26 | All pass |
| External facade | 8 | All pass |
| All compiler system tests | 682 | All pass (33 files) |
| Rust unit tests (new) | 9 | All pass |
| Rust unit tests (total) | 27/30 | 3 pre-existing std.io failures |

## Files Created

- `src/compiler/80.driver/driver_api_types.spl`
- `src/compiler/80.driver/driver_api_interpret.spl`
- `src/compiler/80.driver/driver_api_compile_single.spl`
- `src/compiler/80.driver/driver_api_codegen_backends.spl`
- `src/compiler/80.driver/driver_api_native_single.spl`
- `src/compiler/80.driver/driver_api_project_build.spl`
- `test/system/compiler/driver_api_heavy_path_spec.spl`
- `test/system/compiler/driver_api_tier_policy_spec.spl`
- `doc/02_requirements/feature/driver_api_heavy_path.md`
- `doc/05_design/driver_api_heavy_path.md`
- `doc/09_report/driver_api_heavy_path_complete_2026-03-29.md`

## Files Modified

- `src/compiler/80.driver/driver_api.spl` — Updated to import from tiers
- `src/compiler/80.driver/driver_api_core.spl` — Converted to thin re-export facade
- `src/compiler/80.driver/__init__.spl` — Explicit export use statements
- `src/compiler_rust/compiler/src/interpreter_module/module_loader.rs` — Diagnostics, generalized selective import, new tests

## Acceptance Criteria Status

1. Direct external import of all helpers terminates — **Met**
2. Grouped imports don't evaluate unrelated heavy modules — **Met** (generalized filter)
3. Heavy helpers execute or fail explicitly — **Met**
4. No import path relies on sibling preloading for public helpers — **Met**
5. Loader regressions cover grouped imports — **Met** (9 Rust tests)
6. System specs cover facade behavior — **Met** (8+26 tests)
7. Lightweight facades optional for stability — **Met** (tiers work independently)
