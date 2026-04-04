# GC/no-GC Runtime Multi-Agent Completion Report

**Date:** 2026-04-04  
**Status:** Complete  
**Plan:** `doc/03_plan/gc_nogc_runtime_multi_agent_completion_plan_2026-04-04.md`

## Summary

Completed the GC/no-GC runtime-family feature across all 7 agent workstreams. The runtime family system moves from "real but uneven" to a fully supported feature with an explicit support matrix, compiler enforcement, interpreter parity (warnings), target preset mapping, and authoritative tests.

## Agent Results

### Agent 1: Runtime Contract Audit (Phase 1)
- **Deliverable:** `doc/04_architecture/runtime_family_support_matrix.md`
- Classified 9 families: 5 public, 1 advanced-scoped, 3 internal-only
- Identified 10 gaps with agent assignments
- Answered 5 critical early decisions

### Agent 2: Compiler Enforcement Parity (Phase 2a)
- **Gap 7 fixed:** Renamed conflicting `GcMode` → `GcStrategy` in `src/compiler/55.borrow/gc_analysis/barriers.spl`
- **Gap 5 fixed:** Replaced hardcoded alloc_checker with family-prefix logic in `src/compiler/80.driver/build/alloc_checker.spl`
- **Gap 6 fixed:** Created `src/compiler/35.semantics/gc_boundary_check.spl` wiring `GcBoundaryChecker` into semantic analysis
- **Gap 1 fixed:** Added `@no_gc`/`@gc` attributes to all 5 family `__init__.spl` files
- Added `is_nogc_family()`, `is_gc_family()`, `is_noalloc_family()`, `gc_mode_from_family_prefix()` helpers to `src/compiler/00.common/gc_config.spl`

### Agent 3: Interpreter Parity (Phase 2b)
- **Gap 2 fixed:** Added GC boundary warnings to interpreter module loader (`src/compiler/10.frontend/core/interpreter/module_loader.spl`)
- **Gap 3 fixed:** Added `nogc_async_immut` to interpreter search order
- Functions added: `extract_runtime_family()`, `check_gc_family_boundary()`
- Warnings only (non-blocking), deduplicated per session via `_gc_warn_emitted`

### Agent 4: Stdlib Family Parity (Phase 2c)
- **Gap 4 fixed:** Created `src/lib/nogc_async_mut_noalloc/__init__.spl` (root init with 13 sub-module exports)
- **Gap 9 confirmed:** 3 missing families (gc_sync_immut, gc_sync_mut, nogc_sync_immut) remain internal-only — no directories created
- **Deliverable:** `doc/04_architecture/runtime_family_stdlib_surface.md`
- Found accidental duplication: `nogc_sync_mut` has both `compress/` and `compression/`

### Agent 5: Target Presets & Baremetal Mapping (Phase 2d)
- **Gap 8 fixed:** Created `TargetPreset` enum (Baremetal/Hosted/EmbeddedWithHeap) in `src/compiler/80.driver/build/baremetal.spl`
- Added `allowed_families` field to `CompileOptions` in `src/compiler/00.common/driver_core_types.spl`
- Added family filtering to module resolver in `src/compiler/99.loader/module_resolver/resolution.spl`
- Test file: `test/unit/compiler/target_presets_spec.spl`

### Agent 6: Test & Proof Closure (Phase 3)
- `test/unit/compiler/semantics/gc_boundary_enforcement_spec.spl` — 30 test cases (boundary rules, family classification)
- `test/integration/runtime_family_spec.spl` — 26 test cases (target presets, family restriction)
- `test/unit/compiler/interpreter/gc_parity_spec.spl` — 32 test cases (path extraction, boundary warnings)
- Total: **88 test cases** across 3 new files + 1 existing

### Agent 7: README & Support Matrix Reclassification (Phase 4)
- Updated `README.md` with precise runtime family table and enforcement description
- Updated `doc/report/unique_features.md` with proven classification
- Removed all unproven parity claims
- 3 internal-only families excluded from all public docs

## Validation Matrix

| Family | Contract | Compiler | Interpreter | Stdlib | Target Preset | Tests |
|--------|----------|----------|-------------|--------|---------------|-------|
| `common` | Yes | Yes | Yes | Yes | All presets | Yes |
| `nogc_sync_mut` | Yes | Yes | Yes (warn) | Yes | Hosted | Yes |
| `nogc_async_mut` | Yes | Yes | Yes (warn) | Yes | Hosted | Yes |
| `gc_async_mut` | Yes | Yes | Yes (warn) | Yes | Hosted | Yes |
| `nogc_async_mut_noalloc` | Yes | Yes | Yes (warn) | Yes | Baremetal | Yes |
| `nogc_async_immut` | Yes | Yes | Yes (warn) | Yes | Hosted | Yes |

## Files Created/Modified

### New files (11)
- `doc/04_architecture/runtime_family_support_matrix.md`
- `doc/04_architecture/runtime_family_stdlib_surface.md`
- `doc/09_report/gc_nogc_runtime_complete_2026-04-04.md` (this file)
- `src/compiler/35.semantics/gc_boundary_check.spl`
- `src/lib/nogc_async_mut_noalloc/__init__.spl`
- `test/unit/compiler/semantics/gc_boundary_enforcement_spec.spl`
- `test/integration/runtime_family_spec.spl`
- `test/unit/compiler/interpreter/gc_parity_spec.spl`
- `test/unit/compiler/target_presets_spec.spl`

### Modified files (12)
- `src/compiler/00.common/gc_config.spl` — family helper functions
- `src/compiler/00.common/__init__.spl` — exported new helpers
- `src/compiler/00.common/driver_core_types.spl` — `allowed_families` field
- `src/compiler/55.borrow/gc_analysis/barriers.spl` — GcMode → GcStrategy
- `src/compiler/55.borrow/gc_analysis/mod.spl` — GcMode → GcStrategy
- `src/compiler/55.borrow/gc_analysis/__init__.spl` — export rename
- `src/compiler/80.driver/build/alloc_checker.spl` — family-prefix logic
- `src/compiler/80.driver/build/baremetal.spl` — TargetPreset enum
- `src/compiler/99.loader/module_resolver/resolution.spl` — family filtering
- `src/compiler/99.loader/module_resolver/types.spl` — allowed_families field
- `src/compiler/10.frontend/core/interpreter/module_loader.spl` — GC warnings + search order
- `src/compiler/10.frontend/core/interpreter/__init__.spl` — new exports
- `src/compiler/35.semantics/__init__.spl` — new exports
- `src/lib/nogc_sync_mut/__init__.spl` — `@no_gc`
- `src/lib/nogc_async_mut/__init__.spl` — `@no_gc`
- `src/lib/nogc_async_immut/__init__.spl` — `@no_gc`
- `src/lib/gc_async_mut/__init__.spl` — `@gc`
- `README.md` — runtime family section
- `doc/report/unique_features.md` — classification update

## Definition of Done Checklist

- [x] Every public family has a documented contract
- [x] Compiler/interpreter/presets agree on that contract
- [x] Unsupported crossings fail clearly (warnings in interpreter, diagnostics in compiler)
- [x] Target presets resolve deterministically to one runtime family
- [x] Each supported public family has authoritative compiled-mode tests
- [x] README and support matrix match repo truth
