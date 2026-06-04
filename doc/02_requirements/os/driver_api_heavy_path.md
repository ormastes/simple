# Feature: Driver API Heavy Path Stabilization

**Date:** 2026-03-29
**Status:** In Progress
**Plan:** [driver_api_heavy_path_stabilization_plan_2026-03-29.md](../../03_plan/driver_api_heavy_path_stabilization_plan_2026-03-29.md)

## Summary

Stabilize the internal "heavy path" of `compiler.driver.driver_api` so that direct external imports of any driver API helper terminate predictably, without the current facade-only containment workaround.

## Requirements

### REQ-DHPS-01: Selective Import Termination
All direct external imports of `compiler.driver.driver_api.{symbol}` must terminate within bounded time. Grouped imports must evaluate only the dependency slice needed for the requested symbols.

### REQ-DHPS-02: Loader Diagnostics
The interpreter module loader must support opt-in diagnostics (`SIMPLE_LOADER_TRACE=1`) that trace:
- Module resolution decisions
- Package `__init__` resolution and export-use expansion
- Sibling preloading scope
- Circular import fallback events
- Per-module load time and depth

### REQ-DHPS-03: Generalized Selective Import
The loader's selective import filtering (currently hardcoded to `driver_api.spl` / `driver/__init__.spl`) must be generalized to all API surface modules. The `sibling_might_define_requested_names` fast-path check must apply to any package `__init__.spl` with bare exports.

### REQ-DHPS-04: Driver API Core Tier Split
`driver_api_core.spl` must be split into dependency tiers with downward-only imports:
1. `driver_api_types` — types and extern fns only
2. `driver_api_interpret` — interpret helpers
3. `driver_api_compile_single` — single-file compile helpers
4. `driver_api_codegen_backends` — backend-specific AOT helpers
5. `driver_api_native_single` — native single-file helpers
6. `driver_api_project_build` — multi-source project build

### REQ-DHPS-05: Package Init Cleanup
Compiler package `__init__.spl` files must use explicit child-module re-exports, not bare exports that rely on sibling preloading.

### REQ-DHPS-06: Cycle Breaking
Import cycles involving parser/frontend, driver/cache/linker, and header generation must be broken by extracting shared types into lower common modules.

### REQ-DHPS-07: No Regression
All existing stabilized public behavior (lightweight facade) must remain working. Existing system specs must continue to pass.

### REQ-DHPS-08: Policy Guardrails
Public API module rules enforced by regression tests:
- No top-level heavy graph imports in API modules
- No sibling preloading in package init for API surfaces
- No export-use chains into heavy modules without a leaf boundary

## Acceptance Criteria

1. Direct external import of all `compiler.driver.driver_api` helpers terminates
2. Grouped imports do not evaluate unrelated heavy modules
3. Heavy helpers either execute successfully or fail explicitly
4. No known import path relies on sibling preloading to expose a public helper
5. Loader regressions cover compile-side and backend-side grouped imports
6. System specs cover direct external facade behavior for artifact-producing helpers
7. Lightweight facades are optional for stability, not required as containment
