# Driver API Heavy Path Stabilization Plan

Date: 2026-03-29
Area: `compiler.driver.driver_api` / interpreter module loader
Status: Implemented (2026-03-29)

## Problem

Direct external use of `compiler.driver.driver_api` used to hang during import or midway through helper execution.

The immediate public path is now stabilized with lightweight facade modules:
- `driver_public_api.spl`
- `driver_public_shared.spl`
- `driver_public_compile.spl`

That fixed the user-facing behavior, but it does not fully cure the internal heavy path. The underlying issue is that the interpreter loader and compiler package structure still allow selective imports to drag in too much of the compiler graph.

This plan describes the work needed to convert the current boundary fix into a true internal fix.

## Current State

Working now:
- external imports of `compiler.driver`
- external imports of `compiler.driver.driver_api`
- grouped imports across the stabilized helper surface
- single-file helper wrappers for:
  - `interpret_file`
  - `generate_headers`
  - `aot_shared_library`
  - `compile_file`
  - `compile_to_smf`
  - `check_file`
  - `parse_sdn_file`
  - `aot_c_file`
  - related backend helper imports

Intentional current limitation:
- `aot_native_project_with_backend` fast-fails with a clear runtime error in the lightweight external facade

Still structurally unhealthy:
- the heavy internal import graph behind `driver_api_core`
- package `__init__` and export-use expansion behavior in the interpreter loader
- sibling preloading for package exports
- selective imports that still evaluate more than the requested symbol slice

## Root Cause

The failure mode was not just "slow import". It was a structurally unhealthy load graph.

Observed characteristics:
- `driver_api` originally imported large parts of the compiler at file scope
- grouped import of one symbol still caused broad module parse/evaluation
- package-level export resolution could trigger sibling preloading
- circular import handling relied on partial exports and fallback resolution
- external import could repeatedly re-enter the same graph instead of finishing

In short:
- the dependency graph was too broad
- the loader was not selective enough
- package init behavior expanded import scope too aggressively

## Goal

Replace facade-only containment with a real internal fix so the heavy path is healthy.

Target behavior:
- importing `compiler.driver.driver_api.{symbol}` always terminates
- grouped imports evaluate only the requested symbol dependency slice
- heavy helpers may be slower than facade helpers, but never hang
- unsupported operations return explicit errors instead of stalling
- public API modules remain thin even after the internal fix

## Non-Goals

This plan does not try to:
- remove the current lightweight facades immediately
- re-implement the entire compiler driver stack in one pass
- promise support for multi-source native project helpers in the lightweight facade

## Constraints

- Existing stabilized public behavior must not regress
- Current system specs and loader regressions remain the safety rails
- We should not re-couple public helper modules back into the full compiler graph

## Workstreams

### 1. Loader Diagnostics

Add scoped diagnostics around:
- module resolution
- package `__init__` resolution
- export-use expansion
- sibling preloading
- partial export cache hits
- circular import fallback

Record:
- requested symbols
- modules actually parsed/evaluated
- repeated module visits
- depth/load counts
- time spent per module

Deliverable:
- a bounded trace that identifies which branch causes repeated re-entry for heavy `driver_api_core` imports

### 2. True Selective Import

Upgrade the interpreter loader so grouped imports are selective earlier.

Required changes:
- avoid evaluating unrelated siblings for grouped imports
- resolve only the module(s) that can define the requested names
- reduce `__init__` fallback work when the target symbol is already known

Deliverable:
- grouped import of one `driver_api` symbol evaluates only the necessary leaf modules

### 3. Package Init Cleanup

Audit compiler package `__init__.spl` files, especially under `src/compiler/`.

Refactor patterns that force whole-directory loading:
- bare exports that rely on sibling preloading
- export-use chains that traverse heavy modules
- ambiguous package-vs-file import surfaces

Preferred pattern:
- explicit child-module re-export from thin package modules

Deliverable:
- package import no longer implies loading the whole compiler subtree

### 4. Internal Driver API Split

Split `driver_api_core.spl` into dependency tiers:
- `driver_api_types`
- `driver_api_interpret`
- `driver_api_compile_single`
- `driver_api_codegen_backends`
- `driver_api_native_single`
- `driver_api_project_build`

Rules:
- downward-only dependencies
- no backend/linker/parser graph imports at the top of leaf-light modules
- no package layer should require the full compiler graph to expose one helper symbol

Deliverable:
- importing one internal helper does not load unrelated backend/linker/frontend stacks

### 5. Cycle Breaking

Identify and break import cycles involving:
- parser/frontend
- compiler package init
- driver/cache/linker
- header generation tools

Refactoring tactics:
- extract shared types into lower common modules
- remove sibling-private backreferences
- move runtime-neutral types away from implementation packages
- convert broad re-export modules into thin leaf-oriented interfaces

Deliverable:
- heavy-path import graph becomes acyclic or predictably lazy

### 6. Policy and Guardrails

Define public API module rules:
- no top-level heavy graph imports in API modules
- no sibling preloading in package init for API surfaces
- no export-use chains into heavy modules without a leaf boundary

Enforce with:
- loader regressions
- targeted system specs
- code review checklist

Deliverable:
- future helpers cannot quietly reintroduce heavy-path hangs

## Execution Order

Recommended sequence:

1. Loader diagnostics and tracing
2. True selective import in the Rust loader
3. Compiler package `__init__` cleanup
4. Internal `driver_api_core` split by dependency tier
5. Cycle breaking and common-type extraction
6. Expanded regression coverage
7. Repoint lightweight facades toward healthy internal modules when ready

## Acceptance Criteria

The internal fix is complete when all are true:

1. Direct external import of all `compiler.driver.driver_api` helpers terminates.
2. Grouped imports do not evaluate unrelated heavy modules.
3. Heavy helpers either execute successfully or fail explicitly.
4. No known import path relies on sibling preloading to expose a public helper.
5. Loader regressions cover compile-side and backend-side grouped imports.
6. System specs cover direct external facade behavior for artifact-producing helpers.
7. Lightweight facades are optional for stability, not required as containment.

## Interim Strategy

Until the internal heavy path is fully healthy:
- keep the lightweight facades in place
- keep the explicit fast-fail for unsupported multi-source native project helper calls
- prefer improving loader selectivity before merging facade logic back into heavy modules

## Tracked Artifacts

Current code boundaries:
- `src/compiler/80.driver/driver_api.spl`
- `src/compiler/80.driver/driver_api_core.spl`
- `src/compiler/80.driver/driver_public_api.spl`
- `src/compiler/80.driver/driver_public_shared.spl`
- `src/compiler/80.driver/driver_public_compile.spl`
- `src/compiler_rust/compiler/src/interpreter_module/module_loader.rs`

Current verification:
- `test/system/compiler/driver_api_external_facade_spec.spl`
- `test/system/sffi_bidirectional_interop_spec.spl`
- targeted loader regressions in `module_loader.rs`
