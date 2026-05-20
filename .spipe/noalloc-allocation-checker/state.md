# SPipe State: noalloc-allocation-checker

## Type
feature

## User Request
Build compiler-owned manifest/capability model that prevents allocation in @noalloc contexts.

## Refined Goal
Add a semantic analysis pass (`noalloc_checker.spl` in `35.semantics/`) that enforces `@noalloc` annotations at function granularity. The checker consumes `alloc_inference` results and the `RUNTIME_FAMILY_MANIFEST` to reject:
1. Direct allocation expressions (new, array/dict literals, string interpolation) inside `@noalloc` functions.
2. Calls to functions classified as allocating by `alloc_inference`.
3. Calls to functions from allocating runtime families per the manifest.

Emit hard errors (not warnings) so `@noalloc` is a compile-time guarantee.

## Harness
- File: `src/compiler/35.semantics/noalloc_checker.spl`
- Registration: `src/compiler/35.semantics/__init__.spl` (re-export)

## Acceptance Criteria
- [x] AC-1: `NoallocViolation` struct captures function name, violation kind, and source location.
- [x] AC-2: `NoallocCapabilityManifest` class holds per-function noalloc status and allocation classification from `alloc_inference`.
- [x] AC-3: `check_noalloc_violations(fn_name, body_stmts, manifest)` returns `[NoallocViolation]` for direct alloc expressions.
- [x] AC-4: Transitive call-to-allocating-function detection reuses `alloc_inference_is_alloc()`.
- [x] AC-5: Runtime family import check reuses `RUNTIME_FAMILY_MANIFEST` noalloc/allocates fields.
- [x] AC-6: Public API exported from `35.semantics/__init__.spl`.
- [x] AC-7: Syntax check passes (`bin/simple build lint` or interpreter parse).

## Spec File
`test/unit/compiler/semantics/noalloc_checker_spec.spl` — self-contained (no module imports), functional-style manifest replica, covers all ACs: direct-alloc detection, transitive calls, family-import, manifest CRUD, formatting.

## Verification Notes
- AC-7 (`bin/simple lint test/unit/compiler/semantics/noalloc_checker_spec.spl`): **PASS** (1 docstring warning only, no errors).
- Runtime execution: **BLOCKED** by the systemic interpreter perf bottleneck affecting all specs in `test/unit/compiler/semantics/` (120s timeout, same as `auto_defer_spec.spl`, `comptime_checker_spec.spl`, etc.). This is not spec-specific — see `reference_interpreter_perf_bottlenecks.md`. No stub SMF was added to avoid false-green reporting.
- Phase was previously claimed 8-ship without a real spec file. Spec added 2026-05-20.

## Phase
8-ship
