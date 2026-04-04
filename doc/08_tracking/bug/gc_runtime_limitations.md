# Runtime Family — Known Limitations

**Feature:** GC/no-GC Runtime Families
**Date:** 2026-04-04
**Status:** Implemented with known limitations
**Source:** `doc/04_architecture/runtime_family_support_matrix.md` (Sections 3–4), `doc/04_architecture/runtime_family_stdlib_surface.md` (Section 4), `doc/09_report/gc_nogc_runtime_complete_2026-04-04.md`

---

## Limitation ID: LIM-RTFAM-001
**Severity:** Medium
**Component:** Interpreter — `src/compiler/10.frontend/core/interpreter/module_loader.spl`
**Description:** Interpreter GC boundary warnings are advisory only. The interpreter emits warnings when code crosses GC family boundaries (e.g., a `nogc_*` module calls into `gc_async_mut`) but does NOT block execution. Execution proceeds regardless of the violation.
**Impact:** Code that violates family boundaries will run silently in interpreter mode. The same code may fail or behave incorrectly in compiled mode where `GcBoundaryChecker` enforces stricter rules. This creates a false sense of safety during development.
**Workaround:** Always validate family-boundary-crossing code in compiled mode (`bin/simple build`) before shipping. Do not rely on interpreter mode alone to catch GC boundary violations.
**Fix plan:** Promote boundary violations from warnings to errors in a future compiler release. Requires a flag like `--strict-gc-families` so existing code is not broken immediately.

---

## Limitation ID: LIM-RTFAM-002
**Severity:** High
**Component:** Stdlib — `src/lib/`
**Description:** Three runtime families are internal-only and have no implementation: `gc_sync_immut`, `gc_sync_mut`, and `nogc_sync_immut`. No source directories exist for these families. Attempting to `use std.gc_sync_immut.*`, `use std.gc_sync_mut.*`, or `use std.nogc_sync_immut.*` will produce module-not-found errors at resolution time.
**Impact:** Code expecting these families cannot compile. `test/unit/lib/gc_sync_mut/` contains 4 orphaned spec files (`gc_root_spec.spl`, `gc_specific_spec.spl`, `ptr_parity_spec.spl`, `rc_spec.spl`) that will fail with module-not-found. These tests were likely written against types (`GcHeap`, `Rc`, `Arc`) that now live in `nogc_sync_mut`.
**Workaround:** Use `nogc_sync_mut` for GC-related reference-counted types (`GcHeap`, `Rc`, `Arc`). For purely immutable sync code, use `common`. Relocate orphaned `gc_sync_mut` tests to `test/unit/lib/nogc_sync_mut/`.
**Fix plan:** Formally mark the three families as "deferred" in the support matrix (already documented in Section 5 of the matrix). Relocate orphaned tests. No directory creation planned.

---

## Limitation ID: LIM-RTFAM-003
**Severity:** Medium
**Component:** Stdlib + Interpreter — `src/lib/nogc_async_immut/`, `src/compiler/10.frontend/core/interpreter/module_loader.spl`
**Description:** `nogc_async_immut` has limited test coverage (only 22 files, classified advanced-scoped) and its root `__init__.spl` exports only a version function — no data structure types are re-exported. The family was added to the interpreter search order (Gap 3 fix) but still requires explicit qualified imports (`use std.nogc_async_immut.persistent_map.*`) because the root init provides no type surface.
**Impact:** Users cannot discover or use persistent data structures (`PersistentMap`, `PersistentVec`, `Atom`, `Ref`, etc.) via short-form imports. The family is effectively invisible without knowing exact sub-module paths. CAS atom operations are untested in compiled mode.
**Workaround:** Use fully qualified sub-module imports: `use std.nogc_async_immut.persistent_map.PersistentMap`.
**Fix plan:** Enrich `src/lib/nogc_async_immut/__init__.spl` with core type exports (Gap 9 in support matrix, deferred from Phase 2c). Add at least 5 unit tests for core data structures. Verify CAS operations in compiled mode.

---

## Limitation ID: LIM-RTFAM-004
**Severity:** Low
**Component:** Stdlib — `src/lib/nogc_sync_mut/`
**Description:** `nogc_sync_mut` contains both `compress/` and `compression/` sub-directories. Both exist and likely contain overlapping compression functionality. The duplication was discovered during the stdlib surface audit (Phase 2c) and confirmed unresolved.
**Impact:** Ambiguity for users choosing a compression module. Potential API inconsistency between the two directories. Increased maintenance surface.
**Workaround:** Prefer `compress/` as the canonical directory until consolidation occurs. Inspect both directories before depending on either to verify which is more complete.
**Fix plan:** Audit contents of both directories, designate one canonical, merge unique functionality, remove the duplicate. Tracked in `doc/04_architecture/runtime_family_stdlib_surface.md` Section 5.2.

---

## Limitation ID: LIM-RTFAM-005
**Severity:** Medium
**Component:** Compiler — `src/compiler/00.common/gc_config.spl`, `src/compiler/99.loader/module_resolver/resolution.spl`
**Description:** Family enforcement is path-based, not semantic. The compiler infers a module's runtime family from its directory prefix (e.g., a file under `src/lib/nogc_sync_mut/` is treated as no-GC). There is no deep semantic analysis verifying that the file's actual code conforms to the family contract. A file manually placed in the wrong family directory will not be caught by the compiler.
**Impact:** A developer can accidentally place a GC-allocating module inside `nogc_sync_mut/` or a heap-allocating module inside `nogc_async_mut_noalloc/` without receiving a compile error. Only the `alloc_checker` (for `@alloc`-annotated modules) provides any per-file verification, and it covers only a subset of the stdlib.
**Workaround:** Follow directory placement conventions strictly. Use code review to verify that modules in `nogc_*` families do not use GC-managed types. Run baremetal builds with the `Baremetal` target preset to activate `alloc_checker`.
**Fix plan:** Wire the manifest loader to propagate `GcConfig` from the family `__init__.spl` `@no_gc`/`@gc` attribute to all child modules. Add a semantic pass that verifies pointer kinds (Shared vs Unique) match the declared family GcMode.

---

## Limitation ID: LIM-RTFAM-006
**Severity:** Medium
**Component:** Runtime — all `nogc_*` families
**Description:** There is no runtime GC boundary guard. GC boundary checks happen at compile-time (via `GcBoundaryChecker` in `src/compiler/35.semantics/gc_boundary_check.spl`) and load-time only. There is no runtime mechanism to prevent a no-GC module from invoking a GC-allocating function at runtime through FFI, dynamic dispatch, or function pointers that bypass the static type system.
**Impact:** In adversarial or unusual scenarios (FFI callbacks, runtime-loaded plugins, unsafe blocks), a `nogc_*` module can trigger GC allocation without any diagnostic. On baremetal targets (`nogc_async_mut_noalloc`) this is a hard crash or memory corruption risk.
**Workaround:** Avoid dynamic dispatch and FFI callbacks that cross family boundaries. In baremetal contexts, confine all FFI to `extern fn rt_*` wrappers that are explicitly audited for allocation.
**Fix plan:** For baremetal specifically, consider a linker-level check that rejects symbols from GC-capable families. For hosted targets, a runtime family tag on function pointers is a long-term option but not currently planned.

---

## Limitation ID: LIM-RTFAM-007
**Severity:** Low
**Component:** Compiler — `src/compiler/80.driver/build/alloc_checker.spl`
**Description:** The improved `alloc_checker` (Gap 5 fix) replaced hardcoded module list with family-prefix detection, but retains a legacy fallback path. If family-prefix detection fails (e.g., for modules outside `src/lib/`, or modules loaded via absolute paths), the checker falls back to looking for individual file-level `@alloc` annotations. Many stdlib files lack these annotations, so the fallback will silently miss heap-allocating modules.
**Impact:** Baremetal builds using non-standard module paths may not receive alloc-violation diagnostics. The false-negative rate of the legacy path is unknown.
**Workaround:** Ensure all custom modules intended for baremetal use are placed under `src/lib/nogc_async_mut_noalloc/` or annotated with `@no_alloc` at the file level. Do not rely on the legacy fallback for safety-critical baremetal code.
**Fix plan:** Remove the legacy fallback path and require all modules to be either family-prefixed or explicitly annotated. This is a breaking change requiring a deprecation period.

---

## Limitation ID: LIM-RTFAM-008
**Severity:** Low
**Component:** Compiler CLI — `src/app/cli/main.spl`
**Description:** The `TargetPreset` enum (`Baremetal`, `Hosted`, `EmbeddedWithHeap`) exists in `src/compiler/80.driver/build/baremetal.spl` and is wired into `CompileOptions.allowed_families` and `ModuleResolver`. However, there is no CLI flag to select a preset at the command line. The only way to activate a non-default preset is programmatically via `BaremetalConfig.compile_options()` or by setting `CompileOptions.allowed_families` directly in build scripts.
**Impact:** Users cannot select the `EmbeddedWithHeap` preset (or override family restrictions) from `bin/simple build` without modifying source. Baremetal presets are activated only through `BaremetalConfig.arm()`, `BaremetalConfig.x86_64()`, `BaremetalConfig.riscv()` — which are internal to the build driver, not user-facing.
**Workaround:** Use `BaremetalConfig` directly in project build scripts. For `EmbeddedWithHeap`, construct `CompileOptions` manually with the desired `allowed_families` list.
**Fix plan:** Add `--target-preset=<baremetal|hosted|embedded-with-heap>` CLI flag to `bin/simple build`. Wire it through `CliArgs` → `CompileOptions`. Low priority; current use cases are served by internal API.

---

## Summary Table

| ID | Severity | Component | Short description |
|----|----------|-----------|-------------------|
| LIM-RTFAM-001 | Medium | Interpreter | GC boundary warnings are advisory, not blocking |
| LIM-RTFAM-002 | High | Stdlib | Three families internal-only; orphaned tests for `gc_sync_mut` |
| LIM-RTFAM-003 | Medium | Stdlib + Interpreter | `nogc_async_immut` limited coverage, root init exports only version fn |
| LIM-RTFAM-004 | Low | Stdlib | `compress/` and `compression/` duplication in `nogc_sync_mut` |
| LIM-RTFAM-005 | Medium | Compiler | Family enforcement is path-based only, not semantic |
| LIM-RTFAM-006 | Medium | Runtime | No runtime GC boundary guard against FFI/dynamic-dispatch violations |
| LIM-RTFAM-007 | Low | Compiler | `alloc_checker` legacy fallback may miss heap allocation in non-standard paths |
| LIM-RTFAM-008 | Low | CLI | `TargetPreset` enum not exposed as a CLI flag |
