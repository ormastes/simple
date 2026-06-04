# gc_boundary_crossing Lint Audit

**Date:** 2026-05-20
**Total errors found:** 187 (task said 193; ~6 fixed in recent commits)
**Lint rule:** `src/compiler/35.semantics/gc_boundary_check.spl`
**Family manifest:** `RUNTIME_FAMILY_MANIFEST` in same file

## Rank Table (from manifest)

| Family | GC Mode | Rank | Allocates | Noalloc |
|--------|---------|------|-----------|---------|
| common | neutral | 0 | false | false |
| nogc_async_mut_noalloc | nogc | 1 | false | true |
| nogc_async_mut | nogc | 2 | true | false |
| nogc_async_immut | nogc | 2 | true | false |
| nogc_sync_immut | nogc | 2 | true | false |
| async | nogc | 3 | true | false |
| nogc_sync_mut | nogc | 3 | true | false |
| gc_async_mut | gc | 4 | true | false |
| gc_async_immut | gc | 4 | true | false |
| gc_sync_mut | gc | 4 | true | false |
| gc_sync_immut | gc | 4 | true | false |

## Error Breakdown

| Count | Source Family | Violation Reason |
|-------|--------------|-----------------|
| 153 | nogc_async_mut | higher_layer_runtime_family |
| 31 | gc_async_mut | gc_imports_nogc_family |
| 2 | nogc_async_immut | higher_layer_runtime_family |
| 1 | nogc_async_mut | nogc_imports_gc_family |

## Category Analysis

### Category A: False Positives — None Found
`errors_from_common` produced zero results. No `std.common.*` import is being flagged.
The `is_common_family_path()` function correctly exempts common imports.

### Category B: Re-Export Chains — 1 error (needs architectural decision)

**File:** `src/lib/nogc_async_mut/gpu/__init__.spl`
**Error:** `nogc_async_mut` imports `gc_async_mut.gpu` (`nogc_imports_gc_family`)

This file is a re-export facade: it `use gc_async_mut.gpu.*` then re-exports GPU symbols so `use std.gpu.*` works from any family. This is a genuine architecture question — a nogc facade delegating to GC implementation.

**Options:**
1. Move the facade to `gc_async_mut/gpu/__init__.spl` — breaks `use std.nogc_async_mut.gpu` importers
2. Accept the crossing with a lint suppression annotation (if such syntax exists)
3. Provide a nogc wrapper shim that delegates to GC via FFI boundary

**Recommendation:** User decision needed. The facade is intentional delegation.

### Category C: nogc_async_mut higher_layer_runtime_family — 153 errors

**Root cause:** `nogc_async_mut` (rank 2) imports from:
- `std.async.*` (rank 3): future, task, poll, executor, scheduler, promise, io, combinators
- `std.nogc_sync_mut.*` (rank 3): io.file_ops, io.time_ops, io.process_ops, io.http_sffi, env.variables, terminal, atomic, ptr.raw, etc.

This is a **rank assignment problem**, not a code error. The `nogc_async_mut/async/` directory implements the async primitives that `std.async.*` re-exports. The actual import direction is: `nogc_async_mut/async/future.spl` implements Future and uses `nogc_sync_mut.io.time_ops` for timing. This is architecturally correct — an async layer built on sync primitives.

**The ranks appear inverted:**
- `nogc_async_mut` (rank 2) is the async runtime layer
- `nogc_sync_mut` (rank 3) is the sync I/O primitives layer
- Async runtimes necessarily depend on sync primitives — so async should be HIGHER rank than sync, not lower

**Full import target list (distinct modules flagged):**
```
nogc_async_mut/io/file.spl            → std.nogc_sync_mut.io.file_ops
nogc_async_mut/async/future.spl       → std.nogc_sync_mut.io.time_ops
nogc_async_mut/async/io.spl           → std.async.future, std.nogc_sync_mut.sffi.io
nogc_async_mut/async/scheduler.spl    → std.async.task, std.async.executor
nogc_async_mut/async/executor.spl     → std.async.task
nogc_async_mut/async/combinators.spl  → std.async.future, std.async.poll, std.async.task
nogc_async_mut/async/promise.spl      → std.async.future
nogc_async_mut/async/task.spl         → std.async.future
nogc_async_mut/concurrent.spl         → std.nogc_sync_mut.atomic
nogc_async_mut/concurrent/actor.spl   → std.nogc_sync_mut.concurrent.actor_hooks
nogc_async_mut/cuda/mod.spl           → std.nogc_sync_mut.ptr.raw
nogc_async_mut/dns/resolver.spl       → std.async.future, std.async.poll, std.nogc_sync_mut.io.*
... (153 total)
```

**Recommendation:** User decision on rank table. Two options:
1. **Swap ranks**: Set `nogc_async_mut` rank to 4, `async` to 2, `nogc_sync_mut` to 3 → async imports sync, sync imports noalloc primitives. This matches the actual dependency flow.
2. **Accept as architectural pattern**: Add a lint exception for async→sync imports within the nogc family (same gc_mode, lower rank allowed to import higher rank when gc_mode matches).

### Category D: gc_async_mut gc_imports_nogc_family — 31 errors

**Root cause:** `gc_async_mut` GPU backends directly call NoGC SFFI hooks for math, vulkan, metal, rocm, webgpu, framebuffer.

**Files involved (all in `src/lib/gc_async_mut/gpu/`):**
```
engine2d/backend_metal_helpers.spl   → std.nogc_sync_mut.io.metal_sffi
engine2d/backend_rocm.spl            → std.nogc_sync_mut.gpu.engine2d.sffi_rocm
engine2d/backend_virtio_gpu.spl      → std.nogc_sync_mut.gpu.engine2d.framebuffer_hooks
engine2d/backend_vulkan_helpers.spl  → std.nogc_sync_mut.gpu.engine2d.sffi_vulkan
engine2d/backend_webgpu.spl          → std.nogc_sync_mut.gpu.engine2d.webgpu_sffi
engine2d/backend_vulkan.spl          → std.nogc_sync_mut.gpu.engine2d.sffi_vulkan
engine2d/vulkan_session.spl          → std.nogc_sync_mut.gpu.engine2d.sffi_vulkan
engine2d/render_2d_x86_session.spl   → std.nogc_sync_mut.gpu.engine2d.sffi_vulkan
engine2d/metal_session.spl           → std.nogc_sync_mut.io.metal_sffi
engine3d/backend_baremetal.spl       → std.nogc_sync_mut.gpu.engine3d.math_hooks
engine3d/backend_cpu.spl             → std.nogc_sync_mut.gpu.engine3d.math_hooks, present_hooks
engine3d/backend_cuda.spl            → std.nogc_sync_mut.gpu.engine3d.math_hooks
engine3d/backend_intel.spl           → std.nogc_sync_mut.gpu.engine3d.math_hooks
engine3d/backend_metal.spl           → std.nogc_sync_mut.gpu.engine3d.math_hooks
... (31 total)
```

**Critical finding — doctest contradiction:**
The doctest at `gc_boundary_check.spl:164` says:
```
expect(check_gc_boundary_imports("gc_async_mut.task", ["nogc_sync_mut.fs"]).len()).to_equal(0)
```
This explicitly says GC importing NoGC should return **0 warnings**. But Rule 3 in the implementation (lines 121-122) generates `gc_imports_nogc_family` for exactly this case. The doctest predates Rule 3's addition — Rule 3 is **inconsistent with the original design intent**.

The GPU backends importing NoGC SFFI hooks is the correct architectural pattern: GC-level GPU backends call into NoGC low-level SFFI for actual GPU operations. This is by design.

**Recommendation:** User decision needed:
- **Option A (restore original intent):** Remove Rule 3 (`gc imports nogc` check) from `gc_boundary_check.spl`. Update the doctest. This eliminates 31 errors without any lib changes.
- **Option B (keep Rule 3, restructure):** Move the SFFI hook modules from `nogc_sync_mut/gpu/*/` into a `common/` layer accessible to both families.

### Category E: nogc_async_immut higher_layer_runtime_family — 2 errors

**Files:**
```
src/lib/nogc_async_immut/atom/__init__.spl → std.nogc_sync_mut.atomic
src/lib/nogc_async_immut/atom/cas.spl      → std.nogc_sync_mut.atomic
```

`nogc_async_immut` (rank 2) imports `nogc_sync_mut.atomic` (rank 3). Atoms need atomic CAS — this is a genuine dependency of immutable concurrent values on mutable atomic primitives. Same root cause as Category C: rank ordering puts async below sync when async fundamentally needs sync primitives.

**Recommendation:** Same resolution as Category C.

## Summary: No Safe Mechanical Fixes

All 187 errors fall into 4 categories, all requiring architectural decisions:

| Category | Count | Resolution Path |
|----------|-------|----------------|
| A: common/ false positives | 0 | N/A — none found |
| B: nogc re-exporting gc (gpu/__init__) | 1 | Move facade or accept crossing |
| C: nogc_async imports nogc_sync (rank inversion) | 155 | Fix rank table OR add gc_mode-match exemption |
| D: gc_async imports nogc (Rule 3 vs doctest) | 31 | Remove Rule 3 OR move SFFIs to common/ |

**The two biggest decisions:**
1. **Rank table**: Should `nogc_async_mut` be rank 4 (above sync)? This reflects actual dependency flow.
2. **Rule 3**: Should `gc_async_mut` be allowed to import `nogc_sync_mut`? Original doctest says yes.

No files were modified — conservative approach per task instructions.

## Files Examined

- `src/compiler/35.semantics/gc_boundary_check.spl` — lint rule implementation
- `src/compiler/00.common/gc_boundary.spl` — GC boundary checker (call-level, not import-level)
- `src/lib/nogc_async_mut/gpu/__init__.spl` — Category B re-export facade
- `src/lib/nogc_async_mut/async/future.spl` — Category C example
- `src/lib/nogc_async_immut/atom/__init__.spl` — Category E example
- `src/lib/gc_async_mut/gpu/engine3d/backend_cuda.spl` — Category D example
