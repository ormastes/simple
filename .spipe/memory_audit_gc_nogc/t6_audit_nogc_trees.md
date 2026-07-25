# NOGC Stdlib Trees — Memory-Perspective Audit

**Date:** 2026-06-11
**Scope:** `src/lib/nogc_sync_mut/` (1 589 files), `nogc_async_mut/` (1 770 files),
`nogc_async_mut_noalloc/` (161 files). Quick pass on immut variants.
**Coverage:** All four audit dimensions sampled across IO, net, HTTP, database, GPU, runtime/thread_local, and noalloc. Hot modules read in full; remaining sampled by grep. ~10–15 % of files read line-by-line.

---

## Finding 1 — CRITICAL: `nogc_async_mut/gpu/__init__.spl` directly re-imports `gc_async_mut`

**File:** `src/lib/nogc_async_mut/gpu/__init__.spl:13`
**Evidence:**
```spl
use gc_async_mut.gpu.*
```
The entire `nogc_async_mut` GPU surface (`gpu_init`, `gpu_alloc`, `gpu_free`, `gpu_upload`, `gpu_download`, `GpuContext`, `GpuPtr`, …) is a thin re-export of `gc_async_mut.gpu.*`. Any nogc_async_mut caller of `use std.gpu.*` transparently pulls in the gc_async_mut tree. The gc_boundary lint fires only on explicit `use std.gc_async_mut.*` segments — this alias form is invisible to it (confirmed empirically in research_nogc_verify.md).
**Severity:** HIGH — systematic boundary evasion; any `use std.gpu` from a nogc module bypasses lint entirely.

---

## Finding 2 — HIGH: `nogc_sync_mut/src/testing/gpu_helpers.spl` imports `std.compute` (resolves into gc territory) and `std.io.cuda_sffi` / `std.io.vulkan_sffi`

**File:** `src/lib/nogc_sync_mut/src/testing/gpu_helpers.spl:6`
```spl
use std.compute.{gpu_available, Gpu, gpu_default}
```
`src/lib/compute.spl` is a namespace-anchor stub (`val compute_namespace_anchor = true`); actual resolution of `std.compute.tensor` / GPU sub-paths goes through `gc_async_mut.gpu`. Additionally, `cuda_available()` and `vulkan_available()` are resolved via runtime-inline `use std.io.cuda_sffi` / `use std.io.vulkan_sffi` — paths that are not audited as gc_boundary targets. The file is under `nogc_sync_mut/src/testing/` so it is a test helper, not production, but it ships in the library tree and can be imported.
**Severity:** MEDIUM (test helper, but the import chain is undeclared and unguarded).

---

## Finding 3 — HIGH: `nogc_sync_mut/gpu/engine2d/sffi_{intel,vulkan,opencl,rocm,cuda}.spl` and `engine3d/sffi_*` import `std.gpu.*` alias

**Files (9 files):**
- `nogc_sync_mut/gpu/engine2d/sffi_intel.spl:17`, `sffi_vulkan.spl:16`, `sffi_opencl.spl:12`, `sffi_rocm.spl:17`, `sffi_cuda.spl:16`
- `nogc_sync_mut/gpu/engine3d/sffi_cuda3d.spl:15`, `sffi_intel3d.spl:12`, `sffi_rocm3d.spl:12`, `sffi_vulkan3d.spl:13`

All import `std.gpu.engine{2d,3d}.sffi_dispatch.{GpuFfiMode, FfiDispatchBase, try_load_gpu_lib}`. As established in Finding 1, `std.gpu` routes through `nogc_async_mut/gpu/__init__.spl` which directly imports `gc_async_mut.gpu.*`. These are production nogc_sync_mut files, not test helpers.
**Severity:** HIGH — 9 production SFFI files in `nogc_sync_mut` silently pull gc_async_mut types.

---

## Finding 4 — HIGH: `nogc_async_mut_noalloc` test harness uses string interpolation — potential heap allocation

**Files:**
- `baremetal/common/test_harness.spl:45,51,55,67,74,80,89`

String-interpolated literals like `"[PASS] {name}"`, `"{message}: expected {expected}, got {actual}"` are emitted via `log_raw_println`. The log facade itself (`log.spl`) correctly uses `rt_string_data`/`rt_string_len` + the `rt_simpleos_log_emit` extern for raw byte emission. However the interpolation step `"{name}"` produces a heap-allocated `text` value via `rt_string_new` before it is passed. The noalloc_checker (self-hosted, not deployed) would catch this; the deployed `bin/simple` does not.
**Severity:** HIGH for correctness in baremetal targets — every assert failure path heap-allocates.

---

## Finding 5 — MEDIUM: `HttpClient` handle has no corresponding `free`/`destroy` extern in `net/sffi.spl`

**File:** `src/lib/nogc_sync_mut/net/sffi.spl`
Only one `HttpClient` extern declared:
```
extern fn http_request(client: HttpClient, ...) -> Result<HttpResponse, SimpleError>
```
No `http_client_new`, `http_client_create`, `http_client_free`, or `http_client_destroy`. If `HttpClient` is a handle wrapping a C-side connection pool or TLS context, it leaks. If it is a value type with no C-side state, this is benign — but that is not documented.
**Severity:** MEDIUM — missing lifecycle clarity; likely a leak if HttpClient wraps C state.

---

## Finding 6 — MEDIUM: `rt_thread_local_free` exported but only called from `mimalloc_tls.spl`

**File:** `src/lib/nogc_sync_mut/runtime/thread_local.spl:11,13`
`rt_thread_local_new()` creates a TLS slot (i64 handle). `rt_thread_local_free(tls)` is exported. Grep across all of `nogc_sync_mut/` finds only one callsite: `mimalloc_tls.spl:18`. All other callers of `rt_thread_local_new` (if any) are not paired with `free`. No callers found outside the TLS module itself for the compiler or app layers.
**Severity:** MEDIUM — TLS slots created but not freed = OS-level resource leak per thread.

---

## Finding 7 — MEDIUM: `fast_db.spl` — `FastTable.destroy()` has no verified callsite outside the DB module

**File:** `src/lib/nogc_sync_mut/database/fast_db.spl:37,41`
`rt_db_table_create` → handle stored in `FastTable._handle`. `destroy()` calls `rt_db_table_destroy`. Grep across all `.spl` files outside `fast_db.spl` finds zero calls to `.destroy()` on `FastTable` instances — only engine3d/physics `destroy()` methods (unrelated). Any code that creates `FastTable` and lets it fall out of scope leaks the C-side table.
**Severity:** MEDIUM — systematic handle leak in all users of FastTable.

---

## Finding 8 — LOW: `resource_tracker` is dead for io/net/http/database

**Evidence:** `grep -rn 'resource_tracker|ResourceTracker|track_resource'` across `nogc_sync_mut/{io,net,http,database}/` returns zero results. `resource_tracker.spl` exists as a shim re-exporting `nogc_sync_mut/resource_tracker.spl`, and `test_runner_resources.spl` uses it for test metrics — but no production io/net/http/database code registers handles into it.
**Severity:** LOW (the machinery exists but is not wired to production resource paths).

---

## Finding 9 — LOW: `nogc_async_mut/gpu/engine3d/color3d.spl` and `types3d.spl` use inline `use std.gpu.*` inside doc-blocks

**Files:** `nogc_sync_mut/gpu/engine3d/color3d.spl:12`, `types3d.spl:11-13`
Lines are inside `"""` doc-example strings. Not live code, so no runtime impact. However they demonstrate the pattern and may mislead users into copy-pasting the aliased import without understanding the boundary violation.
**Severity:** LOW (documentation only).

---

## Finding 10 — INFO: No MIR-level Free/Drop is ever emitted by the deployed compiler

Confirmed by prior research: `rt_free`/`rt_unique_free`/`rt_shared_release` are registered as callable externs but zero MIR lowering paths emit a Free/Drop instruction. All allocations in every tree (gc and nogc) are effectively leaked at runtime — the distinction is naming only. Manual `close()`/`destroy()` calls in Simple code do reach the runtime, but only when explicitly authored.

---

## Summary Table

| # | Severity | Location | Issue |
|---|----------|----------|-------|
| 1 | HIGH | `nogc_async_mut/gpu/__init__.spl:13` | Direct `use gc_async_mut.gpu.*` — boundary evasion |
| 2 | MEDIUM | `nogc_sync_mut/src/testing/gpu_helpers.spl:6` | `use std.compute` + inline cuda/vulkan path imports |
| 3 | HIGH | 9× `nogc_sync_mut/gpu/engine{2d,3d}/sffi_*.spl` | `use std.gpu.*` alias pulls gc_async_mut types |
| 4 | HIGH | `nogc_async_mut_noalloc/baremetal/common/test_harness.spl` | String interpolation in noalloc = heap alloc per assert |
| 5 | MEDIUM | `nogc_sync_mut/net/sffi.spl` | `HttpClient` handle — no create/free extern declared |
| 6 | MEDIUM | `nogc_sync_mut/runtime/thread_local.spl` | `rt_thread_local_new` — free called only in mimalloc_tls |
| 7 | MEDIUM | `nogc_sync_mut/database/fast_db.spl` | `FastTable.destroy()` — zero callsites outside module |
| 8 | LOW | `nogc_sync_mut/{io,net,http,database}/` | `resource_tracker` wired to test metrics only, not production |
| 9 | LOW | `nogc_sync_mut/gpu/engine3d/color3d.spl`, `types3d.spl` | gc-alias imports inside doc strings |
| 10 | INFO | Runtime-wide | No MIR-level dealloc emitted — all frees are opt-in manual |

---

## Coverage Notes

- `nogc_sync_mut/io/file.spl`: open/close paired (`rt_io_file_open` / `rt_io_file_close`) — FileHandle.close() is the expected caller. Pattern looks correct.
- `nogc_sync_mut/net/sffi.spl`: TCP has `tcp_listener_close` + `tcp_stream_close`; UDP has `udp_socket_close`. All paired. HTTP lacks a client lifecycle extern (Finding 5).
- `nogc_async_mut_noalloc/baremetal/common/string_extract.spl`: operates on `[i64]` buffers in-place, no heap — correct.
- `nogc_async_mut_noalloc/log.spl`: uses `rt_string_data`/`rt_string_len` + `rt_simpleos_log_emit` — raw pointer path, no allocation in the logger itself. Allocation risk is in callers that pass interpolated strings (Finding 4).
