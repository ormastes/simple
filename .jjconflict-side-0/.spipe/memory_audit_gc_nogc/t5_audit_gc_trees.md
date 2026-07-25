# GC Stdlib Tree Memory Audit
**Date:** 2026-06-11
**Auditor:** Claude Sonnet 4.6
**Scope:** `src/lib/gc_async_mut/` (primary), quick pass `gc_sync_mut` (mimalloc files only; no `gc_async_immut`/`gc_sync_immut` trees found — they do not exist in this repo)

## Coverage

| Subtree | Files sampled | Method |
|---------|--------------|--------|
| `gc_async_mut/js/engine/` | interpreter.spl, interpreter_exec.spl, interpreter_object.spl, interpreter_string_methods.spl, vm_object_store.spl, interpreter_async.spl (via nogc_sync backing) | grep + sed excerpts |
| `gc_async_mut/gpu/engine2d/` | backend_cuda.spl, cuda_session.spl, backend_metal_proof.spl, backend_session.spl | grep + sed excerpts |
| `gc_async_mut/gpu/engine3d/` | backend_emu.spl, backend_emu_primitives.spl, texture3d.spl | grep excerpts |
| `gc_async_mut/gpu/session/` | backend_cuda_adapter.spl, backend_webgpu_adapter.spl | grep excerpts |
| `gc_async_mut/torch/` | mod.spl, optim.spl, torch_training.spl | grep + sed excerpts |
| `gc_async_mut/mimalloc_tls.spl`, `mimalloc.spl` | full | sed excerpts |
| `gc_async_mut/http_server/` | handler.spl, router.spl, types.spl | grep excerpts |
| `gc_async_mut/io/` | rocm_sffi.spl (facade), sffi_common.spl | grep excerpts |
| `gc_sync_mut/` | mimalloc family (structure identical to gc_async_mut) | ls + spot checks |

**Not sampled:** `gc_async_mut/jit/`, `gc_async_mut/debug/`, `gc_async_mut/engine/`,
replay facades, amqp/udp wrappers (all are thin re-export facades over nogc backing).

## Runtime Context (from research_nogc_verify.md)

No garbage collector exists at runtime. Both gc and nogc trees lower to plain `malloc`/`calloc`
via `rt_alloc`. No MIR Free/Drop is ever emitted. `rt_free`/`rt_shared_release` exist as
callable externs but are **never auto-emitted**. gc trees that do not call a free extern
**leak forever**.

---

## Findings

### FINDING 1 — HIGH
**`ObjectStore.prop_obj_ids` / `prop_keys` / `prop_values`: no per-object bulk-delete path**
File: `src/lib/nogc_sync_mut/js/engine/vm_object_store.spl` (backing for both gc and nogc js engines)
Lines: 6–85

The `ObjectStore` is a flat parallel-array store indexed by object ID. Setting a property
pushes three new entries (`prop_obj_ids`, `prop_keys`, `prop_values`). Deleting a single
property (`delete_prop`) removes one slot by index. However, there is **no `delete_object`
function** — when a JS object goes out of scope, all its property rows remain in the three
parallel arrays forever. In a long-lived interpreter session (browser engine, script runner),
every new `{}` allocation plus every property assignment permanently grows these three arrays.
This is unbounded per-session growth with no eviction path.

### FINDING 2 — HIGH
**`JsInterpreter.promise_handlers` and `promise_handler_registrations`: pushed but never removed**
File: `src/lib/nogc_sync_mut/js/engine/interpreter_async.spl` lines 245, 267
Backing both `gc_async_mut` and `nogc_async_mut` js engines.

`promise_handlers.push()` and `promise_handler_registrations.push()` are called on every
`.then()`/promise creation. Neither array has a corresponding `.remove()` call anywhere in
the codebase. Promises that settle do not evict their handler records. In a server or browser
engine that processes thousands of async requests, this array grows monotonically.
`canceled_timer_ids` has the same pattern: `push()` on every `clearTimeout()` call with
**no pruning** after the timer fires.

### FINDING 3 — HIGH
**`JsInterpreter.functions` / `class_proto_fns` / `class_proto_ids`: grow per eval**
File: `src/lib/nogc_sync_mut/js/engine/interpreter.spl` lines 362, 388–389
`src/lib/gc_async_mut/js/engine/interpreter_exec.spl` lines 275, 485–488

Every JS function declaration pushes to `self.functions`; every class declaration pushes to
`class_proto_fns` and `class_proto_ids`. If the interpreter is reused across multiple script
evaluations (e.g. server-side JS, browser tabs), these arrays grow without bound. There is
no reset or scope-limited function table.

### FINDING 4 — HIGH
**`CudaSession.module_cache`: old PTX handle silently clobbered on reload**
File: `src/lib/gc_async_mut/gpu/engine2d/cuda_session.spl` lines 178–188

`load_module()` stores the new module handle in `self.module_cache` directly. If a module
was previously loaded, `cuda_module_unload(old_handle)` is **not called** before overwriting.
The old PTX module leaks on the GPU driver side. Comment says "PTX module cache (placeholder)"
— the single-slot design has no eviction. Each reload leaks one PTX module handle.

### FINDING 5 — MEDIUM
**`mimalloc_tls._g_tls_registry.heaps`: thread slot replaced with placeholder, never removed**
File: `src/lib/gc_async_mut/mimalloc_tls.spl` lines 133–157

`mimalloc_thread_destroy()` replaces the dead thread's heap record with an empty placeholder
rather than removing it. In a long-running process that creates and destroys many threads, the
`heaps` array grows monotonically (one placeholder slot per destroyed thread). Additionally,
`mi_heap_delete()` in `mimalloc.spl` is a **no-op** (`return`), so the miheap struct value
itself is never freed.

### FINDING 6 — MEDIUM
**`MetalProofBackend.cleanup()` is opt-in, not called on drop**
File: `src/lib/gc_async_mut/gpu/engine2d/backend_metal_proof.spl` lines 146–154

`rt_metal_cleanup(handle)` exists and is wired in the `cleanup()` method, but there is no
destructor/`drop()` mechanism in Simple. If a caller forgets to call `cleanup()`, the Metal
device handle leaks. The `BackendCudaAdapter.cleanup()` and `BackendWebgpuAdapter.cleanup()`
have the same pattern (lines 63–65 and 66–68 respectively) — `rt_cuda_cleanup` /
`rt_webgpu_cleanup` are only called if the user explicitly invokes the method.

### FINDING 7 — MEDIUM
**`gc_async_mut/torch/optim.spl` Adam: `m_new`/`v_new` written to `self.m[i]`/`self.v[i]` but old slot not freed before overwrite on gradient-zero path**
File: `src/lib/gc_async_mut/torch/optim.spl` lines 83–114

SGD step: when `g == 0` (no gradient), the old parameter handle `p` is freed and a clone is
pushed — correct. Adam step: `m_old` and `v_old` are explicitly freed before writing `m_new`
and `v_new` — correct for the gradient path. However, on the `g == 0` path in Adam (lines
~209–213), the corresponding `self.m[i]` and `self.v[i]` moment tensors are **not freed** —
only `p` is cloned and freed. Over many training steps with sparse gradients, moment tensors
for zero-gradient parameters accumulate as leaks.

### FINDING 8 — MEDIUM
**`http_server/handler.spl`: session state is functional (value-typed list), no server-side store**
File: `src/lib/gc_async_mut/http_server/handler.spl` lines 261–304

Session functions (`create_session`, `session_add_data`) return new list values rather than
mutating a server-side registry. This means sessions are not stored in a growing global dict.
**Positive finding** — no unbounded session registry leak here. Flagged for completeness.

### FINDING 9 — LOW
**`gc_async_mut/io/rocm_sffi.spl`: gc tree re-exports nogc_sync rocm primitives including `rocm_alloc`/`rocm_free`/`rocm_compile`/`rocm_unload`**
File: `src/lib/gc_async_mut/io/rocm_sffi.spl`

The gc tree exposes `rocm_alloc`/`rocm_free` and `rocm_compile`/`rocm_unload` (ROCm module
lifecycle). These are properly symmetric. However, callers in gc context are expected to call
`rocm_free`/`rocm_unload` manually — the gc classification creates a false expectation that
memory is managed. A gc-tree caller who doesn't call `rocm_free` will leak device memory
permanently.

### FINDING 10 — LOW
**`_promise_id_for_request_id`: O(n) linear scan over all `object_store` IDs per async resolution**
File: `src/lib/nogc_sync_mut/js/engine/interpreter_async.spl` lines 272–280

Every fetch/async resolution scans `0..next_id` looking for a matching `__simple_request_id`
property. As `next_id` grows (Finding 1), this scan becomes O(objects × properties) per
async event. Not a memory leak per se, but directly amplified by Finding 1.

---

## Summary Table

| # | File | Severity | Category |
|---|------|----------|----------|
| 1 | `vm_object_store.spl` — no bulk object delete | HIGH | Unbounded growth |
| 2 | `interpreter_async.spl` — promise_handlers/canceled_timers never pruned | HIGH | Unbounded growth |
| 3 | `interpreter_exec.spl` — functions/class_proto grow per eval | HIGH | Unbounded growth |
| 4 | `cuda_session.spl:178` — module_cache clobber leaks old PTX | HIGH | FFI lifecycle |
| 5 | `mimalloc_tls.spl:133` — dead thread slots never removed, mi_heap_delete no-op | MED | Unbounded growth + FFI |
| 6 | `backend_metal_proof.spl:146`, `backend_cuda_adapter.spl:63`, `backend_webgpu_adapter.spl:66` — cleanup opt-in only | MED | FFI lifecycle |
| 7 | `torch/optim.spl:209` — Adam zero-gradient path leaks moment tensors | MED | FFI lifecycle |
| 8 | `http_server/handler.spl` — sessions value-typed, no server registry | LOW (OK) | Cross-check |
| 9 | `io/rocm_sffi.spl` — gc tree exposes manual-free device APIs | LOW | Cross-tree |
| 10 | `interpreter_async.spl` — O(n) scan amplified by Finding 1 | LOW | Perf × leak |

## Cross-tree Violations

No `gc_*` file was found importing `nogc_*_noalloc`. One cosmetic mirror note exists
(`gc_async_mut/types.spl` references the noalloc naming in a comment). The `gc_async_mut/io/rocm_sffi.spl`
re-exports the nogc_sync_mut rocm API wholesale — this is intentional facade layering,
not an architectural violation, but exposes manual-free semantics under a gc label.

## Double-free / UAF Candidates

None identified in the sampled code. The CUDA session `_cleanup()` zeros `self.ctx` and
`self.module_cache` after destroying them, guarding against double-free on re-entry. Metal
and WebGPU adapters zero `self.handle` after cleanup. The torch optim code is careful to
free temporaries before writing new handles to `self.m[i]`/`self.v[i]` on the gradient path.
