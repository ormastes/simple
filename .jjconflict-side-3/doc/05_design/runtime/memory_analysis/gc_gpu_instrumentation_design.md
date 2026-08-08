# GC-tier + GPU-tier instrumentation design (cross-cutting req 1, M7)

Predecessor: `doc/03_plan/runtime/memory_analysis/memory_infra_next_phase_plan_2026-07-29.md`
(req 1, M7) and the allocator-model matrix in
`doc/02_requirements/runtime/memory_analysis/feature_backend_memory_infra_toggle.md`.
Builds on M1 (`src/compiler_rust/runtime/src/value/heap.rs`) and M3
(`src/lib/common/mem_infra/config.spl`).

## 1. GC truth: vestigial, not running

Grep across `src/compiler_rust/runtime/src` for `mark`/`sweep`/
`collect_garbage`/`gc_collect` found none: **no tracing collector runs
against the runtime's own value heap.** Two real-but-disconnected pieces
exist plus one real, unrelated collector:

- `value/heap.rs` `HeapHeader.gc_flags` + `gc_color()`/`set_gray`/`set_black`/
  `set_white` (lines 54, 104-158): tri-color bits are **defined and
  settable** but nothing reads them to drive a mark phase — no root-scan, no
  trace, no reclaim loop. Objects here are freed **manually**:
  `unregister_heap_ptr`/`unregister_heap_ptr_checked` (heap.rs:242-282),
  called explicitly at interpreter free sites — the M1 malloc-backed nogc
  tier, already wired per L1-L7.
- `concurrent/gc_barrier.rs`: a real Dijkstra write-barrier + gray-queue
  (`GrayQueue`, `GcWriteBarrier`), but its only callers are
  `concurrent/map.rs`/`stack.rs`/`queue.rs` — barrier scaffolding for a
  future collector over those structures, never invoked from an actual
  collection cycle.
- `runtime/src/memory/gc.rs` `GcRuntime` wraps a real, running collector —
  vendored `abfall` mark-sweep (`ctx.allocate`/`ctx.heap().force_collect()`
  do mark and reclaim). Plumbed into `ExecCore`/`Runner`
  (`driver/src/exec_core.rs:56-143`, `runner.rs:93-99`) and
  `CompilerPipeline::with_gc` (`compiler/src/pipeline/core.rs:74`) — but
  every call site allocates for the **compiler pipeline's own internals**,
  not program values. No `interpreter_extern`/codegen path calls
  `gc().allocate()` for a program `Value`.

**Verdict: the GC row of the matrix is satisfied trivially today** —
`gc_async_mut` (`src/lib/gc_async_mut/**`) never routes program allocations
through a tracing collector; its actual allocations (gpu/cuda/torch
handles, §2) are opaque i64 handles into external allocators, invisible to
both the malloc-tier instrumentation and the abfall collector. M1's
`attr`/`guard`/`harden`/`genarena` rows already cover every allocation that
currently happens in this tier, because none of it goes through a GC — no
false claim to retract here.

**What would trigger real GC-row work:** the day `abfall`'s `GcRuntime` (or
any tracing collector) starts owning actual `Value` payloads — e.g. an
AST/HIR arena migrated onto it — the hooks are already identified:
`GcRuntime::allocate`/`try_allocate` (gc.rs:203-225) for alloc,
`GcRuntime::collect` (gc.rs:229-254) for sweep, which already returns
`before`/`after` deltas via `memory_tracker.deallocate(freed)` — a small add
posts that through `note_attr_free`-style plumbing (§3). Owner-tag survival
across `abfall`'s internal moves is unverified (`abfall::GcRoot<T>` is
opaque; needs a follow-up read of `vendor/abfall/src/heap.rs`).
`gc_barrier.rs` is a second, independent future-GC candidate for the
concurrent collections, needing its own root-scan/reclaim driver.

## 2. GPU: choke points in the rt_cuda_* wrappers

Machine has 2 GPUs (RTX A6000, TITAN RTX; `nvidia-smi` verified working),
CUDA 13.0 at `/usr/local/cuda-13.0` with `nvcc` and `compute-sanitizer`
present, and `libnvidia-ml.so.1` (NVML) installed — GPU verification here is
**not** design-only; it can run real device code.

`src/compiler_rust/compiler/src/interpreter_extern/gpu.rs` (4628 lines) is
the SFFI boundary: `rt_cuda_*_fn` wrappers (808-1356) call the CUDA
**driver API** via `dlopen` (`sym!("cuMemAlloc_v2")`/`sym!("cuMemFree_v2")`,
lines 219-220). Verified: **no pool API used anywhere in this file**
(`cuMemAllocAsync`/`cuMemPoolGetAttribute`/`cudaMallocAsync` all absent) —
every alloc is raw `cuMemAlloc_v2`, every free raw `cuMemFree_v2`, with
**zero bookkeeping**: `rt_cuda_mem_alloc_fn` (982-1000) and
`rt_cuda_mem_free_fn` (1002-1016) just forward and return the status code.
The requirement doc's "cudaMallocAsync pool stats" is **not applicable
until a pool API is adopted** — follow-up work, not a current gap.

Choke points for owner-tagged device counters (mirroring M1, §3):
- `rt_cuda_mem_alloc_fn` (gpu.rs:982): after success, before returning —
  record `(ptr, size, current_owner_id())` into a new `DEVICE_ALLOCS:
  Mutex<HashMap<u64, DeviceSlot>>`, gated like `mem_attr_enabled()`.
- `rt_cuda_mem_free_fn` (gpu.rs:1002): before the free call — remove slot,
  decrement `device_live_bytes`, leave `device_peak` (pattern of
  `note_attr_free`, heap.rs:639-651).
- Torch tensors use a **separate** allocator: `gpu_memory_torch_tensor_free`
  (`src/lib/gc_async_mut/gpu/memory.spl:28`) calls
  `rt_torch_torchtensor_free`, PyTorch's own caching allocator, not
  `cuMemAlloc_v2` — needs PyTorch's allocator-stats API (not investigated)
  or the NVML row for coarse per-process totals.
- `GpuArray<T>.drop()` (`gpu/memory.spl:141`) is the existing Simple-level
  RAII free hook — natural place for an owner-tag `text` field, set at
  `gpu_alloc`/`gpu_alloc_upload`/`gpu_alloc_zeros` (memory.spl:155-201) from
  `CURRENT_EXEC_MODULE`, mirroring `set_current_owner` at malloc-tier sites.

**NVML device-truth row (M8 CLI):** `libnvidia-ml.so.1` present; a new
`rt_nvml_*` block in `gpu.rs`, dlopen'd like the CUDA driver table
(109-125 pattern), exposing `nvmlDeviceGetMemoryInfo` per device — ground
truth to reconcile the driver-API counters against.

**Compute-sanitizer exec wrapper:** verified at
`/usr/local/cuda-13.0/bin/compute-sanitizer`; `--tool memcheck`/
`racecheck`/`initcheck` wrap `bin/release/<triple>/simple run prog.spl` as a
plain subprocess. `--mem-infra=gpu-sanitize` resolves to this wrapper in the
M3 `MemInfraPlan` (new row: all backends `false` — it wraps the whole
process, needing a matrix carve-out rather than a backend column).

**STATUS (2026-07-29): implemented as a library skeleton, not yet wired into
`MemInfraPlan`.** `src/lib/gc_async_mut/gpu/mem_profile.spl` adds
`run_under_compute_sanitizer(tool, cmd) -> (text, text, i64)` — locates
`compute-sanitizer` on `PATH` (`which`), and on absence returns a clean
`("", "compute-sanitizer not found", 127)` instead of failing hard; on
presence it execs `compute-sanitizer --tool <tool> <cmd...>` via
`rt_process_run` and forwards its result. Spec:
`test/01_unit/lib/gpu/mem_profile_spec.spl` (5/5 passing, no GPU needed —
the not-found path is forced deterministically via a scoped `PATH`
override, independent of whether the running box actually has
compute-sanitizer installed). Remaining: the `MemInfraPlan` matrix
carve-out (M3) and an actual seeded-OOB run against a real kernel launch on
this machine's GPUs (§4) are not done — this closes the library-wrapper
gap only.

**Device-trace JSON snapshot — memory_viz compatibility is UNVERIFIED.**
`device_trace_to_memory_viz(events: [DeviceAllocEvent]) -> text` (same
file) serializes the `DEVICE_ALLOCS`-shaped trace (`ts`, `owner`, `ptr`,
`bytes`, `kind`) this doc's §2 choke points would emit, once wired, into
JSON. This design doc does not specify PyTorch memory_viz's minimal
accepted snapshot shape, and no viewer test has been run against a real
memory_viz build. Per instruction, the serializer therefore emits our own
well-formed, versioned schema — `{"schema":"simple-gpu-trace","version":1,
"event_count":N,"events":[{"ts":...,"owner":"...","ptr":...,"bytes":...,
"kind":"alloc"|"free"},...]}` — **not** a claimed memory_viz payload.
**Follow-up needed:** load this JSON (or a mapped form of it) into an
actual memory_viz viewer on a GPU machine and record pass/fail before
calling it "memory_viz-compatible" anywhere else in the docs.

## 3. Shared trait shape

One shape, matching M1's existing pattern in `heap.rs` (free functions
behind a cached-bool gate, not a Rust `trait` object — zero-overhead-when-off):

```
fn <model>_note_alloc(id: usize, bytes: u64, owner: u32)
fn <model>_note_free(id: usize, bytes: u64)
fn <model>_live_bytes() -> i64
fn <model>_peak_bytes() -> i64
fn <model>_owner_report(n: usize) -> String   // top-N by live bytes
```

| model | alloc hook | free hook | owner | live/peak |
|---|---|---|---|---|
| malloc-backed nogc | `note_attr_alloc` (heap.rs:623) via `register_heap_ptr` | `note_attr_free` (heap.rs:639) via `unregister_heap_ptr` | `set_current_owner`/`current_owner_id` (heap.rs:591,618) | `rt_heap_live_bytes*`, `owner_report` (heap.rs:654) |
| GC-managed (abfall, unused for program values) | `GcRuntime::allocate`/`try_allocate` (gc.rs:203,214) | `GcRuntime::collect` (gc.rs:229) — sweep-driven, not per-object | none yet — owner tag not threaded through `abfall::GcRoot<T>` | `heap_bytes`/`tracked_memory` (gc.rs:178,183); delta already computed (gc.rs:245) |
| index-based arena/slotmap | `ast_generation_bump` (`nodes.spl:309`) gated by `SIMPLE_AST_GEN_CHECK` (`nodes.spl:317`) | generation increment on slot reuse (same site) | not yet — only a global generation counter | none yet — L6 is UAF/staleness, not bytes |
| GPU device (cuda tier) | new: `rt_cuda_mem_alloc_fn` (gpu.rs:982) | new: `rt_cuda_mem_free_fn` (gpu.rs:1002) | new: `current_owner_id()` at alloc site | new: `DEVICE_ALLOCS` sum; NVML cross-check (§2) |
| static pools (baremetal) | out of scope — `nogc_async_mut_noalloc`, pool high-water only | n/a (pools don't free) | n/a | pool high-water/exhaustion only |

GC-tier and GPU-tier are the two gaps this doc addresses: both need the
alloc/free hook **added**, not redesigned — the malloc-tier functions are
the concrete template (`Mutex<HashMap<..>>`, `OnceLock<bool>` gate, relaxed
atomics) to copy for `DEVICE_ALLOCS` and (once wired) `GcRuntime`.

## 4. Test plan per model

- **Malloc-backed nogc**: already covered (L1-L7, M1) — no new work.
- **GC-managed (abfall)**: no fixture possible today since no program value
  allocates there — the right test is **negative**: assert `gc_async_mut`
  fixtures show zero `GcRuntime::allocate` calls, proving the vestigial
  verdict holds. Runnable without a GPU.
- **Index-based arena**: extend the L6 SSpec with a byte-counter fixture
  once `<model>_note_alloc`/`_note_free` land in `ast_generation_bump`.
  Runnable without a GPU.
- **GPU device (cuda tier)**: runnable **on this machine** (2 GPUs present).
  Seeded-leak: alloc via `rt_cuda_mem_alloc_fn`, skip the free, assert
  `device_live_bytes` stays nonzero and `owner_report` names the module.
  Seeded-OOB: `compute-sanitizer --tool memcheck` around a kernel launch
  overrunning a `cuMemAlloc_v2` buffer, assert nonzero exit + report. NVML
  cross-check: compare `DEVICE_ALLOCS` sum against `nvmlDeviceGetMemoryInfo`
  delta (coarse — assert direction, not exact equality). Torch-tensor path
  is **not** runnable through this choke point (separate allocator, §2).
  **STATUS (2026-07-29):** the exec-wrapper and trace-serializer library
  pieces are done and spec-covered without a GPU
  (`test/01_unit/lib/gpu/mem_profile_spec.spl`, 5/5 passing) — see the
  "STATUS" notes under the compute-sanitizer paragraph above. The
  `DEVICE_ALLOCS` bookkeeping itself, the seeded-leak/seeded-OOB runs
  against real device code, the NVML cross-check, and the memory_viz
  viewer verification are all still open (require Rust changes to
  `gpu.rs`, out of this file's scope — owned separately per M7 task
  split).
- **Static pools**: design-only regardless of machine — `nogc_async_mut_noalloc`
  targets baremetal/QEMU; covered by the existing board-runnable rule.
