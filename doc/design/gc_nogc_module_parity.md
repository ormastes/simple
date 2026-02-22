# GC/NoGC Module Parity

Design document tracking which modules exist in both `gc_async_mut/` and `nogc_sync_mut/`, what shared types live in `common/`, and the import mapping between modes.

**Updated:** 2026-02-22

---

## Module Parity Table

| Module | `gc_async_mut/` | `nogc_sync_mut/` | `nogc_async_mut/` | `common/` shared types |
|--------|:--------------:|:----------------:|:-----------------:|:----------------------:|
| `torch` | ✅ | ✅ | ✅ | `common/torch/interface.spl` — `TorchBackend`, `LayerForward`, `HasParameters` |
| `cuda` | ✅ | ✅ | ✅ | — |
| `gpu` | ✅ | ✅ | ✅ | `common/gpu/device.spl` — `GpuBackend`, `Gpu`, constructors |
| `gpu_runtime` | ✅ | ✅ | — | — |
| `pure` (ML algorithms) | ✅ | ✅ | ✅ | — (tensor, autograd, nn, training, data — no FFI handles) |
| `torch/dyn_ffi` | ✅ | ✅ | ✅ | — (identical, stateless DynLoader wrappers) |
| `gpu_driver` | ✅ (`gpu.spl`) | ✅ (`gpu_driver/`) | — | — (local extern fn replaces import) |
| `ml` (async-specific) | — | — | ✅ | — (async training loops + data pipeline utils) |
| math blocks `m{}` | ✅ | ✅ | ✅ | — (language feature, available in all modes) |

### Modules with NoGC copies (originals retained in `gc_async_mut/`)

| Module | NoGC Copy | Notes |
|--------|-----------|-------|
| `torch/dyn_ffi.spl` | `nogc_sync_mut/torch/dyn_ffi.spl` | Stateless DynLoader wrappers — identical copy (2026-02-22) |
| `gpu.spl` (root) | `nogc_sync_mut/gpu_driver/` | Explicit lifecycle, no owns_handle — local `extern fn` replaces import (2026-02-22) |

**Note:** Source files remain in `gc_async_mut/` for GC-mode users. No modules pending migration.

### Modules only in `nogc_sync_mut/` (NoGC-first)

| Module | Notes |
|--------|-------|
| `gpu_driver/` | Migrated from `gc_async_mut/gpu.spl` — local `extern fn` declarations replace `compiler.loader.cuda_ffi` import |
| `mem_tracker/` | Memory tracking utilities (NoGC-only) |

---

## Common/ Extractions

### `common/torch/` (existing)

**File:** `src/lib/common/torch/interface.spl`

**Contents:**
- `TorchBackend` trait — handle-level ops (available, create_zeros, tensor_add, etc.)
- `LayerForward` trait — `fn forward(input: i64) -> i64`
- `HasParameters` trait — `fn parameter_handles() -> [i64]`

**Used by:**
- `gc_async_mut/torch/backend.spl` — `impl TorchBackend for GcTorchOps`
- `nogc_sync_mut/torch/backend.spl` — `impl TorchBackend for NogcTorchOps`

### `common/gpu/` (new, 2026-02-22)

**File:** `src/lib/common/gpu/device.spl`

**Contents:**
- `GpuBackend` enum — `Cuda`, `Vulkan`, `None_`
- `Gpu` struct — `backend: GpuBackend`, `device_id: i32`, `is_initialized: bool`
- `impl Gpu` — `is_valid() -> bool`, `sync() -> bool`
- `gpu_cuda(device_id: i32) -> Gpu`
- `gpu_vulkan(device_id: i32) -> Gpu`
- `gpu_none() -> Gpu`

**Used by:**
- `gc_async_mut/gpu/device.spl` — was the original definition
- `nogc_sync_mut/gpu/device.spl` — imports and re-exports

---

## Import Mapping

When migrating user code from GC to NoGC, apply these import substitutions:

| GC Import | NoGC Import |
|-----------|-------------|
| `use std.torch.*` | `use std.nogc_sync_mut.torch.*` |
| `use std.gc_async_mut.torch.*` | `use std.nogc_sync_mut.torch.*` |
| `use std.cuda.*` | `use std.nogc_sync_mut.cuda.*` |
| `use std.gc_async_mut.cuda.*` | `use std.nogc_sync_mut.cuda.*` |
| `use std.gpu.*` | `use std.nogc_sync_mut.gpu.*` |
| `use std.gc_async_mut.gpu.*` | `use std.nogc_sync_mut.gpu.*` |
| `use std.gpu_runtime.*` | `use std.nogc_sync_mut.gpu_runtime.*` |
| `use std.gc_async_mut.gpu_runtime.*` | `use std.nogc_sync_mut.gpu_runtime.*` |
| `use std.gc_async_mut.pure.*` | `use std.nogc_sync_mut.pure.*` |
| `use std.gc_async_mut.torch.dyn_ffi.*` | `use std.nogc_sync_mut.torch.dyn_ffi.*` |
| `use std.gc_async_mut.gpu.*` | `use std.nogc_sync_mut.gpu_driver.*` |
| `use std.nogc_sync_mut.torch.*` | `use std.nogc_async_mut.torch.*` |
| `use std.nogc_sync_mut.cuda.*` | `use std.nogc_async_mut.cuda.*` |
| `use std.nogc_sync_mut.gpu.*` | `use std.nogc_async_mut.gpu.*` |
| `use std.nogc_sync_mut.pure.*` | `use std.nogc_async_mut.pure.*` |

**Shared types** (no import change needed):
```simple
use std.common.gpu.device.{GpuBackend, Gpu}   # same in both modes
use std.common.torch.interface.{TorchBackend}  # same in both modes
```

---

## Pattern Differences by Module

### `cuda/` migration

| Aspect | GC (`gc_async_mut`) | NoGC (`nogc_sync_mut`) |
|--------|---------------------|------------------------|
| Class fields | `handle: i64`, `owns_handle: bool` | `handle: i64` only |
| Constructor | `CudaStreamWrapper(handle: h, owns_handle: true)` | `CudaStreamWrapper(handle: h)` |
| `drop()` | `if self.owns_handle: rt_cuda_stream_destroy(self.handle)` | `rt_cuda_stream_destroy(self.handle)` |
| API surface | Identical | Identical |

### `gpu/` migration

| Aspect | GC (`gc_async_mut`) | NoGC (`nogc_sync_mut`) |
|--------|---------------------|------------------------|
| Tensor type | `TorchTensorWrapper?` from `std.torch` | `Tensor?` from `std.nogc_sync_mut.torch` |
| Stream type | `TorchStream?` from `std.torch` | `Stream?` from `std.nogc_sync_mut.torch` |
| Device types | `GpuBackend`, `Gpu` defined in `gpu/device.spl` | Imported from `std.common.gpu.device` |
| Backend detection | `use std.torch.{torch_cuda_available}` | `use std.nogc_sync_mut.torch.{cuda_available}` |

### `gpu_runtime/` migration

The key difference is elimination of the borrowed-view pattern:

```simple
# GC: creates temporary wrapper with owns_handle: false
fn gpu_tensor_is_cuda(tensor_handle: i64) -> bool:
    val t = TorchTensorWrapper(handle: tensor_handle, owns_handle: false)
    t.is_cuda()

# NoGC: direct FFI call
fn gpu_tensor_is_cuda(tensor_handle: i64) -> bool:
    rt_torch_torchtensor_is_cuda(tensor_handle)
```

All 5 functions that used the borrowed-view pattern were replaced:
- `gpu_tensor_to_cuda` — `TorchTensorWrapper.cuda()` → `rt_torch_torchtensor_cuda()`
- `gpu_tensor_is_cuda` — `TorchTensorWrapper.is_cuda()` → `rt_torch_torchtensor_is_cuda()`
- `gpu_tensor_numel` — `TorchTensorWrapper.numel()` → `rt_torch_torchtensor_numel()`
- `gpu_stream_sync` — `TorchStream.sync()` → `rt_torch_torchstream_sync()`
- `gpu_stream_query` — `TorchStream.query()` → `rt_torch_torchstream_query()`

### `pure/` migration

Pure module contains only math/ML algorithms with no FFI handles:
- No `owns_handle` fields (pure value types)
- No `drop()` methods (no resources to free)
- Migration = bulk copy + fix 6 internal cross-references

| File | Old import | New import |
|------|-----------|------------|
| `nn.spl` | `std.gc_async_mut.pure.nn_layers` | `std.nogc_sync_mut.pure.nn_layers` |
| `evaluator.spl` | `std.gc_async_mut.pure.evaluator_broadcast` | `std.nogc_sync_mut.pure.evaluator_broadcast` |
| `parser.spl` | `std.gc_async_mut.pure.parser_expr` | `std.nogc_sync_mut.pure.parser_expr` |
| `evaluator_broadcast.spl` | `std.gc_async_mut.pure.evaluator` | `std.nogc_sync_mut.pure.evaluator` |
| `nn_layers.spl` | `std.gc_async_mut.pure.nn` | `std.nogc_sync_mut.pure.nn` |
| `parser_expr.spl` | `std.gc_async_mut.pure.parser` | `std.nogc_sync_mut.pure.parser` |

---

### nogc_async_mut ML Modules (new, 2026-02-22)

`nogc_async_mut/` now contains full copies of the ML library:

| Subsystem | Files | Source |
|-----------|------:|--------|
| `pure/` | 50 | Copy from `nogc_sync_mut/pure/` with import path fix |
| `torch/` | 8 | Copy from `nogc_sync_mut/torch/` with import path fix |
| `gpu/` | 5 | Copy from `nogc_sync_mut/gpu/` with import path fix |
| `cuda/` | 3 | Copy from `nogc_sync_mut/cuda/` with import path fix |
| `ml/` | 4 | New async-specific training integration |

The `ml/` module is unique to `nogc_async_mut/` and provides:
- `async_training.spl` — `train_epoch()`, `evaluate_model()`, `train_loop()`
- `data_pipeline.spl` — `prefetch_batches()`, `shuffle_indices()`

---

## Math Block m{} for ML

`m{}` is a language-level feature — available in **all** library modes (`gc_async_mut`, `nogc_sync_mut`, `nogc_async_mut`). No import required.

```simple
# Power operator inside m{} uses ^ (outside uses **)
val loss = m{ 0.5 * (pred - target)^2 }

# Broadcast operators for vectorized math
val scaled = m{ weights .* inputs }    # element-wise multiply
val dot    = m{ a @ b }               # matrix multiply
val t      = m{ matrix' }             # transpose

# Implicit multiplication
val norm = m{ 2*x^2 + 3x + 1 }       # 3x is 3 * x
```

All `m{}` expressions produce normal values — they compose with any ML code in any library mode.

---

## Async Module Parity

### Async modules in `nogc_async_mut/` (53 files, 9,795 lines)

The entire async library lives exclusively in `nogc_async_mut/`. There are **no** async modules in `gc_async_mut/`.

| Subsystem | Files | Key Modules |
|-----------|------:|-------------|
| Core async | 10 | `async/future.spl`, `async/promise.spl`, `async/executor.spl` |
| Host runtime | 10 | `async_host/scheduler.spl`, `async_host/runtime.spl`, `async_host/joinset.spl` |
| Actors | 2 | `actors/actor.spl` (588 lines) |
| Concurrent | 7 | `concurrent/channel.spl`, `concurrent/mutex.spl`, `concurrent/collections.spl` |
| I/O | 5 | `io/event_loop.spl`, `io/tcp.spl`, `io/file.spl` |
| Root | 19 | `actor_scheduler.spl`, `actor_heap.spl`, `supervisor.spl`, `gen_server.spl`, etc. |

### gc_async_mut async status

Despite the name, `gc_async_mut/` contains **only sync code**:
- `torch/` — synchronous tensor operations and training
- `cuda/` — synchronous CUDA stream/event/memory wrappers
- `gpu/` — synchronous GPU memory management
- `gpu_runtime/` — synchronous GPU runtime utilities
- `pure/` — synchronous math/ML algorithms

CUDA streams provide hardware-level async parallelism, but all Simple wrappers are synchronous function calls.

### Future GC async modules

When GC-aware async modules are created, they should follow these patterns:
- **Per-task heap:** Each async task gets its own GC heap (`ActorHeap` with GC presets)
- **Copy-on-send:** Cross-task messaging copies data (no shared references)
- **Arena fallback:** Short-lived tasks use `HeapConfig__no_gc(size)` for zero-GC overhead

### Async import mapping (future)

When GC async modules are created:

| GC Async Import | NoGC Async Import |
|-----------------|-------------------|
| `use std.gc_async.future.*` | `use std.async.*` |
| `use std.gc_async.actor.*` | `use std.actors.*` |
| `use std.gc_async.channel.*` | `use std.concurrent.channel.*` |

---

## Cross-References

- **Async migration guide:** [`doc/design/async_migration_guide.md`](async_migration_guide.md) — GC↔NoGC patterns for async code
- **nogc_async_mut architecture:** [`doc/guide/nogc_async_mut_architecture.md`](../guide/nogc_async_mut_architecture.md) — 53-file, 9,795-line async library
- **Cross-language async patterns:** [`doc/research/async_patterns_cross_language.md`](../research/async_patterns_cross_language.md) — Rust/Go/Erlang/Swift/Kotlin/Zig/C++/Python

---

## Verification Commands

```bash
# No owns_handle in any nogc module
grep -r 'owns_handle' src/lib/nogc_sync_mut/cuda/
grep -r 'owns_handle' src/lib/nogc_sync_mut/gpu/
grep -r 'owns_handle' src/lib/nogc_sync_mut/torch/dyn_ffi.spl  # 0 matches
grep -r 'owns_handle' src/lib/nogc_sync_mut/gpu_driver/         # 0 matches

# No gc_async_mut cross-references in nogc modules
grep -r 'gc_async_mut' src/lib/nogc_sync_mut/pure/

# File counts
find src/lib/nogc_sync_mut/cuda/ -name '*.spl' | wc -l         # 3
find src/lib/nogc_sync_mut/gpu/ -name '*.spl' | wc -l           # 5
find src/lib/nogc_sync_mut/gpu_runtime/ -name '*.spl' | wc -l   # 2
find src/lib/nogc_sync_mut/pure/ -name '*.spl' | wc -l          # 50
find src/lib/nogc_sync_mut/torch/ -name '*.spl' | wc -l         # 8 (was 7, +dyn_ffi.spl)
find src/lib/nogc_sync_mut/gpu_driver/ -name '*.spl' | wc -l    # 2
find src/lib/common/gpu/ -name '*.spl' | wc -l                  # 2

# nogc_async_mut file counts
find src/lib/nogc_async_mut/pure/ -name '*.spl' | wc -l     # 50
find src/lib/nogc_async_mut/torch/ -name '*.spl' | wc -l    # 8
find src/lib/nogc_async_mut/gpu/ -name '*.spl' | wc -l      # 5
find src/lib/nogc_async_mut/cuda/ -name '*.spl' | wc -l     # 3
find src/lib/nogc_async_mut/ml/ -name '*.spl' | wc -l       # 4

# GC pattern SSpec tests
find test/unit/lib/gc_async_mut/ -name 'gc_*_spec.spl' | wc -l  # 6
```
