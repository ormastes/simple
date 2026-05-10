# scilib_port_ndarray — NDArray Task List

**Area:** `std.ndarray`  
**Target files:** `src/lib/nogc_sync_mut/ndarray/` (new dir), `src/lib/nogc_sync_mut/src/tensor.spl` (migration), `src/lib/nogc_sync_mut/src/tensor/` subtree (migration)  
**Namespace:** `use std.ndarray`  
**Phase:** v1 = NDArray core + migration; v1.1 = I/O + alias removal + fancy/boolean indexing; v2 = pure-Simple backend slot  
**Architecture lock:** Path B, OQ-A..F resolved. See `doc/05_design/scilib_port_architecture.md`.  
**Hard gate:** T-PERFSUGAR-01 (`rt_f64_array_alloc`) must be `fixed` before ANY ctor impl begins.  
**Sibling scopes — DO NOT TOUCH:**  
- `T-BLAS-*` → `src/lib/common/linalg/ffi_blas.spl`  
- `T-LAPACK-*` → `src/lib/common/linalg/ffi_lapack.spl`  
- `T-CUDA-*` → `src/runtime/scilib/{cublas,openblas,mock}_shim.c`  
- `T-MATHBLOCK-*` → `src/compiler_rust/compiler/src/codegen/*/math_block*`  
- `T-DF-*` → `src/lib/nogc_sync_mut/df/`  
- `T-ML-*` → `src/lib/gc_async_mut/ml/`  
- `T-PERFSUGAR-*` → `src/compiler_rust/` and `src/runtime/`  

All acceptance criteria must pass via `bin/simple test <spec.spl>` in interpreter mode (no `--mode=native`, no `--mode=smf`). Backend: `SIMPLE_BLAS_BACKEND=mock`. Zero `skip()`. Zero primitive types in public signatures.

---

## Dependency Graph

```
T-PERFSUGAR-01  (external gate — must be fixed first)
       │
T-NDARRAY-01 (types.spl scaffold)
       │
T-NDARRAY-02 (DType/Device re-exports)
       │
T-NDARRAY-03 (StorageBackend trait)
       │
T-NDARRAY-04 (Tensor call-site audit)
       │
T-NDARRAY-05 (Tensor→NDArray rename in tensor.spl)
       │
T-NDARRAY-06 (Tensor = NDArray alias)
       │
T-NDARRAY-07 (LibtorchBackend impl)
       │
T-NDARRAY-08 (MockBackend impl)
       │
       ├── T-NDARRAY-09 (zeros/ones/empty/full/eye)  ← T-PERFSUGAR-01 (rt_f64_array_alloc)
       │         │
       │   T-NDARRAY-10 (from_seq / array ctor)       ← T-PERFSUGAR-01
       │         │
       │   T-NDARRAY-11 (arange / linspace)            ← T-PERFSUGAR-01
       │         │
       │   T-NDARRAY-12 (PERF-SUGAR-011 measure)
       │         │
       │   T-NDARRAY-13 (PERF-SUGAR-003 workaround)
       │         │
       │   T-NDARRAY-14 (broadcasting engine)
       │         │
       │   T-NDARRAY-15 (element access + sliced views)
       │         │
       │   T-NDARRAY-16 (reshape / transpose / squeeze / flatten)
       │         │
       │   T-NDARRAY-17 (ufunc elementwise methods)
       │         │
       │   T-NDARRAY-18 (reductions: sum/mean/std/min/max/argmax)
       │         │
       │   T-NDARRAY-19 (dtype dispatch layer)
       │         │
       │   T-NDARRAY-20 (device dispatch + CublasBackend slot)
       │         │
       │   T-NDARRAY-21 (broadcast scalar ops + in-place sugar)
       │         │
       │   T-NDARRAY-22 (where<T> + gather + mask stubs)
       │         │
       │   T-NDARRAY-23 (v1 acceptance-gate spec suite)
       │
       └── T-NDARRAY-24 (v1.1: strided view) ← T-PERFSUGAR-05
           T-NDARRAY-25 (v1.1: I/O save_npy/load_npy/load_txt)
           T-NDARRAY-26 (v1.1: fancy/boolean indexing full impl)
           T-NDARRAY-27 (v1.1: Tensor alias removal)
           T-NDARRAY-28 (v2: pure-Simple backend slot)
```

---

## v1 Tasks

---

### T-NDARRAY-01 — Scaffold `src/lib/nogc_sync_mut/ndarray/types.spl`

**Effort:** S (½d)  
**Phase:** v1  
**Depends-on:** T-PERFSUGAR-01 (confirmed `fixed` status before starting)

**Description:**  
Create `src/lib/nogc_sync_mut/ndarray/` directory and stub `types.spl` containing the six typed-wrapper structs:
`Float64`, `Float32`, `Int64`, `Index`, `Shape`, `Stride`. Each is a single-field struct with no
primitive in its public accessor signature (accessors may return the typed wrapper itself or another
typed wrapper, never a raw `f64`/`i64`). Also add the `NDArray<T>` struct stub with fields `_backend`,
`_shape: [Index]`, `_strides: [Stride]`, `_dtype: DType`, `_device: Device`, `_offset: Index`
(all internal). Add `mod.spl` re-exporting the public surface.

**Acceptance:**  
- `bin/simple lint src/lib/nogc_sync_mut/ndarray/types.spl` clean.  
- No primitive type (`f64`, `i64`, `f32`, `i32`) appears in any public `fn` signature or exported `struct` field.  
- `Float64`, `Float32`, `Int64`, `Index`, `Shape`, `Stride`, `NDArray` are exported from `mod.spl`.  

---

### T-NDARRAY-02 — Re-export `DType` and `Device` from `tensor.spl`

**Effort:** S (½d)  
**Phase:** v1  
**Depends-on:** T-NDARRAY-01

**Description:**  
Add `use` re-exports of `DType` and `Device` from `src/lib/nogc_sync_mut/src/tensor.spl` into
`src/lib/nogc_sync_mut/ndarray/types.spl` and into `mod.spl`. Do NOT redefine either enum — they
stay in `tensor.spl` unchanged. The `NDArray<T>` struct fields `_dtype: DType` and `_device: Device`
reference the re-exported types. Verify that `use std.ndarray` exposes `DType` and `Device`
without requiring a direct `use std.tensor` import.

**Acceptance:**  
- A test file containing `use std.ndarray` and then `let d: DType = DType.F64` compiles and runs in interpreter mode without error.  
- No `enum DType` or `enum Device` definition appears anywhere under `src/lib/nogc_sync_mut/ndarray/`.  
- `bin/simple lint src/lib/nogc_sync_mut/ndarray/` clean.  

---

### T-NDARRAY-03 — Define `StorageBackend` trait (no inheritance, composition only)

**Effort:** M (1d)  
**Phase:** v1  
**Depends-on:** T-NDARRAY-02

**Description:**  
Create `src/lib/nogc_sync_mut/ndarray/backend.spl` defining the `StorageBackend` trait with methods:
`alloc(shape: Shape, dtype: DType, device: Device) -> Result<StorageHandle, NdarrayError>`,
`free(handle: StorageHandle)`, `data_ptr(handle: StorageHandle) -> Index` (raw pointer as `Index`),
`copy_to_host(handle: StorageHandle, dst: [Float64])`, `copy_from_host(handle: StorageHandle, src: [Float64])`,
`backend_name() -> text`. Define `StorageHandle` as an opaque `struct StorageHandle { _id: i64 }`
(primitive `i64` kept internal, never in public API). Define `NdarrayError` enum with variants
`AllocFailed(Shape)`, `DtypeMismatch(DType, DType)`, `ShapeMismatch(Shape, Shape)`,
`BackendUnavailable(text)`, `IndexOutOfBounds(Index, Shape)`. No inheritance anywhere.

**Acceptance:**  
- `bin/simple lint src/lib/nogc_sync_mut/ndarray/backend.spl` clean.  
- `StorageBackend` trait has no `class Parent` in its definition.  
- `NdarrayError` and `StorageHandle` exported from `mod.spl`.  
- A stub type `struct NoopBackend` implementing `StorageBackend` with trivial bodies compiles without error.  

---

### T-NDARRAY-04 — Audit existing `Tensor<T,N>` call sites before migration

**Effort:** M (1d)  
**Phase:** v1  
**Depends-on:** T-NDARRAY-03

**Description:**  
Grep all `.spl` files under `src/` for uses of `Tensor<`, `tensor.zeros`, `tensor.ones`,
`tensor.from_`, `.ndim()`, `Tensor<f64, 2>`, `Tensor<f64, 1>`, `Tensor<T, N>`, `_handle: i64`
(in tensor context). Produce a migration inventory: file path, line number, usage pattern,
whether it uses the rank `N` parameter or `ndim()` (dynamic rank body). Identify any call sites
that rely on the static-rank `N` in a type position (i.e., `Tensor<T, 2>` as a type annotation).
These must be migrated to `Matrix<T>` (linalg scope) or `NDArray<T>` with a `rank_check` guard.
Record findings as comments in a scratch note — do NOT edit source files in this task.

**Acceptance:**  
- Inventory document (in-task comment or tracking note) lists every call site with rank-N usage flagged.  
- No source files are modified in this task.  
- Count of files using `Tensor<` reported and confirmed < 50 (if > 50, escalate before proceeding).  

---

### T-NDARRAY-05 — Rename `Tensor<T,N>` → `NDArray<T>` (dynamic rank) in `tensor.spl`

**Effort:** L (2d)  
**Phase:** v1  
**Depends-on:** T-NDARRAY-04

**Description:**  
In `src/lib/nogc_sync_mut/src/tensor.spl` and its subtree (`tensor/factory.spl`, `tensor/ops/`):
(1) Rename struct `Tensor<T, N>` to `NDArray<T>` — drop the `N` rank parameter.
(2) Replace the static `fn ndim() -> i64 { N }` with a dynamic `fn ndim(self) -> Index { Index(self._shape.len()) }`.
(3) Change `_shape: [i64]` → `_shape: [Index]`; update all internal shape accesses.
(4) Remove the `_handle: i64` comment about "PyTorch tensor handle"; rename field to `_backend_handle: i64` (still internal).
(5) Update all factory methods in `tensor/factory.spl` to return `NDArray<T>` and accept `Shape` instead of `[i64]`.
(6) Update any internal callers within the tensor subtree. Do NOT update callers outside `nogc_sync_mut/src/tensor*/` — that is T-NDARRAY-04 scope.

**Acceptance:**  
- `bin/simple lint src/lib/nogc_sync_mut/src/tensor.spl` and `src/lib/nogc_sync_mut/src/tensor/` clean.  
- No remaining `Tensor<T, N>` struct definition in the renamed files.  
- `NDArray<T>` struct has `_shape: [Index]`, no raw `[i64]` shape field.  
- `ndim()` returns `Index`, not `i64`.  
- All factory methods accept `Shape`, not `[i64]`.  

---

### T-NDARRAY-06 — Add `Tensor = NDArray` backward alias with deprecation annotation

**Effort:** S (½d)  
**Phase:** v1  
**Depends-on:** T-NDARRAY-05

**Description:**  
In `src/lib/nogc_sync_mut/src/tensor.spl`, after the `NDArray<T>` struct definition, add:
`#[deprecated(since="v1.1", note="Use NDArray<T> directly")]`
`type Tensor<T> = NDArray<T>`
Also add re-export of this alias from `mod.spl` so that code doing `use std.ndarray; let t: Tensor<Float64>` still compiles with a deprecation warning. Verify the lint emits a deprecation warning for any code using `Tensor<T>` (not an error — callers must have one release to migrate).

**Acceptance:**  
- `type Tensor<T> = NDArray<T>` present in `tensor.spl`.  
- `#[deprecated(since="v1.1")]` annotation present on the alias.  
- A test file using `Tensor<Float64>` compiles but emits a deprecation lint warning.  
- A test file using `NDArray<Float64>` compiles with no warning.  

---

### T-NDARRAY-07 — Wrap existing libtorch internals as `LibtorchBackend` impl

**Effort:** M (1d)  
**Phase:** v1  
**Depends-on:** T-NDARRAY-06

**Description:**  
Create `src/lib/nogc_sync_mut/ndarray/libtorch_backend.spl` implementing `StorageBackend` trait for
the existing libtorch FFI. `alloc` calls the existing `rt_tensor_create` (or equivalent) using
the dtype/device mapping from `DType`/`Device`. `data_ptr` returns the raw buffer pointer from
`rt_tensor_data_ptr`. `copy_to_host` / `copy_from_host` call existing `rt_tensor_copy_*` externs.
`backend_name()` returns `"libtorch"`. The existing `_backend_handle: i64` in `NDArray<T>` is this
backend's storage handle. No new FFI symbols are introduced — this task only wraps existing ones
behind the trait interface.

**Acceptance:**  
- `LibtorchBackend` implements all methods of `StorageBackend` trait without `pass_todo`.  
- `bin/simple lint src/lib/nogc_sync_mut/ndarray/libtorch_backend.spl` clean.  
- A smoke spec: create `NDArray<Float64>` via `LibtorchBackend`, call `data_ptr`, verify non-zero handle. Passes `bin/simple test` in interpreter mode.  

---

### T-NDARRAY-08 — Implement `MockBackend` for interpreter-mode specs

**Effort:** M (1d)  
**Phase:** v1  
**Depends-on:** T-NDARRAY-07

**Description:**  
Create `src/lib/nogc_sync_mut/ndarray/mock_backend.spl` implementing `StorageBackend` with:
- `alloc`: allocates a host-side `[Float64]` buffer of `shape.numel()` elements using
  `rt_f64_array_alloc` (T-PERFSUGAR-01 gate); stores buffer as i64 handle via
  `rt_array_as_ptr`; records dtype and shape in a module-level table keyed by handle id.
- `free`: frees host buffer.
- `data_ptr`: returns stored pointer.
- `copy_to_host` / `copy_from_host`: memcpy via extern.
- `backend_name()`: returns `"mock"`.

`MockBackend` is selected when `SIMPLE_BLAS_BACKEND=mock` (read at `NDArray` creation time via
`rt_getenv`). The test harness sets this env var by default for all `ndarray/` specs.

**Acceptance:**  
- `depends-on: T-PERFSUGAR-01 (rt_f64_array_alloc)` — `rt_f64_array_alloc` must be in the runtime before this task is started.  
- `MockBackend` implements all `StorageBackend` methods without `pass_todo`.  
- `SIMPLE_BLAS_BACKEND=mock bin/simple test src/lib/nogc_sync_mut/ndarray/mock_backend_spec.spl` passes interpreter mode; zero `skip()`.  
- No `rt_blas_*` or `rt_lapack_*` symbols are called from `MockBackend`.  

---

### T-NDARRAY-09 — Factory: `zeros`, `ones`, `empty`, `full`, `eye`

**Effort:** M (1d)  
**Phase:** v1  
**Depends-on:** T-NDARRAY-08  
**Cross-area:** depends-on: T-PERFSUGAR-01 (rt_f64_array_alloc, rt_f32_array_alloc, rt_i64_array_alloc)

**Description:**  
In `src/lib/nogc_sync_mut/ndarray/factory.spl`, implement five construction free functions:
- `zeros<T>(shape: Shape, device: Device) -> NDArray<T>`: allocates via active backend, zero-fills.
- `ones<T>(shape: Shape, device: Device) -> NDArray<T>`: allocates, fills with typed `T(1)`.
- `empty<T>(shape: Shape, device: Device) -> NDArray<T>`: allocates without initialization (uninitialized memory; document this clearly).
- `full<T>(shape: Shape, fill: T, device: Device) -> NDArray<T>`: allocates, broadcast-fills.
- `eye(n: Index, device: Device) -> NDArray<Float64>`: NxN identity matrix.

All parameters use typed wrappers (`Shape`, `Device`, `Index`), never primitives. The critical path
for `zeros` and `ones` is the bulk-alloc extern: call `rt_f64_array_alloc(numel)` (for F64 case),
not a `push` loop. Include dtype dispatch in each function: F64 → `rt_f64_array_alloc`, F32 →
`rt_f32_array_alloc`, I64 → `rt_i64_array_alloc`.

**Acceptance:**  
- `NDArray.zeros(Shape(1024, 1024), Device.CPU)` completes in interpreter mode in under 5 s (wall clock). If it exceeds 5 s, file a new PERF-SUGAR entry and do NOT merge.  
- `NDArray.ones(Shape(4, 4), Device.CPU)` returns array where all elements equal `Float64(1.0)`.  
- `NDArray.eye(Index(3), Device.CPU)` returns 3x3 identity; diagonal elements `Float64(1.0)`, off-diagonal `Float64(0.0)`.  
- Zero primitive types in any public signature.  
- `bin/simple test src/lib/nogc_sync_mut/ndarray/factory_spec.spl` passes; zero `skip()`.  

---

### T-NDARRAY-10 — Factory: `from_seq` (array ctor from sequence)

**Effort:** M (1d)  
**Phase:** v1  
**Depends-on:** T-NDARRAY-09  
**Cross-area:** depends-on: T-PERFSUGAR-01 (rt_f64_array_alloc)

**Description:**  
Implement `from_seq<T>(data: [T], shape: Shape, device: Device) -> Result<NDArray<T>, NdarrayError>`.
The `shape.numel()` must equal `data.len()`; return `NdarrayError.ShapeMismatch` if not.
Copy elements from `data` into backend buffer using `copy_from_host`. This is the Simple equivalent
of `np.array(obj)`. Also implement a helper `from_scalar<T>(val: T, device: Device) -> NDArray<T>`
returning a rank-0 array (shape `Shape()`).
Document: `from_seq` always copies (no zero-copy path in v1).

**Acceptance:**  
- `NDArray.from_seq([Float64(1.0), Float64(2.0), Float64(3.0)], Shape(3), Device.CPU)` succeeds.  
- `NDArray.from_seq([Float64(1.0), Float64(2.0)], Shape(3), Device.CPU)` returns `Err(ShapeMismatch(...))`.  
- `NDArray.from_scalar(Float64(3.14), Device.CPU)` returns rank-0 array; `ndim()` returns `Index(0)`.  
- `bin/simple test src/lib/nogc_sync_mut/ndarray/from_seq_spec.spl` passes; zero `skip()`.  

---

### T-NDARRAY-11 — Factory: `arange` and `linspace`

**Effort:** S (½d)  
**Phase:** v1  
**Depends-on:** T-NDARRAY-10  
**Cross-area:** depends-on: T-PERFSUGAR-01 (rt_f64_array_alloc)

**Description:**  
Implement:
- `arange(start: Float64, stop: Float64, step: Float64, device: Device) -> NDArray<Float64>`:
  length = `ceil((stop - start) / step)`. Allocate via `rt_f64_array_alloc(len)`. Fill with
  `start + i * step` for `i in 0..len`.
- `linspace(start: Float64, stop: Float64, num: Index, device: Device) -> NDArray<Float64>`:
  length = `num`. Step = `(stop - start) / (num - 1)`. Fill closed-interval.

Both are free functions in `factory.spl`, not methods on `NDArray`. They shadow `tensor/factory.spl`
equivalents — verify no duplicate symbol is exported from `mod.spl`.

**Acceptance:**  
- `arange(Float64(0.0), Float64(1.0), Float64(0.25), Device.CPU)` yields 4-element array `[0.0, 0.25, 0.5, 0.75]`.  
- `linspace(Float64(0.0), Float64(1.0), Index(5), Device.CPU)` yields `[0.0, 0.25, 0.5, 0.75, 1.0]`.  
- `bin/simple test src/lib/nogc_sync_mut/ndarray/arange_spec.spl` passes; zero `skip()`.  

---

### T-NDARRAY-12 — Measure PERF-SUGAR-011 (Float64 wrapper allocation cost at scale)

**Effort:** S (½d)  
**Phase:** v1  
**Depends-on:** T-NDARRAY-09

**Description:**  
Write a benchmark spec `ndarray/perf_wrapper_alloc_spec.spl` that:
(1) Constructs `NDArray.from_seq` with a literal list of 10,000 `Float64(x)` elements.
(2) Times wall-clock in interpreter mode.
(3) Compares to an equivalent `[u8]` bulk-alloc to establish a baseline.
If construction exceeds 10 s for 10,000 elements, update PERF-SUGAR-011 status to `observed` and
document the measured cost. If < 2 s, mark as `anticipated — within acceptable range`. Do NOT
implement the newtype optimization here — that is compiler scope (T-PERFSUGAR-11).

**Acceptance:**  
- Measurement result written to the PERF-SUGAR-011 entry in `doc/08_tracking/feature_request/scilib_perf_sugar.md` (update Status field and Current-cost field).  
- If cost > 10 s: entry promoted to `observed`, escalation note added, impl paused for PERF-SUGAR-011 resolution.  
- If cost acceptable: entry remains `anticipated` with note.  

---

### T-NDARRAY-13 — PERF-SUGAR-003 workaround: typed specializations alongside generic facade

**Effort:** S (½d)  
**Phase:** v1  
**Depends-on:** T-NDARRAY-11  
**Cross-area:** depends-on: T-PERFSUGAR-03 (generic erased dispatch — workaround plan, not fix)

**Description:**  
For methods on `NDArray<T>` that are performance-critical in interpreter mode (element access,
elementwise add, scalar multiply), provide concrete non-generic specializations alongside the generic
facade. Pattern: implement `fn _add_f64(self, other: NDArray<Float64>) -> NDArray<Float64>` and
`fn _add_i64(self, other: NDArray<Int64>) -> NDArray<Int64>`; the public `fn add<T>` dispatches
via `match self._dtype { DType.F64 => self._add_f64(...), ... }`. Document this as a workaround
for PERF-SUGAR-003 (no interpreter-side monomorphization). Update PERF-SUGAR-003 status to
`observed` with the workaround documented. Do NOT attempt to fix the compiler here.

**Acceptance:**  
- PERF-SUGAR-003 entry updated: Status = `observed`, workaround = "dtype-dispatch to typed
  specializations inside `NDArray` methods; see `ndarray/ops.spl`".  
- The public `add` method signature remains generic (`add<T>`); no primitives in public API.  
- `bin/simple lint src/lib/nogc_sync_mut/ndarray/ops.spl` clean.  

---

### T-NDARRAY-14 — Broadcasting engine: `broadcast_shapes` + `broadcast_expand`

**Effort:** L (2d)  
**Phase:** v1  
**Depends-on:** T-NDARRAY-13

**Description:**  
Implement the broadcasting algorithm (arch §4) in `src/lib/nogc_sync_mut/ndarray/broadcast.spl`:
- `broadcast_shapes(a: Shape, b: Shape) -> Result<Shape, NdarrayError>`:
  Right-align shapes (left-pad shorter with `Index(1)`). For each aligned pair `(da, db)`:
  if `da == db`, keep; if `da == Index(1)`, use `db`; if `db == Index(1)`, use `da`; else
  return `NdarrayError.ShapeMismatch(a, b)`.
- `broadcast_expand(arr: NDArray<Float64>, target: Shape) -> NDArray<Float64>`:
  Physically expand the array to `target` shape by copying along broadcast dimensions.
  This is the O(n) materialization step called before dispatching to the backend.
  For v1 this is a Simple-level loop using `rt_f64_array_alloc`; NOT deferred to extern yet
  (PERF-SUGAR-009 tracks the extern optimization).

This engine is the gating substrate for all ufunc ops (T-NDARRAY-17, T-NDARRAY-21).

**Acceptance:**  
- `broadcast_shapes(Shape(3, 1), Shape(1, 4))` returns `Ok(Shape(3, 4))`.  
- `broadcast_shapes(Shape(3, 2), Shape(1, 4))` returns `Err(ShapeMismatch(...))`.  
- `broadcast_shapes(Shape(4), Shape(3, 4))` returns `Ok(Shape(3, 4))` (left-pad).  
- `broadcast_expand` on a `(3,1)` array with target `(3,4)` returns correct 3x4 values.  
- `bin/simple test src/lib/nogc_sync_mut/ndarray/broadcast_spec.spl` passes; zero `skip()`.  

---

### T-NDARRAY-15 — Element access and sliced views: `ndarray[i,j]` and `ndarray[lo..hi, ..]`

**Effort:** L (2d)  
**Phase:** v1  
**Depends-on:** T-NDARRAY-14

**Description:**  
In `src/lib/nogc_sync_mut/ndarray/index.spl`, implement:
- `fn get(self, indices: [Index]) -> Result<T, NdarrayError>`: multi-axis element access.
  Converts multi-index to flat offset via stride arithmetic: `offset = sum(indices[i] * strides[i])`.
  Calls `backend.data_ptr` + pointer arithmetic to read element.
- `fn slice(self, ranges: [SliceRange]) -> NDArray<T>`: returns a non-owning view.
  `SliceRange` is `struct SliceRange { start: Index, stop: Index, step: Index }`.
  The view shares `_backend`, updates `_offset`, `_shape`, `_strides`. No copy.
  For v1, `step` must be `Index(1)` (strided views with `step != 1` are v1.1 via T-NDARRAY-24).
  A `SliceRange` with `step != 1` returns `NdarrayError.BackendUnavailable("strided_step_v1.1")`.
- `fn set(self, indices: [Index], val: T) -> Result<Unit, NdarrayError>`: element write.

Note: subscript syntax `arr[i, j]` is handled by the compiler desugaring to `arr.get([i, j])`;
this task implements the method, not the compiler syntax.

**Acceptance:**  
- `arr.get([Index(0), Index(1)])` on a 2D array returns correct element.  
- `arr.slice([SliceRange(Index(1), Index(3), Index(1)), full_range])` returns a view with shape `(2, ncols)`; no copy occurs (verify by checking no second `alloc` call in MockBackend).  
- `arr.get([Index(99)])` on a 1D array of length 5 returns `Err(IndexOutOfBounds(...))`.  
- `bin/simple test src/lib/nogc_sync_mut/ndarray/index_spec.spl` passes; zero `skip()`.  

---

### T-NDARRAY-16 — Shape manipulation: `reshape`, `transpose`, `squeeze`, `flatten`

**Effort:** M (1d)  
**Phase:** v1  
**Depends-on:** T-NDARRAY-15

**Description:**  
In `src/lib/nogc_sync_mut/ndarray/ops.spl`, implement as methods on `NDArray<T>`:
- `reshape(self, new_shape: Shape) -> Result<NDArray<T>, NdarrayError>`: returns a view (no copy)
  if the array is contiguous; returns `Err(ShapeMismatch)` if `new_shape.numel() != self.numel()`.
  Recomputes row-major strides from `new_shape`.
- `transpose(self) -> NDArray<T>`: reverses `_shape` and `_strides` arrays. O(1) view, no copy.
  For rank > 2, reverses all axes. Matches numpy `a.T` semantics.
- `squeeze(self) -> NDArray<T>`: removes all size-1 axes. Returns view. O(1).
- `unsqueeze(self, axis: Index) -> NDArray<T>`: inserts a size-1 axis at `axis`. Returns view.
- `flatten(self) -> NDArray<T>`: returns contiguous rank-1 copy (always copies).
- `contiguous(self) -> NDArray<T>`: if not contiguous, returns a contiguous copy; otherwise returns self.

**Acceptance:**  
- `NDArray.zeros(Shape(2,3), Device.CPU).reshape(Shape(6))` returns rank-1 array; same elements.  
- `NDArray.zeros(Shape(3,4), Device.CPU).transpose()` returns shape `(4,3)`; `ndim()` = `Index(2)`.  
- `reshape` to wrong numel returns `Err`.  
- `squeeze` on `Shape(1,3,1)` returns `Shape(3)`.  
- `bin/simple test src/lib/nogc_sync_mut/ndarray/reshape_spec.spl` passes; zero `skip()`.  

---

### T-NDARRAY-17 — Ufunc elementwise methods: `add`, `sub`, `mul`, `div`, `exp`, `log`, `sin`, `cos`, `sqrt`

**Effort:** L (2d)  
**Phase:** v1  
**Depends-on:** T-NDARRAY-16

**Description:**  
In `src/lib/nogc_sync_mut/ndarray/ops.spl`, implement elementwise methods on `NDArray<T>`:
- Binary: `add`, `sub`, `mul`, `div` — each calls `broadcast_shapes` first, then `broadcast_expand`
  on the smaller operand, then dispatches to the dtype-specialized loop (T-NDARRAY-13 pattern).
  In v1 the inner loop is a Simple `for i in 0..numel` with element read/write; the `rt_ndarray_broadcast_add`
  extern optimization is tracked by PERF-SUGAR-009 (not implemented here).
- Unary: `exp`, `log`, `sin`, `cos`, `sqrt` — applied element-wise in Simple loop. These names
  are methods on `NDArray<T>`, never free functions, to avoid shadowing `std.math` scalar helpers
  (naming harmony rule from arch §5 and `04_naming_harmony` §2.3).
- All return a new `NDArray<T>` (copy, not in-place). In-place sugar (`+=`, `*=`) is T-NDARRAY-21.

**Acceptance:**  
- `a.add(b)` where `a` has shape `(3,1)` and `b` has shape `(1,4)`: result shape `(3,4)`.  
- `a.mul(b)` with incompatible shapes `(3,2)` + `(1,4)`: returns `Err(ShapeMismatch)`.  
- `NDArray.ones(Shape(3), Device.CPU).exp()` returns array of `e ≈ 2.718`; all elements within `Float64(0.001)` of `e`.  
- Methods `exp`, `log`, `sin`, `cos`, `sqrt` are NOT visible as free functions at `std.ndarray` scope.  
- `bin/simple test src/lib/nogc_sync_mut/ndarray/ufunc_spec.spl` passes; zero `skip()`.  

---

### T-NDARRAY-18 — Reductions: `sum`, `mean`, `std`, `min`, `max`, `argmax`, `argsort` (stub)

**Effort:** M (1d)  
**Phase:** v1  
**Depends-on:** T-NDARRAY-17

**Description:**  
Implement reduction methods on `NDArray<T>` in `ops.spl`:
- `sum(self, axis: Option<Index>) -> NDArray<Float64>`: full or axis reduction.
- `mean(self, axis: Option<Index>) -> NDArray<Float64>`: full or axis.
- `std(self, axis: Option<Index>, ddof: Index) -> NDArray<Float64>`: standard deviation.
- `min(self, axis: Option<Index>) -> NDArray<T>`: element or axis min.
- `max(self, axis: Option<Index>) -> NDArray<T>`: element or axis max.
- `argmax(self, axis: Option<Index>) -> NDArray<Index>`: returns `NDArray<Index>`.

All are methods — never free functions (naming harmony rule). `axis: Option<Index>` uses
typed `Index` wrapper not raw `i64`. For `axis = Option.None`, reduce over all elements.
`argsort` returns `Err(NdarrayError.BackendUnavailable("argsort_v1.1"))` in v1 (stub body with
TODO comment — do not use `skip()` or convert to NOTE; leave as concrete stub with error return).

**Acceptance:**  
- `NDArray.ones(Shape(3, 4), Device.CPU).sum(Option.None)` returns scalar-equiv `Float64(12.0)`.  
- `NDArray.from_seq([Float64(1.0), Float64(2.0), Float64(3.0)], Shape(3), Device.CPU).mean(Option.None)` returns `Float64(2.0)`.  
- `argmax` returns `NDArray<Index>`, not `NDArray<i64>`.  
- `argsort` returns `Err(...)` (not panics, not `skip()`).  
- `bin/simple test src/lib/nogc_sync_mut/ndarray/reduction_spec.spl` passes; zero `skip()`.  

---

### T-NDARRAY-19 — DType dispatch layer: route ops by `_dtype` field

**Effort:** S (½d)  
**Phase:** v1  
**Depends-on:** T-NDARRAY-18

**Description:**  
Centralise the dtype dispatch pattern established in T-NDARRAY-13 into a `dtype_dispatch.spl` helper
in `ndarray/`. Provide a macro-like pattern (or simple `match` helper struct) so that each operation
that needs dtype dispatch can call `dispatch_dtype(self._dtype, f64_fn, f32_fn, i64_fn)` without
duplicating the `match` in every method. For dtypes not supported by a given operation
(e.g., integer arrays through `exp`), the dispatcher returns `NdarrayError.DtypeMismatch(got, expected)`.
Document the mapping:
- `DType.F64` → `rt_f64_*` externs
- `DType.F32` → `rt_f32_*` externs
- `DType.I64`, `DType.I32` → pure-Simple loops (no BLAS)
- All others → `Err(DtypeMismatch)` for linalg ops; allowed for element-wise.

**Acceptance:**  
- Calling `.exp()` on an `NDArray<Int64>` returns `Err(DtypeMismatch(DType.I64, DType.F64))`, not a panic.  
- No method in `ops.spl` has a hand-written `match self._dtype { ... }` block — all use the dispatch helper.  
- `bin/simple lint src/lib/nogc_sync_mut/ndarray/` clean after adding `dtype_dispatch.spl`.  

---

### T-NDARRAY-20 — Device dispatch: CPU vs CUDA routing + `CublasBackend` slot

**Effort:** S (½d)  
**Phase:** v1  
**Depends-on:** T-NDARRAY-19  
**Cross-area:** depends-on: T-CUDA-01 (CublasBackend — implemented by cuda_fortran agent, slot reserved here)

**Description:**  
In `backend.spl`, implement `BackendRegistry`: a module-level store that maps `Device` to a
`StorageBackend` impl. At `NDArray` creation time, the registry selects the backend:
- `Device.CPU` → `LibtorchBackend` (or `MockBackend` when `SIMPLE_BLAS_BACKEND=mock`).
- `Device.CUDA(_)` → `CublasBackend` (registered by T-CUDA-01; in v1 placeholder returns
  `Err(BackendUnavailable("CublasBackend not registered"))` if not present).

`BackendRegistry.register(device_class: text, backend: StorageBackend)` allows the CUDA agent
to inject `CublasBackend` at runtime without modifying ndarray source. This follows the
`libspl_torch` injection pattern referenced in arch §6.

**Acceptance:**  
- `BackendRegistry.register("mock", MockBackend)` compiles.  
- `NDArray.zeros(Shape(4), Device.CPU)` with no CUDA backend registered succeeds.  
- `NDArray.zeros(Shape(4), Device.CUDA(Index(0)))` with no CUDA backend registered returns
  `Err(BackendUnavailable("CublasBackend not registered"))`, not a panic.  
- `bin/simple test src/lib/nogc_sync_mut/ndarray/backend_registry_spec.spl` passes; zero `skip()`.  

---

### T-NDARRAY-21 — Broadcast scalar ops and in-place mutation sugar

**Effort:** M (1d)  
**Phase:** v1  
**Depends-on:** T-NDARRAY-20

**Description:**  
Implement:
- `add_scalar(self, rhs: T) -> NDArray<T>`: broadcast `rhs` across all elements. Uses dtype dispatch.
- `mul_scalar(self, rhs: T) -> NDArray<T>`: same pattern.
- `sub_scalar(self, rhs: T) -> NDArray<T>`.
- `div_scalar(self, rhs: T) -> NDArray<T>`.
- `iadd(self, rhs: NDArray<T>) -> Unit`: in-place add; modifies `self` via `backend.data_ptr`.
- `imul_scalar(self, rhs: T) -> Unit`: in-place scalar multiply.

The `add_scalar` / `mul_scalar` methods are the v1 surface for PERF-SUGAR-009's scalar broadcast.
For `iadd`, document that PERF-SUGAR-010 tracks the `+=` augmented-assign sugar that would
desugar to `iadd` automatically. For now callers write `arr.iadd(other)` explicitly.

**Acceptance:**  
- `NDArray.ones(Shape(3), Device.CPU).add_scalar(Float64(2.0))` returns `[3.0, 3.0, 3.0]`.  
- `arr.iadd(other)` modifies `arr` in-place; no new allocation occurs (verify MockBackend alloc count).  
- PERF-SUGAR-009 updated to `observed` with the scalar broadcast workaround noted.  
- `bin/simple test src/lib/nogc_sync_mut/ndarray/scalar_ops_spec.spl` passes; zero `skip()`.  

---

### T-NDARRAY-22 — Fancy/boolean indexing stubs: `gather`, `mask`, `where<T>`

**Effort:** S (½d)  
**Phase:** v1  
**Depends-on:** T-NDARRAY-21

**Description:**  
Stub three hard indexing operations as explicit error returns (not `skip()`, not TODO→NOTE):
- `gather(self, indices: NDArray<Index>) -> Result<NDArray<T>, NdarrayError>`: returns
  `Err(BackendUnavailable("gather_v1.1"))`.
- `mask(self, mask_arr: NDArray<Bool>) -> Result<NDArray<T>, NdarrayError>`: returns
  `Err(BackendUnavailable("mask_v1.1"))`.
- `where_select<T>(cond: NDArray<Bool>, x: NDArray<T>, y: NDArray<T>) -> Result<NDArray<T>, NdarrayError>`:
  returns `Err(BackendUnavailable("where_v1.1"))`.

These stubs ensure callers get a clear error rather than a panic or silent wrong result. Full
implementation is T-NDARRAY-26 (v1.1). Having the stubs means v1.1 spec files can be written
against a stable interface without waiting for impl.

**Acceptance:**  
- All three functions present in `index.spl` with correct signatures (no primitives).  
- Each returns `Err(BackendUnavailable(...))` when called; does not panic.  
- `bin/simple lint` clean.  
- Spec file for v1.1 stubs passes with the expected `Err` results as assertions.  

---

### T-NDARRAY-23 — v1 acceptance-gate spec suite

**Effort:** M (1d)  
**Phase:** v1  
**Depends-on:** T-NDARRAY-22

**Description:**  
Write the comprehensive v1 gate spec `src/lib/nogc_sync_mut/ndarray/ndarray_v1_gate_spec.spl`
covering all items listed in arch §12 (v1 → v1.1 gates) relevant to ndarray:
- `NDArray.zeros` shape/dtype/device round-trip
- `NDArray.ones` broadcast-add verification
- `from_seq` copy semantics
- `linspace` endpoint correctness
- `broadcast_shapes` correct for 4 shape combinations (match/left-pad/expand/error)
- `slice` non-owning view (shape correct, no alloc)
- `reshape` + `transpose` strides correct
- `squeeze` size-1 axis removal
- `sum(None)` and `mean(None)` numeric correctness
- `add_scalar` elementwise
- `iadd` in-place (no new alloc)
- `where_select` returns `Err` (stub confirmed)
- Alias `Tensor<Float64>` compiles with deprecation warning (not error)
- `DType`/`Device` accessible via `use std.ndarray` without `use std.tensor`
- No primitive types in any signature (lint check embedded in spec)

All assertions use concrete expected values; zero `skip()`.

**Acceptance:**  
- `SIMPLE_BLAS_BACKEND=mock bin/simple test src/lib/nogc_sync_mut/ndarray/ndarray_v1_gate_spec.spl` passes in interpreter mode.  
- All 15+ `it` blocks green; zero `skip()`.  
- Arch §12 v1 → v1.1 gate checklist items for ndarray can be checked off after this task.  

---

## v1.1 Tasks

---

### T-NDARRAY-24 — Strided views: step != 1 slices and column slices

**Effort:** L (2d)  
**Phase:** v1.1  
**Depends-on:** T-NDARRAY-23  
**Cross-area:** depends-on: T-PERFSUGAR-05 (StridedView extern — must be fixed before this task)

**Description:**  
Extend `index.spl` to support `SliceRange.step != Index(1)`. Implement `StridedView<T>` as a
view struct backed by `(ptr: Index, len: Index, stride: Index)`. Subscript `view.get(i)` lowers
to `ptr + i * stride`. Column slice `arr.slice([full_range, SliceRange.at(j)])` returns a
`StridedView<T>` with stride = row stride. This is the O(1) path required for DataFrame column
operations in T-DF-*. Remove the `Err(BackendUnavailable("strided_step_v1.1"))` guard added in
T-NDARRAY-15; replace with the real impl.

**Acceptance:**  
- `arr.slice([..., SliceRange(Index(0), Index(n), Index(2))])` returns every-other-row view with correct shape.  
- Column slice `arr.slice([full, SliceRange.at(Index(1))])` returns strided view; no copy; shape `(nrows, 1)`.  
- `PERF-SUGAR-005` status updated to `fixed` in tracking file.  
- `bin/simple test src/lib/nogc_sync_mut/ndarray/strided_view_spec.spl` passes; zero `skip()`.  

---

### T-NDARRAY-25 — I/O: `save_npy`, `load_npy`, `load_txt`

**Effort:** M (1d)  
**Phase:** v1.1  
**Depends-on:** T-NDARRAY-24

**Description:**  
In `src/lib/nogc_sync_mut/ndarray/io.spl`:
- `save_npy(arr: NDArray<Float64>, path: text) -> Result<Unit, IoError>`: write `.npy` v1.0 header
  (magic `\x93NUMPY`, version 1.0, shape/dtype header dict, C-order data). Delegates byte I/O to
  `std.nogc_sync_mut.io`.
- `load_npy(path: text) -> Result<NDArray<Float64>, NdarrayError>`: parse `.npy` header, allocate
  via `rt_f64_array_alloc`, read data.
- `load_txt(path: text, sep: text, dtype: DType) -> Result<NDArray<Float64>, NdarrayError>`:
  parse delimited text, infer shape from row count + column count; use `std.common.csv` for
  line tokenization.

**Acceptance:**  
- `save_npy` + `load_npy` round-trip: loaded array equals saved array element-wise.  
- `load_txt` on a 3-row, 2-col tab-separated file returns shape `(3, 2)`.  
- `bin/simple test src/lib/nogc_sync_mut/ndarray/io_spec.spl` passes; zero `skip()`.  

---

### T-NDARRAY-26 — Fancy/boolean indexing full impl: `gather`, `mask`, `where<T>`

**Effort:** L (2d)  
**Phase:** v1.1  
**Depends-on:** T-NDARRAY-24

**Description:**  
Replace the stubs from T-NDARRAY-22 with real implementations:
- `gather(self, indices: NDArray<Index>) -> Result<NDArray<T>, NdarrayError>`: element gather
  from index array. Result shape = `indices.shape`. Uses dtype dispatch.
- `mask(self, mask_arr: NDArray<Bool>) -> Result<NDArray<T>, NdarrayError>`: boolean mask filter.
  Result is a rank-1 array of matching elements (variable length). Requires a count pass then
  alloc via `rt_f64_array_alloc(count)`.
- `where_select<T>(cond: NDArray<Bool>, x: NDArray<T>, y: NDArray<T>) -> Result<NDArray<T>, NdarrayError>`:
  element-wise conditional select; `cond`, `x`, `y` must be broadcast-compatible.

**Acceptance:**  
- `gather` on `[10, 20, 30]` with indices `[2, 0]` returns `[30, 10]`.  
- `mask` on `[1, 2, 3, 4]` with mask `[true, false, true, false]` returns `[1, 3]`.  
- `where_select` with scalar condition arrays broadcasts correctly.  
- `bin/simple test src/lib/nogc_sync_mut/ndarray/fancy_index_spec.spl` passes; zero `skip()`.  

---

### T-NDARRAY-27 — Remove `Tensor = NDArray` alias and migrate remaining call sites

**Effort:** M (1d)  
**Phase:** v1.1  
**Depends-on:** T-NDARRAY-26

**Description:**  
(1) Remove `type Tensor<T> = NDArray<T>` alias from `tensor.spl`.
(2) Grep all `.spl` files under `src/` for remaining `Tensor<` usages (rerun T-NDARRAY-04
approach). Each remaining usage is either a call site that ignored the deprecation warning or
an internal tensor subtree reference. Migrate to `NDArray<T>` or `Matrix<T>`/`Vector<T>` as
appropriate.
(3) Verify no `Tensor<` references remain in `src/lib/` (excluding comments and the subtree
that was already migrated in T-NDARRAY-05).
(4) Confirm arch §12 (v1.1 → v2) gate item: "Tensor = NDArray alias removed; no remaining
references to Tensor type in src/lib/" is satisfied.

**Acceptance:**  
- `grep -r "Tensor<" src/lib/` returns zero matches (excluding comments).  
- `bin/simple test` passes all existing tests with no regressions.  
- Arch §12 v1.1 alias removal gate checked off.  

---

## v2 Tasks

---

### T-NDARRAY-28 — Register pure-Simple backend slot in `BackendRegistry`

**Effort:** S (½d)  
**Phase:** v2  
**Depends-on:** T-NDARRAY-27

**Description:**  
Add a `PureSimpleBackend` placeholder in `backend.spl` implementing `StorageBackend` with all
methods delegating to pure-Simple Simple arithmetic (no C externs). Selected via
`SIMPLE_BLAS_BACKEND=pure_simple`. In v2, the actual kernels (AXPY, GEMM in pure Simple) are
written by the linalg agent; this task just registers the backend slot and wires up the
`BackendRegistry.register("pure_simple", PureSimpleBackend)` call. Verify the arch §6 "Future
Pure-Simple Backend Slot" contract is satisfied.

**Acceptance:**  
- `SIMPLE_BLAS_BACKEND=pure_simple` selects `PureSimpleBackend` without error.  
- `NDArray.zeros(Shape(4), Device.CPU)` via `PureSimpleBackend` succeeds (uses Simple-level alloc).  
- `bin/simple lint src/lib/nogc_sync_mut/ndarray/backend.spl` clean.  
- Arch §6 backend selection table for `pure_simple` value satisfied.  

---

## Cross-Area Dependency Summary

| This task | Cross-area dep | Dep meaning |
|-----------|---------------|-------------|
| T-NDARRAY-08 | T-PERFSUGAR-01 | `rt_f64_array_alloc` must exist in runtime |
| T-NDARRAY-09 | T-PERFSUGAR-01 | same — used in zeros/ones/full/eye alloc path |
| T-NDARRAY-10 | T-PERFSUGAR-01 | same — used in from_seq copy |
| T-NDARRAY-11 | T-PERFSUGAR-01 | same — used in arange/linspace alloc |
| T-NDARRAY-13 | T-PERFSUGAR-03 | workaround plan must be understood before impl |
| T-NDARRAY-20 | T-CUDA-01 | CublasBackend impl (CUDA agent registers it) |
| T-NDARRAY-24 | T-PERFSUGAR-05 | StridedView extern must be fixed |

**Anti-pattern checklist (verify before each task is closed):**
- [ ] No `nvfortran` dependency added
- [ ] No DataFrame ops or `Symbol` intern added (df scope)
- [ ] No acceptance criterion written as "passes `--mode=native`"
- [ ] No `skip()` in any spec file
- [ ] No TODO converted to NOTE
- [ ] No primitive type (`f64`, `i64`, `f32`, `i32`, `u64`) in any public `fn` signature or exported `struct` field
- [ ] All specs run under `SIMPLE_BLAS_BACKEND=mock` in interpreter mode

---

## Phase Summary

| Phase | Task IDs | Count |
|-------|----------|-------|
| v1 | T-NDARRAY-01 through T-NDARRAY-23 | 23 |
| v1.1 | T-NDARRAY-24 through T-NDARRAY-27 | 4 |
| v2 | T-NDARRAY-28 | 1 |
| **Total** | | **28** |

**Effort breakdown:**
- S (½d): T-NDARRAY-01, 02, 06, 11, 12, 13, 19, 20, 22, 28 = 10 × ½d = 5d
- M (1d): T-NDARRAY-03, 07, 08, 09, 10, 16, 18, 21, 23, 25, 27 = 11 × 1d = 11d
- L (2d): T-NDARRAY-04, 05, 14, 15, 17, 24, 26 = 7 × 2d = 14d
- **Total: ~30 person-days**
