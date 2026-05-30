<!-- codex-design -->
# Science Math Backend Extensions Design

**Date:** 2026-05-05
**Status:** Design target with initial slices. Narrow SIMD f64x4 and f32x4 ndarray binary probes, narrow f64x4 ndarray scalar arithmetic probes, narrow f32x4 ndarray scalar add/sub/mul/div probes with scalar tail handling, narrow f64x4 and f32x4 ndarray whole-array sum/mean probes, narrow f64x4 and f32x4 ndarray abs/square/neg unary probes, narrow f64x4/f32x4 linalg probes, interpreter-visible f32x4/f32x8 SIMD arithmetic probes, focused SIMD spec wall-clock and public operation latency gating, explicit CUDA device-buffer, array-shaped storage helpers, copy-producing CUDA reshape/flatten/2-D transpose shape operations, explicit CUDA 1-D concatenate/stack combine operations, device-side Float64 CUDA array-array and array-scalar add/sub/mul/div kernels, scalar-result CUDA sum/mean/min/max reduction kernels, 2-D CUDA sum/mean-axis kernels, device-side 1-D/2-D slicing including positive steps, negative bounds, negative steps, and empty slices, explicit copied PyTorch tensor ownership with resident 1-D through 4-D zeros/ones/full/empty/random-uniform/random-normal creation, arange/linspace/eye creation, add/sub/mul/div/atan2, 2-D matmul, resident solve/inverse, abs/neg/square/sqrt/exp/log/relu/leaky_relu/gelu/sigmoid/tanh/sin/cos/tan/asin/acos, scalar add/sub/mul/div/pow, softmax/log_softmax, reduction/statistics/determinant, axis-reduction, 1-D through 4-D reshape, rank-2 through rank-4 permute, contiguous materialization, positive-bound slicing, and combine probes, and explicit CUDA/PyTorch dynamic linalg dot/GEMV/GEMM/solve/inverse routing exist; broad SIMD, broad CUDA-native NDArray kernels, and PyTorch/libtorch zero-copy backend dispatch remain future work.
**Related:** `doc/03_plan/science_math_backend_extension_research_plan.md`, `doc/04_architecture/science_math_lib_set.md`, `doc/05_design/science_math_lib_set.md`.

## Design Goal

Extend the science/math stack with optional accelerated backends while keeping the scalar backend as the portable source of truth.

The backend order is deliberate:

1. SIMD first, because it improves host-only ndarray/linalg paths without new external runtime dependencies.
2. CUDA second, because it requires explicit device memory, runtime symbols, and opt-in hardware verification.
3. PyTorch/libtorch third, because it is best treated as optional tensor interop and ML acceleration rather than a foundation for `std.ndarray`.

This design is the target shape for acceleration. Current implementation slices are intentionally narrow and do not replace the scalar backend as the source of truth. Broader backend routing still requires the research and selected requirements described in `doc/03_plan/science_math_backend_extension_research_plan.md`.

## Backend Capsule

All accelerated paths sit behind the existing science backend capsule:

```text
std.ndarray / std.linalg / std.scipy.* / std.df
        |
        v
ScienceBackend contract
        |
        +-- ScalarCpuBackend
        +-- MockBackend
        +-- CpuSimdBackend
        +-- OpenBlasBackend
        +-- CudaBackend
        +-- LibtorchBackend
```

Public APIs must not import CUDA, libtorch, or target-specific SIMD modules directly. They call a backend selector and receive either a supported backend operation or a typed error.

## Module Boundaries

The future code should keep backend-specific dependencies behind private modules:

```text
src/lib/common/science_backend/        shared capability records and selector
src/lib/common/science_backend/scalar/ portable reference implementation
src/lib/common/science_backend/mock/   deterministic tests and diagnostics
src/lib/common/science_backend/simd/   CPU SIMD kernels or native shims
src/runtime/*cuda*                    CUDA allocation, copy, BLAS, solver shims
src/runtime/*torch*                   optional libtorch/DLPack shims
```

Public packages such as `std.ndarray`, `std.linalg`, and `std.scipy.*` may depend on the backend contract. They must not depend on CUDA headers, libtorch headers, or CPU-feature-specific modules. DataFrame operations should stay row/column semantic first; only numeric column kernels may dispatch to science backends after missing-value and dtype semantics are explicit.

## Capability Record

Each backend reports:

- `name`
- supported `DType` values
- supported `Device` values
- supported `Layout` and stride constraints
- required alignment
- operation list
- in-place support
- allocation behavior
- blocking behavior
- required runtime symbols
- deterministic test mode availability

Dispatch must fail before computation when a backend cannot honor the request. Silent partial execution on the wrong device is not allowed.

Capability records must be cheap to query on hot paths. Expensive probing, dynamic symbol lookup, and device enumeration should happen once during backend initialization or lazy first use, then be cached with invalidation only when configuration changes.

## Selection Order

Backend selection uses this priority:

1. Explicit per-call backend override.
2. Environment/config override for diagnostics and tests.
3. Device-owned backend, such as `Device.Cuda(0)`.
4. Operation-specific preferred backend from capability records.
5. Scalar fallback.

Fallback is allowed only when it preserves observable semantics. CUDA arrays must not silently copy to CPU for mutating operations unless the API name or options make the transfer explicit.

The selector should expose a diagnostic trace for tests and user reports:

```text
operation=gemm requested=cuda selected=cuda reason=supported dtype=f64 layout=row_major device=cuda:0
operation=sum requested=auto selected=scalar reason=length_below_simd_threshold
operation=solve requested=torch selected=error reason=missing_runtime_symbol:rt_torch_torchtensor_linalg_solve
```

## SIMD Design

`CpuSimdBackend` accelerates CPU arrays when all constraints pass:

- dtype is F64 or F32 for v1;
- input and output arrays are contiguous;
- length exceeds a backend threshold;
- aliasing is absent or explicitly supported;
- operation is in the SIMD operation table.

Initial operation table:

- elementwise add, sub, mul, div;
- unary abs, neg, square;
- sum and mean reductions;
- dot and axpy;
- row-major matvec;
- small contiguous copy/fill helpers if benchmarking shows value.

Compiler-level auto-SIMD remains a separate follow-up. This backend can use runtime/library kernels first, then later consume compiler idiom recognition.

SIMD implementation rules:

- Keep scalar implementations as readable reference code.
- Use explicit tests for zero length, one element, non-vector-width lengths, threshold boundaries, and aliasing.
- Keep backend thresholds configurable for benchmark work but deterministic in tests.
- Record measured thresholds before enabling automatic dispatch by default.
- Avoid global compiler changes in the first SIMD backend unless separately selected by requirements.

Current SIMD probe coverage:

- `std.ndarray` has f64x4 add/sub/mul/div dispatch with scalar tail handling for contiguous one-dimensional Float64 arrays.
- `std.ndarray` has f64x4 scalar add/sub/mul/div dispatch with scalar tail handling for contiguous one-dimensional Float64 arrays.
- `std.ndarray` has f64x4 whole-array sum dispatch with scalar tail handling for contiguous one-dimensional Float64 arrays; `mean` reuses that sum path.
- `std.ndarray` has explicit f32x4 whole-array `sum_f32` dispatch with scalar tail handling for contiguous one-dimensional Float32 arrays; `mean_f32` reuses that sum path.
- `std.ndarray` has f64x4 abs/square/neg unary dispatch with scalar tail handling for contiguous one-dimensional Float64 arrays.
- `std.ndarray` has a narrow Float32 storage surface plus f32x4 add/sub/mul/div dispatch with scalar tail handling for contiguous one-dimensional arrays.
- `std.ndarray` has f32x4 scalar add/sub/mul/div dispatch with scalar tail handling for contiguous one-dimensional Float32 arrays.
- `std.ndarray` has explicit f32x4 `abs_f32`/`square_f32`/`neg_f32` unary dispatch with scalar tail handling for contiguous one-dimensional Float32 arrays.
- `std.linalg` has f64x4 dot and axpy helpers plus public contiguous one-dimensional `dot`/`try_axpy` dispatch with scalar tail handling.
- `std.linalg` has explicit Float32 `dot_f32`/`try_axpy_f32` entry points plus f32x4 dot and axpy helpers with scalar tail handling for contiguous one-dimensional arrays.
- `std.simd` has interpreter-visible f32x4 and f32x8 add/sub/mul/div/FMA intrinsics to cover the F32 side of the selected SIMD requirement.
- This is still not a general backend selector, broad Float32 ndarray API, multi-dimensional SIMD traversal, automatic mixed-dtype linalg dispatch, broad unary SIMD coverage beyond abs/square/neg, or broad ndarray/linalg SIMD implementation.

## OpenBLAS/LAPACKE Design

`OpenBlasBackend` is the host-native dense linalg backend for Phase B:

- It is selected through `SIMPLE_BLAS_BACKEND=openblas` or explicit adapter calls.
- Public `std.linalg` signatures stay scalar-compatible; unavailable native linkage falls back to scalar behavior.
- Small public `solve` calls stay on the scalar path to preserve exact scalar test semantics; the explicit `openblas_solve` adapter exercises LAPACKE parity and larger configured solves may route through OpenBLAS.
- Availability checks use typed backend diagnostics through `require_linalg_backend("openblas")`.
- The runtime C ABI exposes integer-callable bit-buffer wrappers for `ddot`, `daxpy`, `dgemm`, and `dgesv` so interpreter-mode tests can exercise the same dynamic loading path as CUDA/PyTorch probes.
- `scripts/fetch-scilib-openblas-deps.shs` can stage Ubuntu OpenBLAS/LAPACKE packages into `build/scilib/deps/root` without root privileges.
- `scripts/check-scilib-runtime-shims.shs` builds mock and OpenBLAS shims, auto-detects the local staged dependency root when present, verifies ABI symbol parity, runs deterministic BLAS/LAPACK parity fixtures, records warm load/latency/RSS evidence, and runs the Simple OpenBLAS backend spec against a canonical `libspl_scilib.so` SFFI path.
- `SCILIB_REQUIRE_REAL_OPENBLAS=1` is the hard real-backend gate. It must fail when the shim compiled the unavailable fallback.

Current OpenBLAS probe coverage:

- `std.linalg.openblas_dot`, `openblas_axpy`, `openblas_gemv`, `openblas_gemm`, and `openblas_solve` are explicit dynamic adapters with typed unavailable errors.
- Existing public `dot`, `try_axpy`, `gemv`, `try_gemm`, and larger `solve` calls consult OpenBLAS when configured, then preserve scalar fallback if the shim is absent or non-real.
- The C shim compiles and exports the complete mock/OpenBLAS ABI on this host. With locally staged OpenBLAS/LAPACKE packages, `SCILIB_REQUIRE_REAL_OPENBLAS=1 scripts/check-scilib-runtime-shims.shs` reports `openblas_real=true` and the OpenBLAS-configured scilib suite passes.
- This completes the selected Phase B real-backend probe and gate. Phase C now reuses the same configured public-routing pattern for CUDA and PyTorch dot/GEMV/GEMM/solve probes, while broad accelerator ownership and ndarray dispatch remain future work.

## CUDA Design

`CudaBackend` introduces explicit device buffers owned by ndarray metadata:

- `Device.Cuda(index)` identifies device placement.
- Host/device copies are explicit constructors or conversion calls.
- CUDA memory allocation and free go through runtime shims.
- Streams are represented by backend handles, not public raw pointers.
- BLAS and solver calls route through `rt_cuda_*`, `rt_cublas_*`, and `rt_cusolver_*` C ABI symbols.

Initial operation table:

- device allocation/free/copy;
- dot, gemv, gemm;
- solve for explicit Float64 vector right-hand sides through the narrow cuSOLVER-backed CUDA shim; inverse remains scalar/future backend work;
- elementwise add/mul only after device kernel launch and stream semantics are designed.

Async APIs must expose or document synchronization. A function in `nogc_async_mut` cannot hide a blocking device sync without either returning an async handle or documenting the blocking point.

CUDA ownership model:

```text
Host NDArray        owns host buffer, Device.Cpu
Cuda NDArray        owns device buffer handle, Device.Cuda(index)
Transfer operation  creates a new owner unless an explicit in-place copy API is selected
Backend handle      owns stream/library handles and caches device capability
```

CUDA implementation rules:

- Device allocation/free must be exception-safe through runtime cleanup paths.
- Host/device transfers must be explicit in API names or options.
- cuBLAS/cuSOLVER status values must map to typed backend errors.
- CPU-only hosts should skip CUDA-specific tests with an unavailable-backend diagnostic, while scalar parity tests continue to run.
- Initial CUDA work should prefer dense linalg where transfer cost and payoff are easiest to reason about.

The implemented v1 CUDA probe is explicit opt-in linalg/storage interop:

- `std.cuda.CudaBuffer.allocate(size)` exposes explicit CUDA device-buffer ownership for testable allocation and free.
- `CudaBuffer.copy_from_i64_values`, `copy_to_i64_values`, `copy_to`, and `memset` exercise host-to-device, device-to-host, device-to-device, and memset transfers through the runtime CUDA FFI.
- `std.cuda.CudaNDArray.from_f64_array(host, device_id)` owns a `CudaBuffer` plus `Shape`, `DType.F64`, and `Device.CUDA(index: device_id)` metadata for explicit host-to-device array storage.
- `CudaNDArray.to_host_f64()` copies the owned device buffer back into a host `NDArray`; `CudaNDArray.free()` releases the device owner.
- `CudaNDArray.reshape_f64`, `flatten_f64`, and `transpose_2d_f64` produce new CUDA-owned results rather than aliasing buffers, so ownership remains single-release. Reshape/flatten use device-to-device copy with new metadata; 2-D transpose uses element device-to-device copies and handles empty shapes without allocation.
- `CudaNDArray.concatenate_1d_f64` and `stack_1d_f64` validate dtype, rank, and device, then combine 1-D CUDA owners through device-to-device copies.
- `CudaNDArray.add_f64`, `sub_f64`, `mul_f64`, and `div_f64` validate dtype, shape, and device, allocate a device result buffer, and execute the runtime `rt_cuda_f64_binary_op` PTX kernel without copying operand data back to host for arithmetic.
- `CudaNDArray.add_scalar_f64`, `sub_scalar_f64`, `mul_scalar_f64`, and `div_scalar_f64` provide explicit scalar arithmetic for CUDA owners. Add/sub/mul stage a same-shape scalar device buffer and reuse the device binary kernel; div uses the existing `rt_cuda_f64_scalar_div` kernel.
- `CudaNDArray.sum_f64` executes a narrow runtime `rt_cuda_f64_sum` PTX kernel over the contiguous device owner and copies only the scalar result bits back to host; empty sum returns `0.0`.
- `CudaNDArray.mean_f64` reuses the device-side scalar sum and divides on host; empty mean is rejected before transfer.
- `CudaNDArray.min_f64` and `max_f64` execute narrow runtime `rt_cuda_f64_minmax` PTX kernels over the contiguous device owner and copy only the scalar result bits back to host; empty min/max are rejected before transfer.
- `CudaNDArray.sum_axis_f64(axis)` validates a 2-D Float64 CUDA owner, supports axis `0`, `1`, and `-1`, executes `rt_cuda_f64_sum_axis`, and returns a new 1-D CUDA-owned result buffer without copying the source owner to host.
- `CudaNDArray.slice_1d_f64` normalizes bounds before transfer, preserves valid empty slices as zero-length CUDA owners, uses device-to-device copy for contiguous positive step-1 slices, and uses `rt_cuda_f64_slice_1d` for strided positive and negative steps without copying the source owner to host.
- `CudaNDArray.slice_2d_f64` normalizes bounds before transfer, preserves valid empty row or column slices as zero-length CUDA owners with the requested shape, uses per-row device-to-device copies for rectangular positive step-1 slices, and uses `rt_cuda_f64_slice_2d` for strided positive and negative row/column steps without copying the source owner to host.
- `std.linalg.cuda_dot(left, right)` accepts two Float64 NDArrays, stages host Float64 bit buffers through `libspl_scilib.so`, executes a cuBLAS-backed device dot when the CUDA scilib shim is available, frees temporary device buffers, and returns a scalar Float64.
- `std.linalg.cuda_dot_values(left, right)` provides the same path for raw Float64 arrays.
- `std.linalg.cuda_gemm(alpha, a, b, beta, c_in)` stages row-major Float64 matrix bit buffers, executes a cuBLAS-backed device GEMM, copies the result back, and returns a new host NDArray.
- `std.linalg.cuda_gemv(alpha, matrix, vector, beta, y_in)` stages row-major Float64 matrix/vector bit buffers through `rt_scilib_cuda_dgemv_bits`, executes a direct cuBLAS-backed device GEMV, copies the result back, and returns a new host vector.
- `std.linalg.cuda_solve(a, b)` stages a square row-major Float64 matrix and matching vector through `rt_scilib_cuda_dgesv_bits`, executes cuSOLVER LU solve in column-major device layout, copies the solution back, and maps singular/nonzero `info` to typed backend execution errors.
- `std.linalg.cuda_inv(a)` stages a square row-major Float64 matrix and an identity right-hand side through `rt_scilib_cuda_dgesv_bits` with `nrhs=n`, executes cuSOLVER LU solve in column-major device layout, copies the inverse back, and maps singular/nonzero `info` to typed backend execution errors.
- `std.linalg.backend_status("cuda")` reports available only when `rt_scilib_cuda_available` is present and returns true.
- Public `std.linalg.dot`, `gemv`, and `try_gemm` consult the CUDA adapter when `SIMPLE_BLAS_BACKEND=cuda`, then preserve scalar fallback if the shim is absent or rejects the operation.
- Public `std.linalg.solve` and larger `inv` calls consult the CUDA adapter when `SIMPLE_BLAS_BACKEND=cuda`, then preserve scalar fallback if the shim is absent or rejects the operation.
- If the shim is absent, APIs return typed `BackendUnavailable("cuda")` errors and scalar tests keep passing.

This probe is configured public routing and explicit storage ownership, not default automatic dispatch. It provides native CUDA kernels for copied Float64 array-array and array-scalar add/sub/mul/div storage owners, copy-producing CUDA reshape/flatten/2-D transpose shape operations, explicit CUDA 1-D concatenate/stack combine operations, scalar-result sum/mean/min/max reductions, 2-D sum-axis reductions with `mean_axis_f64(axis)` implemented as sum-axis plus device scalar divide, contiguous and strided 1-D slices including negative steps and empty slices, and rectangular/strided 2-D slices including negative row/column steps and empty row or column slices; it does not yet provide broad CUDA-native ndarray kernels, broad axis reductions beyond 2-D sum/mean, parallel reductions, stream controls, mutating NDArray operations, broad cuSOLVER coverage beyond `dgesv`, or no-hidden-copy checks for mutating NDArray APIs. The low-level CUDA perf probe, explicit device-buffer and `CudaNDArray` transfer/arithmetic/shape-operation/combine/reduction/slicing specs, configured no-shim fallback, runtime Float64 binary/reduction/scalar-divide/slice-kernel tests, and interpreter available-shim scalar parity for `cuda_dot`/direct `cuda_gemv`/`cuda_gemm`/`cuda_solve`/`cuda_inv` pass on the current host.

## PyTorch/Libtorch Design

`LibtorchBackend` is optional and primarily supports tensor interop:

- v1 exposes selected no-autograd tensor kernels through backend dispatch.
- ndarray-to-tensor conversion must declare copy or zero-copy behavior.
- DLPack interop is preferred for zero-copy exchange when lifetime rules are proven.
- Direct libtorch C++ wrappers or stable ABI shims can be used behind Simple runtime symbols.
- Autograd, neural-network modules, and optimizers belong in a later `std.ml` design.

The backend must not become a dependency for core ndarray correctness. If libtorch is unavailable, scalar and mock tests continue to pass.

The implemented v1 probe is explicit opt-in linalg interop only:

- `std.linalg.torch_dot(left, right)` accepts two Float64 NDArrays, copies contiguous values into libtorch tensors through `libspl_torch.so`, executes a no-autograd tensor dot, frees tensor handles, and returns a scalar Float64.
- `std.linalg.torch_dot_values(left, right)` provides the same path for raw Float64 arrays.
- `std.linalg.torch_gemm(alpha, a, b, beta, c_in)` copies row-major Float64 matrices into libtorch tensors, executes tensor matmul, copies the result back, applies alpha/beta scaling on the Simple side, and returns a host NDArray.
- `std.linalg.torch_gemv(alpha, matrix, vector, beta, y_in)` is a public vector wrapper over the explicit PyTorch GEMM adapter using an `N x 1` temporary matrix.
- `std.linalg.TorchNDArray.from_f64_array(host)` creates an explicit libtorch-owned copied Float64 tensor from a contiguous 1-D or 2-D host NDArray and records Simple shape/dtype metadata.
- `TorchNDArray.zeros_f64(shape)`, `ones_f64(shape)`, and `full_f64(shape, value)` create 1-D through 4-D libtorch-owned tensors through native constructors, convert them to Float64, and record Simple shape/dtype metadata.
- `TorchNDArray.arange_f64(start, end, step)`, `linspace_f64(start, end, steps)`, and `eye_f64(size)` create libtorch-owned Float64 range and identity tensors with Simple shape metadata and validate invalid counts before backend execution.
- `TorchNDArray.to_host_f64()` copies the libtorch tensor back into a Simple host NDArray; `TorchNDArray.free()` releases the owned handle.
- `TorchNDArray.add_f64(other)`, `sub_f64(other)`, `mul_f64(other)`, `div_f64(other)`, and `atan2_f64(other)` perform shape-checked resident Float64 tensor arithmetic and return another owned tensor handle.
- `TorchNDArray.matmul_f64(other)` performs 2-D resident Float64 tensor matrix multiplication after validating dtype, rank, inner dimensions, and device, then returns another owned tensor handle.
- `TorchNDArray.solve_f64(rhs)` performs 2-D square resident Float64 linear solve for a 1-D Float64 right-hand side and returns a 1-D owned tensor handle.
- `TorchNDArray.inverse_f64()` performs 2-D square resident Float64 matrix inversion through libtorch and returns another owned tensor handle.
- `TorchNDArray.abs_f64()`, `neg_f64()`, `square_f64()`, `sqrt_f64()`, `exp_f64()`, `log_f64()`, `relu_f64()`, `leaky_relu_f64(slope)`, `sigmoid_f64()`, `tanh_f64()`, `sin_f64()`, `cos_f64()`, `tan_f64()`, `asin_f64()`, and `acos_f64()` perform resident Float64 unary tensor operations and return another owned tensor handle.
- `TorchNDArray.add_scalar_f64(scalar)`, `sub_scalar_f64(scalar)`, `mul_scalar_f64(scalar)`, `div_scalar_f64(scalar)`, and `pow_scalar_f64(exponent)` perform resident Float64 scalar arithmetic and power operations and return another owned tensor handle.
- `TorchNDArray.softmax_axis_f64(axis)` and `log_softmax_axis_f64(axis)` run resident rank-1/rank-2 softmax operations with axis validation and preserve shape metadata.
- `TorchNDArray.sum_f64()`, `mean_f64()`, `min_f64()`, `max_f64()`, `norm_f64()`, `std_f64()`, `var_f64()`, and `det_f64()` run scalar-result reductions/statistics or determinant operations on the resident tensor before any explicit host copy.
- `TorchNDArray.sum_axis_f64(axis)`, `mean_axis_f64(axis)`, `min_axis_f64(axis)`, `max_axis_f64(axis)`, `argmin_axis_f64(axis)`, and `argmax_axis_f64(axis)` run 2-D resident axis reductions through libtorch reduction-dim shims and return 1-D owned Float64 tensor handles.
- `TorchNDArray.clone_f64()`, `unsqueeze_f64(axis)`, `squeeze_f64(axis)`, `reshape_f64(shape)`, `flatten_f64()`, `transpose_2d_f64()`, `permute_f64(axes)`, and `contiguous_f64()` run resident libtorch copy/view/shape operations and keep Simple shape metadata aligned before explicit host copy; `reshape_f64` accepts rank 1 through 4 shapes with matching element counts, and `permute_f64` accepts rank 2 through 4 tensors with a complete non-duplicated axis order.
- `TorchNDArray.slice_1d_f64(spec)` and `slice_2d_f64(rows, cols)` run resident positive-bound, positive-step libtorch slice operations and keep Simple shape metadata aligned before explicit host copy.
- `TorchNDArray.empty_f64(shape)`, `random_uniform_f64(shape)`, and `random_normal_f64(shape)` allocate resident 1-D through 4-D libtorch tensor owners and keep creation shape metadata aligned before explicit host copy.
- `TorchNDArray.concatenate_1d_f64(arrays)` and `stack_1d_f64(arrays)` combine two to four resident 1-D Float64 tensors through libtorch cat/stack shims and return owned tensor handles.
- `std.linalg.torch_solve(a, b)` stages a square Float64 matrix and matching vector through copied tensor handles and calls `rt_torch_torchtensor_linalg_solve`.
- `std.linalg.torch_inv(a)` stages a square Float64 matrix through a copied tensor handle, calls `rt_torch_torchtensor_inverse`, copies the result back, and returns a host NDArray.
- `std.linalg.backend_status("torch")` and `"pytorch"` report available only when the dynamic shim can be loaded.
- Public `std.linalg.dot`, `gemv`, `try_gemm`, larger `solve`, and larger `inv` calls consult the PyTorch adapter when `SIMPLE_BLAS_BACKEND=torch` or `SIMPLE_BLAS_BACKEND=pytorch`, then preserve scalar fallback if the shim is absent or rejects the operation.
- If the shim is absent, APIs return typed `BackendUnavailable("pytorch")` errors and scalar tests keep passing.

This probe is configured public routing for dot/GEMV/GEMM/solve/inv, not default automatic dispatch. It provides copied tensor ownership, resident 1-D through 4-D zeros/ones/full/empty/random-uniform/random-normal creation, arange/linspace/eye creation, resident add/sub/mul/div/atan2 arithmetic, resident 2-D matmul, resident solve/inverse, resident scalar add/sub/mul/div/pow operations, resident abs/neg/square/sqrt/exp/log/relu/leaky_relu/gelu/sigmoid/tanh/sin/cos/tan/asin/acos unary operations, resident softmax/log_softmax operations, resident reductions/statistics/determinant operations, resident 2-D axis reductions, resident clone/reshape/permute/contiguous/slice/combine operations, and copied dense linalg interop only; it does not yet provide DLPack, zero-copy lifetime guards, CUDA tensor routing, autograd, broad elementwise coverage beyond the exposed arithmetic/unary probes, or general ndarray backend selection.

PyTorch ownership model:

```text
Simple-owned copied tensor      Simple creates tensor from copied buffer
Simple-owned shared tensor      Simple buffer stays alive through exported capsule/lifetime guard
Libtorch-owned copied ndarray   Simple copies tensor data into an NDArray buffer
Libtorch-owned shared ndarray   Only allowed after lifetime guard tests are stable
```

PyTorch implementation rules:

- Treat DLPack and direct wrapper shims as separate capability flags.
- Keep autograd disabled or explicitly detached for backend-dispatch kernels.
- Put neural network layers, optimizers, and training loops under a later `std.ml` design, not `std.ndarray`.
- Report ABI/version mismatch as `BackendUnavailable` or `MissingRuntimeSymbol`, not as a generic execution failure.

## Error Model

Shared backend errors:

- `BackendUnavailable(name)`
- `UnsupportedDType(backend, dtype)`
- `UnsupportedDevice(backend, device)`
- `UnsupportedLayout(backend, layout)`
- `UnsupportedStride(backend)`
- `UnsupportedAliasPattern(backend)`
- `MissingRuntimeSymbol(symbol)`
- `BlockingOperationInAsyncContext(operation)`
- `BackendExecutionFailed(backend, message)`

Layer C public APIs should preserve domain errors where possible and wrap backend failures only when the backend detail matters to the caller.

Error messages should include the requested backend, selected backend when any, operation name, dtype, shape rank, and device. They should not dump full array contents.

## Verification Design

Required always-on gate:

```text
SIMPLE_BLAS_BACKEND=mock bin/simple test test/feature/scilib --mode=interpreter
bin/simple check src/lib
```

Backend-specific gates:

- SIMD: scalar parity specs plus the focused `scripts/check-scilib-accelerator-perf.shs` wall-clock gate. The gate records focused interpreter-visible public operation budgets for f64 dot/axpy, f32 dot/axpy, NDArray f64 add, NDArray f64 sum, NDArray f64 abs/square, NDArray f64 scalar multiply, NDArray f32 sum, NDArray f32 scalar multiply/divide, and NDArray f32 abs/square through `test/perf/scilib_simd_ops_perf_spec.spl`; broad native SIMD microbenchmarks remain follow-up work.
- CUDA: opt-in GPU specs gated by CUDA availability; tests must report unavailable rather than fail on CPU-only hosts. The accelerator perf gate records scalar fallback comparison timings for the same dot/GEMV/GEMM/solve/inverse fixtures plus narrow 4096-element Float64 HtoD/DtoH transfer timings.
- PyTorch: opt-in libtorch specs gated by runtime availability and ABI version diagnostics. The accelerator perf gate records scalar fallback comparison timings for the same dot/GEMM/solve/inverse fixtures plus narrow 4096-element Float64 tensor creation/copy timings.

Current PyTorch probe gates:

```text
SIMPLE_BLAS_BACKEND=mock bin/simple test test/feature/scilib/linalg_torch_backend_spec.spl --mode=interpreter --no-cache
g++ -std=c++17 -O2 -fPIC -shared src/runtime/torch_ffi.cpp -o build/scilib/libspl_torch.so ...
SIMPLE_SFFI_PATH=build/scilib SIMPLE_BLAS_BACKEND=mock bin/simple test test/feature/scilib/linalg_torch_backend_spec.spl --mode=interpreter --no-cache
```

Current CUDA probe gates:

```text
SIMPLE_BLAS_BACKEND=mock bin/simple test test/feature/scilib/cuda_device_buffer_spec.spl --mode=interpreter --no-cache
SIMPLE_SFFI_PATH=/tmp/simple-no-sffi SIMPLE_BLAS_BACKEND=mock bin/simple test test/feature/scilib/linalg_cuda_backend_spec.spl --mode=interpreter --no-cache
gcc -shared -fPIC -I/usr/local/cuda-13.0/targets/x86_64-linux/include -Isrc/runtime/scilib src/runtime/scilib/cublas_shim.c -o build/scilib/libspl_scilib.so -L/usr/local/cuda-13.0/targets/x86_64-linux/lib -lcublas -lcudart -Wl,-rpath,/usr/local/cuda-13.0/targets/x86_64-linux/lib
SIMPLE_SFFI_PATH=build/scilib SIMPLE_BLAS_BACKEND=mock bin/simple test test/feature/scilib/linalg_cuda_backend_spec.spl --mode=interpreter --no-cache
```

Current accelerator performance gate:

```text
SCILIB_REQUIRE_ACCELERATOR_PERF=1 scripts/check-scilib-accelerator-perf.shs
```

This gate builds the local CUDA and PyTorch shims when the host toolchains are present, checks scalar parity for CUDA 4096-element dot, CUDA 64x32 GEMV, CUDA 32x32 GEMM, CUDA 16x16 solve, CUDA 16x16 inverse, PyTorch dot, PyTorch GEMM, PyTorch 16x16 solve, and PyTorch 16x16 inverse fixtures, records warm dynamic-load time, operation latency, focused public SIMD operation latency, and max RSS, and enforces configurable budgets through `SCILIB_ACCELERATOR_MAX_LOAD_MS`, `SCILIB_ACCELERATOR_MAX_OP_US`, `SCILIB_SIMD_MAX_SPEC_MS`, `SCILIB_SIMD_MAX_OP_NS`, and `SCILIB_ACCELERATOR_MAX_RSS_KB`.

Performance evidence before release:

- warm backend startup time;
- representative operation latency for small, medium, and large arrays;
- max RSS during representative workloads;
- backend selection trace for at least one supported and one fallback case.

System test design for the future backend feature should include:

- scalar/mock parity for every backend-routed operation;
- backend-unavailable behavior for CUDA and PyTorch on default developer machines;
- dispatch override tests using environment/config controls;
- no-hidden-copy tests for CUDA mutating operations;
- lifetime tests for PyTorch zero-copy paths before enabling them;
- startup checks proving backend discovery does not materially slow default library import or MCP/LSP package startup.

## Implementation Milestones

### Milestone 1: Contract And Diagnostics

- Add backend capability types.
- Add selector with scalar and mock entries.
- Add dispatch trace diagnostics.
- Add parity test fixture helpers.
- Add unavailable-backend test helpers.
- Add documentation for backend override configuration.

### Milestone 2: SIMD

- Add contiguous F64/F32 operation kernels.
- Add threshold policy.
- Add scalar fallback tests.
- Record initial benchmark data.
- Enable automatic dispatch only after parity and benchmark evidence are recorded.

### Milestone 3: CUDA

- Add runtime symbol inventory.
- Add device allocation/copy lifecycle.
- Add cuBLAS dot/gemm.
- Broaden cuSOLVER beyond vector `dgesv` after the current row-major to column-major matrix layout conversion is exercised on larger fixtures.
- Add opt-in GPU verification script and unavailable-backend reporting path.

### Milestone 4: PyTorch/Libtorch

- Add availability probe.
- Add ndarray/tensor conversion rules.
- Add selected tensor kernels.
- Add DLPack or wrapper-shim interop after ownership tests are stable.
- Add ABI/version diagnostics and package-size notes.

## Open Decisions

- Whether SIMD kernels should live in `src/lib/common` as pure fallback-compatible kernels or under runtime-backed native shims.
- Whether CUDA stream handles become public advanced options or remain backend-private in v1.
- Whether PyTorch zero-copy support lands before or after direct libtorch operator wrappers.
- Whether backend benchmarks become release-blocking or warning-only for the first accelerated backend.
- Whether OpenBLAS dispatch and CUDA/PyTorch dispatch share one selector or remain dense-linalg-specific adapters.
- Whether backend selection traces are always available in debug builds or only behind environment flags.

## Design Completion Gate

Before implementation starts, this design must be reconciled with final selected requirements and updated with:

- exact operation list for the selected first backend;
- concrete file/module names for new implementation code;
- selected fallback and unavailable-backend semantics;
- selected NFR targets for startup, latency, RSS, and benchmark fixtures;
- system test file paths and traceability from each selected `REQ-NNN`;
- release/package impact for optional native dependencies.
