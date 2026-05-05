<!-- codex-research -->
# Science Math Backend Extension Research Plan

**Date:** 2026-05-05
**Status:** Future research plan only. SIMD, CUDA, and PyTorch/libtorch backends are not part of the current implementation slice.
**Related:** `doc/01_research/domain/simd_auto_application.md`, `doc/01_research/domain/cpu_simd_scheduling.md`, `doc/01_research/domain/pytorch_integration.md`, `doc/01_research/domain/pytorch_wrapper_design.md`, `doc/04_architecture/science_math_lib_set.md`, `doc/05_design/science_math_lib_set.md`.

## Goal

Define the research work required before implementing accelerated science/math backends for `std.ndarray`, `std.linalg`, `std.scipy.*`, `std.df`, and later `std.ml`.

The planned extension order is:

1. `CpuSimdBackend` for contiguous CPU hot loops.
2. `CudaBackend` for explicit device arrays plus cuBLAS/cuSOLVER-backed dense linalg.
3. `LibtorchBackend` for optional PyTorch/libtorch tensor interop and broad ML kernel coverage.

This document is intentionally a plan, not a requirement selection or an implementation commitment. The current science-lib slice remains scalar/mock-backend focused. SIMD, CUDA, and PyTorch work starts only after the research artifacts, options, and final user-selected requirements listed below are complete.

## Non-Goals

- Do not implement these backends in the current science-lib slice.
- Do not make CUDA, PyTorch, or OpenBLAS mandatory for core correctness.
- Do not route DataFrame semantics through math blocks.
- Do not add autograd to `std.ndarray`; keep autograd in a later tensor/ML layer.
- Do not hide blocking host/device synchronization behind async APIs.
- Do not require GPU hardware, libtorch, or native BLAS packages for the default `src/lib` check or feature test suite.
- Do not change public ndarray/DataFrame semantics to fit a backend implementation shortcut.

## Source Baseline

Local research already establishes:

- SIMD should start from compiler/runtime capability routing and contiguous ndarray kernels, not broad expression magic.
- CPU parallel `@simd` scheduling can reuse the existing runtime direction around Rayon-style work stealing.
- PyTorch integration should prefer direct libtorch/ATen bindings for core kernels and reserve Python interop for ecosystem-only features.
- Existing science architecture already defines scalar, mock, SIMD, CUDA, OpenBLAS, and libtorch backend roles.

Current primary external references to confirm before implementation:

- LLVM auto-vectorization: loop vectorizer and SLP vectorizer behavior, cost model, reductions, runtime pointer checks, and diagnostics. Source: https://llvm.org/docs/Vectorizers.html
- OpenMP SIMD directives: portable directive vocabulary and restrictions useful as design reference even if Simple does not adopt OpenMP directly. Source: https://www.openmp.org/specifications/
- NVIDIA CUDA programming guide: device memory spaces, streams, asynchronous behavior, and host/device execution model. Source: https://docs.nvidia.com/cuda/cuda-c-programming-guide/
- PyTorch C++ and stable ABI docs: libtorch C++ API, stable C/C++ API boundary, and ABI limitations. Sources: https://docs.pytorch.org/docs/stable/cpp_index.html and https://docs.pytorch.org/docs/stable/notes/libtorch_stable_abi.html

## Research Threads

Each thread must produce evidence, not only recommendations. Evidence can include source references, local code maps, runtime symbol inventories, prototype measurements, or small throwaway experiments recorded in the research notes.

### Thread A: Backend Capability Contract

Questions:

- Which operations require backend dispatch in v1: elementwise ufuncs, reductions, dot, matmul, solve, inv, sparse ops, or DataFrame kernels?
- What capability record is sufficient for dtype, layout, device, alignment, aliasing, in-place behavior, allocation, and blocking behavior?
- How should backend selection be configured: environment, runtime config, compile-time target, explicit per-call override, or all of these in priority order?

Outputs:

- Final backend capability matrix.
- Error taxonomy for unsupported dtype/layout/device and unavailable runtime symbols.
- Dispatch trace format for debugging backend selection.
- Public/private module boundary map showing which packages may depend on backend internals.
- Compatibility notes for `nogc_sync_mut` and `nogc_async_mut` surfaces.

Acceptance criteria:

- Every initially accelerated operation has an explicit scalar fallback policy.
- Every backend-visible data structure has ownership and aliasing rules.
- Unsupported backend requests fail with typed diagnostics before executing partial work.

### Thread B: SIMD Backend

Questions:

- Which ndarray operations should use explicit Simple SIMD kernels versus relying on LLVM auto-vectorization?
- What minimum size thresholds avoid slowing small arrays?
- Which alignment and stride constraints are required for F64/F32/I64/Bool?
- How should scalar fallback and SIMD parity tests share fixtures?

Outputs:

- SIMD operation priority list.
- CPU feature detection and cache-key policy.
- Microbenchmark fixture set for warm latency and RSS.
- Decision on explicit vector kernels versus compiler idiom recognition for v1.
- Parity test matrix across dtype, length, alignment, and aliasing cases.

Acceptance criteria:

- SIMD v1 can be implemented without CUDA, PyTorch, OpenBLAS, or compiler-wide language changes.
- Thresholds are based on benchmark data for small, medium, and large arrays.
- Scalar parity tests cover remainder lanes and non-multiple-of-vector-width lengths.

### Thread C: CUDA Backend

Questions:

- Which runtime symbols are required for allocation, copy, stream, event, BLAS, and solver work?
- How should `Device.Cuda(index)` arrays own device memory and transfer back to host?
- Which operations must be stream-aware and which may be synchronous v1 calls?
- What GPU-only CI or opt-in local verification gates are realistic?

Outputs:

- CUDA C ABI shim inventory.
- Device memory lifecycle design.
- cuBLAS/cuSOLVER operation matrix and error mapping.
- GPU verification plan gated by environment availability.
- Stream and synchronization policy for sync and async library surfaces.
- Host/device transfer API proposal with explicit copy semantics.

Acceptance criteria:

- No CUDA operation silently copies device data to host as a fallback for mutation.
- CPU-only CI can distinguish "backend unavailable" from correctness failures.
- Runtime symbol loading, driver/runtime version diagnostics, and memory cleanup paths are specified.

### Thread D: PyTorch/Libtorch Backend

Questions:

- Which `NDArray` layouts can be converted to libtorch tensors without copy?
- Should interop use DLPack, stable ABI C shims, direct C++ wrapper shims, or staged support for all?
- Where does ownership live when Simple and libtorch both reference the same memory?
- Which APIs belong in `std.ndarray` backend dispatch versus a future `std.ml` tensor/autograd layer?

Outputs:

- Libtorch binding strategy.
- Tensor ownership and lifetime rules.
- Copy versus zero-copy matrix.
- Autograd boundary decision record.
- Packaging and ABI compatibility policy for optional libtorch availability.
- Interop test plan covering Simple-owned, libtorch-owned, copied, and shared buffers.

Acceptance criteria:

- Core ndarray/scipy/DataFrame correctness does not depend on libtorch.
- Autograd scope is excluded from backend dispatch unless a separate `std.ml` requirement selects it.
- Zero-copy paths have lifetime tests before being exposed as stable API.

## Local Research Checklist

Complete these repository-facing tasks before drafting final requirements:

- Map existing ndarray/linalg/scipy/DataFrame functions that are pure scalar loops and classify them by dtype, shape, layout, mutability, and allocation behavior.
- Identify current backend-related code and tests, including mock BLAS routing and any runtime/native build hooks.
- Review compiler/runtime support for native shims, CPU feature detection, dynamic symbol loading, and platform-specific package layout.
- Record hot request/startup paths affected by backend selection, especially MCP/LSP package smoke requirements when `src/lib` or runtime packaging changes.
- Inventory existing SSpec patterns for optional-environment tests so CUDA/libtorch absence reports cleanly.

## Domain Research Checklist

Complete these external-reference tasks before implementation:

- SIMD: LLVM vectorizer behavior, platform feature detection, fallback dispatch patterns, alignment requirements, and benchmark methodology.
- CUDA: CUDA runtime API, stream/event semantics, cuBLAS/cuSOLVER status mapping, memory ownership, and version compatibility.
- PyTorch/libtorch: C++ API stability, stable ABI limits, DLPack ownership rules, tensor stride/layout behavior, and package distribution costs.
- Packaging: how optional native dependencies should be discovered without slowing default startup or making release artifacts non-portable.
- Verification: common practices for optional accelerator CI gates and performance regression reporting on unavailable hardware.

## Risk Register

| Risk | Affected backend | Mitigation |
| --- | --- | --- |
| Backend dispatch hides host/device copies. | CUDA, PyTorch | Require explicit transfer APIs and dispatch traces. |
| Optional native dependency breaks default install. | CUDA, PyTorch, OpenBLAS | Load symbols lazily and keep scalar backend mandatory. |
| SIMD is slower on small arrays. | SIMD | Require measured thresholds and scalar fallback. |
| Zero-copy tensor interop causes use-after-free. | PyTorch | Require ownership matrix and lifetime tests before stable API. |
| Async API blocks on device synchronization. | CUDA, PyTorch | Mark blocking points or return explicit handles. |
| Backend errors erase domain errors. | All | Preserve domain errors and wrap only backend-specific failures. |

## Requirement Options To Draft Later

### SIMD Feature Options

| Option | Description | Pros | Cons | Effort |
| --- | --- | --- | --- | --- |
| SIMD-A | Explicit backend for a short list of contiguous F64/F32 ndarray kernels. | Lowest risk, easy scalar parity, directly useful for science core. | Leaves compiler-wide auto-SIMD for later. | M |
| SIMD-B | Compiler-recognized vector idioms plus ndarray backend kernels. | Broader payoff beyond science lib. | Touches compiler, runtime, and library at once. | XL |
| SIMD-C | Rely on LLVM auto-vectorization first, add diagnostics only. | Minimal code. | Weak guarantees and harder user-visible performance promises. | S |

### CUDA Feature Options

| Option | Description | Pros | Cons | Effort |
| --- | --- | --- | --- | --- |
| CUDA-A | Dense linalg only: explicit device arrays, copy, dot, gemm, solve. | Matches highest-value operations and keeps surface bounded. | Elementwise GPU arrays remain limited. | L |
| CUDA-B | Full ndarray device backend plus BLAS/LAPACK. | More coherent device model. | Larger runtime and verification scope. | XL |
| CUDA-C | cuBLAS/cuSOLVER through host arrays only. | Fastest to expose acceleration. | Hides copies and risks misleading async behavior. | M |

### PyTorch Feature Options

| Option | Description | Pros | Cons | Effort |
| --- | --- | --- | --- | --- |
| TORCH-A | Optional libtorch backend for selected tensor kernels, no autograd. | Useful acceleration and interop without ML framework scope creep. | Requires careful ABI and packaging policy. | L |
| TORCH-B | Full tensor/autograd layer under `std.ml`. | Strong ML story. | Much larger API and lifetime surface. | XL |
| TORCH-C | DLPack import/export only. | Enables ecosystem interop with limited risk. | Does not accelerate Simple operations directly. | M |

## NFR Options To Draft Later

| Option | Description | Pros | Cons | Effort |
| --- | --- | --- | --- | --- |
| NFR-A | Correctness-first: scalar parity required, perf budgets recorded but not release-blocking. | Good for initial backend landing. | May allow slow first backend. | S |
| NFR-B | Perf-gated: require measured speedups for representative large fixtures. | Prevents fake acceleration. | More hardware-sensitive and harder in CI. | M |
| NFR-C | Production-gated: warm startup, latency, max RSS, and backend availability diagnostics are release-blocking. | Best release quality. | Requires stable benchmark infrastructure. | L |

## Research Completion Gate

Before implementation starts, produce:

- `doc/01_research/local/science_math_backend_extensions.md`
- `doc/01_research/domain/science_math_backend_extensions.md`
- `doc/02_requirements/feature/science_math_backend_extensions_options.md`
- `doc/02_requirements/nfr/science_math_backend_extensions_options.md`
- `doc/03_plan/sys_test/science_math_backend_extensions.md`
- Backend-specific benchmark fixture notes under `doc/03_plan/perf/` if the selected NFRs require performance gates.

The user must select final feature and NFR options before implementation. Unchosen options should be deleted when final requirements are written.

Implementation must not begin until final selected requirements exist at:

- `doc/02_requirements/feature/science_math_backend_extensions.md`
- `doc/02_requirements/nfr/science_math_backend_extensions.md`
