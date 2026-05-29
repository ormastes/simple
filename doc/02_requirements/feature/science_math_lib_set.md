<!-- codex-requirements -->
# Science Math Lib Set Feature Requirements

**Date:** 2026-05-05
**Status:** User-selected phased sequence.
**Selection:** A -> B -> C -> D.
**Research:** `doc/01_research/local/science_math_lib_set.md`, `doc/01_research/domain/science_math_lib_set.md`
**Design:** `doc/04_architecture/science_math_lib_set.md`, `doc/05_design/science_math_lib_set.md`

## Phase A: Scalar Science Core

- **REQ-SCILIB-A-001:** Provide a portable scalar baseline for `std.ndarray` with constructors, dtype metadata, shape/stride metadata, indexing, slicing, broadcasting, ufuncs, reductions, concat/stack, sort, random basics, and CSV/text I/O.
- **REQ-SCILIB-A-002:** Provide scalar/mock `std.linalg` operations for dot, axpy, gemv, gemm, norm, trace, solve, inv, and det over `NDArray`.
- **REQ-SCILIB-A-003:** Provide scalar `std.scipy.*` modules for stats, integrate, optimize, special, interpolate, signal, sparse, and spatial APIs over `NDArray`.
- **REQ-SCILIB-A-004:** Provide `std.df` `Series` and `DataFrame` support for typed numeric columns, missing masks, filtering, indexing, sorting, concat, groupby, joins, and CSV/text I/O.
- **REQ-SCILIB-A-005:** Keep SIMD, CUDA, OpenBLAS, and PyTorch optional. The scalar core must remain correct without those dependencies.

## Phase B: Scalar Core Plus Host BLAS

- **REQ-SCILIB-B-001:** Add an OpenBLAS/LAPACKE host backend behind the existing public linalg APIs without changing scalar public signatures.
- **REQ-SCILIB-B-002:** Preserve scalar fallback when OpenBLAS/LAPACKE is unavailable, incompatible, or unsupported for the requested dtype/layout.
- **REQ-SCILIB-B-003:** Add backend parity tests comparing scalar/mock and OpenBLAS/LAPACKE results on deterministic dense linalg fixtures.
- **REQ-SCILIB-B-004:** Report host backend availability and symbol-loading failures through typed backend errors, not panics or silent fallback.

## Phase C: Full Backend Acceleration Slice

- **REQ-SCILIB-C-001:** Add SIMD backend support for selected contiguous CPU F64/F32 ndarray and linalg hot loops.
- **REQ-SCILIB-C-002:** Add CUDA backend support for explicit device buffers, transfer APIs, dense linalg kernels, and GPU-only verification.
- **REQ-SCILIB-C-003:** Add PyTorch/libtorch backend support as an optional tensor/kernel adapter without making libtorch required for core correctness.
- **REQ-SCILIB-C-004:** Ensure accelerated backends preserve scalar semantics and fail cleanly when unavailable.
- **REQ-SCILIB-C-005:** Avoid hidden host/device copies for mutating CUDA operations unless the API explicitly requests a transfer.

## Phase D: Data Analysis Expansion

- **REQ-SCILIB-D-001:** Expand DataFrame compatibility after scalar ndarray/linalg semantics are stable.
- **REQ-SCILIB-D-002:** Prioritize joins, groupby, missing values, CSV/text I/O, indexing, sorting, concat, and reshape-style workflows.
- **REQ-SCILIB-D-003:** Keep DataFrame operations out of `math{}` and `m{}` expression semantics.
- **REQ-SCILIB-D-004:** Maintain a compatibility manifest for pandas-style behavior before broadening the surface beyond numeric columns.

## Out Of Scope Until Separately Selected

- Full upstream NumPy, SciPy, pandas, or PyTorch replacement compatibility.
- Direct Fortran source ingestion or Fortran-mangled symbol binding.
- Autograd and neural-network APIs in the core science namespace.
