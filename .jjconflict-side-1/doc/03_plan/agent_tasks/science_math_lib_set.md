# Agent Task Plan: Science Math Lib Set

**Date:** 2026-05-05
**Status:** Research/design plan only. No implementation assigned by this file.
**Primary docs:** `doc/01_research/local/science_math_lib_set.md`, `doc/01_research/domain/science_math_lib_set.md`, `doc/04_architecture/science_math_lib_set.md`, `doc/05_design/science_math_lib_set.md`.

## Phase 0: Requirement Selection

- Produce final feature requirements and NFRs from this research/design set.
- Decide compatibility target per family: NumPy-core subset, SciPy-domain subset, pandas subset, Fortran-compatible BLAS/LAPACK subset.
- Define "complete" as a staged compatibility manifest, not full upstream replacement in one release.

## Phase 1: Namespace Consistency

- Owner A: `std.ndarray` and `std.linalg` export consistency across `common`, `nogc_async_mut`, and `nogc_sync_mut`.
- Owner B: `std.df` async/nogc facade consistency.
- Owner C: compatibility map from older `common/statistics`, `common/numerical_methods`, and `common/linear_algebra` into the new science namespace plan.

## Phase 2: NumPy Core

- Constructors and dtype/device/layout polish.
- Axis reductions and common ufuncs.
- Concat/stack/sort/random/I/O basics.
- Slicing/indexing/broadcast regression coverage.

## Phase 3: Fortran-Compatible Linalg

- BLAS Layer A/B/C wrappers.
- LAPACK Layer A/B/C wrappers.
- Mock backend computes correct small-N results.
- OpenBLAS/LAPACKE host backend.
- CUDA/cuBLAS/cuSOLVER backend.

## Phase 4: SciPy And Pandas

- SciPy-style stats/optimize/integrate/special/signal/sparse/spatial modules.
- Pandas-style groupby, joins, concat, missing values, CSV/text I/O, and indexing modes.

## Phase 5: Backend Extensions

- SIMD backend: contiguous F64 hot loops and parity tests.
- CUDA backend: runtime shims, device memory, GPU-only tests.
- PyTorch backend: optional libtorch adapter, no core correctness dependency.

## Global Rules

- Keep DataFrame out of math blocks.
- Keep public signatures typed; raw primitives stay inside backend layers.
- Avoid hidden allocation in nogc hot paths.
- Avoid hidden blocking FFI in async APIs.
- Specs must run in interpreter mode with mock backend unless explicitly GPU-only.

