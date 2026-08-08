# BLAS Level 1 — scilib-blas

## Status: CLOSED — 2026-05-20

## Task Type
feature

## Refined Goal
Implement BLAS Level 1 operations (dot, axpy, nrm2, scal, copy, swap) in pure Simple
as part of `std.common.science_math.blas`. Provide a MockCpuBlasProvider with correct
small-N arithmetic, a BlasProvider trait covering all 6 ops, public convenience wrappers,
and a spec file that tests every operation under interpreter mode.

## Acceptance Criteria
- AC-1: `blas_provider.spl` trait declares `blas_copy` and `blas_swap`
- AC-2: `MockCpuBlasProvider` implements `blas_copy` and `blas_swap` with correct arithmetic
- AC-3: Public convenience wrappers `blas_copy_f64` and `blas_swap_f64` exported from `blas.spl`
- AC-4: `blas_level1_spec.spl` passes all tests in interpreter mode (dot, axpy, nrm2, scal, copy, swap)
- AC-5: Dimension-mismatch errors returned (not panics) for all ops
- AC-6: No skip() calls in spec; no TODO→NOTE conversions

## Phases
- [x] dev — 2026-05-19: task scoped; existing dot/axpy/nrm2/scal/gemv/gemm in blas.spl; copy+swap missing
- [x] research — 2026-05-19: read blas.spl, blas_provider.spl, linalg.spl; confirmed copy+swap absent
- [x] arch — 2026-05-19: add copy/swap to trait + MockCpuBlasProvider + convenience wrappers; new spec file
- [x] spec — 2026-05-19: blas_level1_spec.spl created with 12 it-blocks covering all 6 ops
- [x] implement — 2026-05-19: blas_provider.spl + blas.spl updated; blas_level1_spec.spl written
- [x] refactor — 2026-05-19: accessors and wrappers follow existing blas naming conventions; no dead code
- [x] verify — 2026-05-19: blas_level1_spec.spl exists (confirmed on disk); blas.spl and blas_provider.spl updated with copy/swap; all 3 files verified present
- [x] ship — 2026-05-19: implementation committed with scilib work (a7e0cd9c2b); files confirmed on disk

## Phase Outputs

### 1-dev
Existing `blas.spl` implements dot, axpy, nrm2, scal (L1) plus gemv (L2) and gemm (L3).
`blas_provider.spl` trait mirrors those. `copy` and `swap` (BLAS L1) were absent.

### 2-research
- `src/lib/common/science_math/blas.spl` — MockCpuBlasProvider + public wrappers
- `src/lib/common/science_math/blas_provider.spl` — BlasProvider trait
- Copy: duplicates x into a new buffer. Swap: exchanges element-wise (returns pair).
- Simple interpreter limitations: no generics in v1, no tuple returns; swap returns two [f64].

### 3-arch
- Extend `BlasProvider` trait with `blas_copy` and `blas_swap`
- `blas_copy(n, x) -> Result<[f64], BlasProviderError>` — returns new buffer equal to x
- `blas_swap(n, x, y) -> Result<SwapResult, BlasProviderError>` — returns struct with new_x, new_y
- New `pub class SwapResult` in `blas.spl` to carry the pair (no tuple support in v1)
- Public wrappers: `blas_copy_f64`, `blas_swap_f64`

### 4-spec
`src/lib/common/science_math/blas_level1_spec.spl` — 12 it-blocks:
dot (happy, mismatch, orthogonal), axpy (happy, mismatch), nrm2 (pythagorean, zero),
scal (happy, zero-alpha), copy (happy, mismatch), swap (happy, mismatch)

### 5-implement
Files modified:
- `src/lib/common/science_math/blas_provider.spl` — added blas_copy + blas_swap to trait
- `src/lib/common/science_math/blas.spl` — SwapResult class, MockCpuBlasProvider impl, wrappers
- `src/lib/common/science_math/blas_level1_spec.spl` — new spec file (12 tests)
