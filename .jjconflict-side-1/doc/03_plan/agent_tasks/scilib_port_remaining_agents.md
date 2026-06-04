# SciLib Port Remaining Agent Plan

**Date:** 2026-05-19
**Status:** Implementation wave completed 2026-05-18 — committed a7e0cd9c2b (36 files, 4392 insertions). All 10 ACs met. Source in src/lib/common/science_math/ + src/lib/nogc_sync_mut/linalg/. Test specs in test/03_system/feature/scilib/.
**Canonical architecture:** `doc/05_design/scilib_port_architecture.md`
**Single-agent routing plan:** `doc/03_plan/agent_tasks/scilib_port_claude_sonnet_single_agent.md`

## Current Remains Summary

**Implementation wave completed 2026-05-18.** All layers in the dependency chain
were implemented and committed at a7e0cd9c2b:

```text
perf_sugar -> ndarray -> blas -> lapack -> cuda_fortran -> math_block -> df -> ml
```

All gates are closed. Individual plan docs updated to reflect implemented status.

## Existing Source Plans

Use these detailed plans instead of creating new parallel plans:

- `doc/03_plan/agent_tasks/scilib_port_perf_sugar.md`
- `doc/03_plan/agent_tasks/scilib_port_ndarray.md`
- `doc/03_plan/agent_tasks/scilib_port_blas.md`
- `doc/03_plan/agent_tasks/scilib_port_lapack.md`
- `doc/03_plan/agent_tasks/scilib_port_cuda_fortran.md`
- `doc/03_plan/agent_tasks/scilib_port_math_block.md`
- `doc/03_plan/agent_tasks/scilib_port_df.md`
- `doc/03_plan/agent_tasks/scilib_port_ml.md`
- `doc/08_tracking/feature_request/scilib_perf_sugar.md`

## Agent A: Perf Sugar Gate

**Priority:** P0
**Detailed plan:** `doc/03_plan/agent_tasks/scilib_port_perf_sugar.md`

### Goal

Close the allocation/performance blockers that every numeric layer inherits.

### Remaining Work

- Fix `PERF-SUGAR-001`: `rt_f64_array_alloc` typed allocation path.
- Verify bootstrap/rebuild requirements from the perf-sugar plan.
- Update `doc/08_tracking/feature_request/scilib_perf_sugar.md` from
  `anticipated` to `observed` or `fixed` for every touched entry.
- Capture any remaining perf gap as a concrete bug, not a loose TODO.

### Exit Tests

```bash
bin/simple test test/03_system/feature/scilib/perf_sugar_spec.spl --mode=interpreter --clean
bin/simple test test/05_perf/scilib_simd_ops_perf_spec.spl --mode=interpreter --clean
```

### Unlocks

- Agent B: NDArray core.

## Agent B: NDArray Core

**Priority:** P0 after Agent A
**Detailed plan:** `doc/03_plan/agent_tasks/scilib_port_ndarray.md`

### Goal

Finish the common array model consumed by BLAS, LAPACK, math-block, dataframe,
and ML layers.

### Remaining Work

- Implement/verify `NDArray<T>`, `Vector<T>`, `Matrix<T>`, `Shape`, `Index`,
  `Stride`, dtype metadata, shape/stride semantics.
- Keep row-major public behavior explicit.
- Provide typed errors for shape mismatch, rank mismatch, unsupported dtype, and
  out-of-bounds access.
- Keep CUDA/device memory out of this phase except for documented provider hooks.

### Exit Tests

```bash
bin/simple test test/03_system/feature/scilib/ndarray_create_spec.spl --mode=interpreter --clean
bin/simple test test/03_system/feature/scilib/ndarray_dtype_spec.spl --mode=interpreter --clean
bin/simple test test/03_system/feature/scilib/ndarray_error_spec.spl --mode=interpreter --clean
bin/simple test test/03_system/feature/scilib/ndarray_shape_ops_spec.spl --mode=interpreter --clean
bin/simple test test/03_system/feature/scilib/ndarray_broadcast_spec.spl --mode=interpreter --clean
bin/simple test test/03_system/feature/scilib/ndarray_reduction_spec.spl --mode=interpreter --clean
```

### Unlocks

- Agent C: BLAS provider boundary.
- Agent D: LAPACK provider boundary, after BLAS shared types are stable.

## Agent C: BLAS Provider Boundary

**Priority:** P1 after Agent B
**Detailed plan:** `doc/03_plan/agent_tasks/scilib_port_blas.md`

### Goal

Implement dense linear algebra through a provider boundary, with mock CPU path
first and native providers optional.

### Remaining Work

- Define shared `LinalgError`, `NormOrd`, `BlasHandle` in the agreed location.
- Implement Layer A extern names with cuBLAS C API naming only; no Fortran
  mangled names in BLAS extern declarations.
- Implement mock backend for interpreter tests.
- Implement typed `Float64` public v1 operations before generic facades.
- Implement row-major public wrappers and column-major provider conversion.
- Add audit comments for `gemv`/`gemm` operand swaps and `idamax` 1-based to
  0-based correction.
- Update `PERF-SUGAR-003` and `PERF-SUGAR-011` status when observed.

### Exit Tests

```bash
SIMPLE_BLAS_BACKEND=mock bin/simple test test/03_system/feature/scilib/blas_axpy_spec.spl --mode=interpreter --clean
SIMPLE_BLAS_BACKEND=mock bin/simple test test/03_system/feature/scilib/blas_gemm_spec.spl --mode=interpreter --clean
SIMPLE_BLAS_BACKEND=mock bin/simple test test/03_system/feature/scilib/linalg_backend_diagnostics_spec.spl --mode=interpreter --clean
```

### Unlocks

- Agent D: LAPACK provider boundary.
- Agent E: CUDA/Fortran shims.

## Agent D: LAPACK Provider Boundary

**Priority:** P1 after Agents B and C
**Detailed plan:** `doc/03_plan/agent_tasks/scilib_port_lapack.md`

### Goal

Add first LAPACK-level wrappers without duplicating BLAS/NDArray ownership.

### Remaining Work

- Implement typed `LapackInfo`, pivot wrappers, workspace wrappers, and error
  mapping.
- Implement `gesv`, `getrf`, `getri`, `inv`, and `solve` first.
- Cover `Singular` and `NotConverged` error paths with real specs.
- Keep `syevd`, `gesvd`, and `geqrf` after the first solve/factorization path.
- Ensure LAPACKE/OpenBLAS provider absence reports a typed unavailable error.
- Promote `PERF-SUGAR-001`, `PERF-SUGAR-003`, and `PERF-SUGAR-011` entries before
  implementation begins where the plan requires it.

### Exit Tests

```bash
SIMPLE_BLAS_BACKEND=mock bin/simple test test/03_system/feature/scilib/lapack_gesv_spec.spl --mode=interpreter --clean
SIMPLE_BLAS_BACKEND=mock bin/simple test test/03_system/feature/scilib/lapack_inv_spec.spl --mode=interpreter --clean
SIMPLE_BLAS_BACKEND=mock bin/simple test test/03_system/feature/scilib/lapack_det_spec.spl --mode=interpreter --clean
bin/simple test test/03_system/feature/scilib/linalg_openblas_backend_spec.spl --mode=interpreter --clean
```

### Unlocks

- Agent F: Math-block linalg.
- Agent H: ML linear model consumers.

## Agent E: CUDA/Fortran Provider Shims

**Priority:** P2 after Agents C and D contracts are stable
**Detailed plan:** `doc/03_plan/agent_tasks/scilib_port_cuda_fortran.md`

### Goal

Provide optional accelerated providers while preserving CPU/mock semantics.

### Remaining Work

- Build/provider-select `libspl_cublas`, `libspl_openblas`,
  `libspl_cublas_mock`.
- Keep Fortran interop behind explicit C-compatible wrappers.
- Add ABI smoke tests for symbol names, integer width, pointer lifetimes, and
  row/column-major conversion.
- Ensure CUDA tests are skip-safe or clearly unavailable on machines without
  CUDA.
- Do not silently transfer arrays between CPU and GPU.

### Exit Tests

```bash
bin/simple test test/03_system/feature/scilib/cuda_provider_smoke_spec.spl --mode=interpreter --clean
bin/simple test test/03_system/feature/scilib/cuda_device_buffer_spec.spl --mode=interpreter --clean
bin/simple test test/03_system/feature/scilib/fortran_abi_smoke_spec.spl --mode=interpreter --clean
bin/simple test test/03_system/feature/scilib/linalg_cuda_backend_spec.spl --mode=interpreter --clean
```

## Agent F: Math Block Linalg

**Priority:** P2 after Agent D
**Detailed plan:** `doc/03_plan/agent_tasks/scilib_port_math_block.md`

### Goal

Route math-block syntax through stable NDArray/BLAS/LAPACK APIs.

### Remaining Work

- Implement parser/evaluator paths for matrix multiplication, indexing/slicing,
  `solve`, and `inv`.
- Ensure `A @ B + c` binds as expected.
- Ensure singular `inv` returns a typed error.
- Implement or delete TODOs; do not convert TODOs to notes.
- Promote `PERF-SUGAR-002` when observed.
- Keep v2 sketch tasks out of v1 implementation.

### Exit Tests

```bash
SIMPLE_BLAS_BACKEND=mock bin/simple test test/03_system/feature/scilib/math_block_matmul_spec.spl --mode=interpreter --clean
SIMPLE_BLAS_BACKEND=mock bin/simple test test/03_system/feature/scilib/math_block_solve_spec.spl --mode=interpreter --clean
```

## Agent G: DataFrame Layer

**Priority:** P2 after Agent B; some tasks after Agent C
**Detailed plan:** `doc/03_plan/agent_tasks/scilib_port_df.md`

### Goal

Finish dataframe/series surface while reusing NDArray semantics where relevant.

### Remaining Work

- Complete construction, column ops, filtering, groupby, merge, pivot, missing
  values, scalar broadcast, value counts, and CSV/text specs.
- Keep `read_parquet` deferred to v2 with a typed error and feature request.
- Track all dataframe perf-sugar annotations in
  `doc/08_tracking/feature_request/scilib_perf_sugar.md`.
- Do not duplicate NDArray indexing/reduction logic.

### Exit Tests

```bash
bin/simple test test/03_system/feature/scilib/df_construction_spec.spl --mode=interpreter --clean
bin/simple test test/03_system/feature/scilib/df_filter_spec.spl --mode=interpreter --clean
bin/simple test test/03_system/feature/scilib/df_groupby_spec.spl --mode=interpreter --clean
bin/simple test test/03_system/feature/scilib/df_merge_spec.spl --mode=interpreter --clean
bin/simple test test/03_system/feature/scilib/df_missing_values_spec.spl --mode=interpreter --clean
bin/simple test test/03_system/feature/scilib/df_value_counts_spec.spl --mode=interpreter --clean
```

## Agent H: ML Consumers

**Priority:** P3 after Agents B, C, and D
**Detailed plan:** `doc/03_plan/agent_tasks/scilib_port_ml.md`

### Goal

Wire ML helpers to the numeric core without implementing private solvers.

### Remaining Work

- Implement linear model consumers on top of `linalg.solve`/`gesv`.
- Implement metrics helpers only after NDArray reductions are stable.
- Avoid independent solver/reduction logic in ML modules.

### Exit Tests

```bash
bin/simple test test/03_system/feature/scilib/ml_linear_spec.spl --mode=interpreter --clean
bin/simple test test/03_system/feature/scilib/ml_metrics_spec.spl --mode=interpreter --clean
```

## Agent I: SciPy-Compatible Facade Triage

**Priority:** P3; do not block core scilib

### Goal

Classify SciPy-like facade specs into v1, v1.1, v2, or deferred.

### Remaining Work

- Keep stable early targets: `stats` basics, `fft` basics, simple optimize root
  finding.
- Keep sparse v1 to COO construction and CSR/CSC matvec/matmul/transpose.
- Defer broad `special`, advanced `optimize`, nD sparse broadcasting, and
  full SciPy parity.
- Mark every unsupported facade with an explicit typed unavailable/deferred
  diagnostic.

### Candidate Tests

```bash
bin/simple test test/03_system/feature/scilib/scipy_stats_spec.spl --mode=interpreter --clean
bin/simple test test/03_system/feature/scilib/scipy_sparse_spec.spl --mode=interpreter --clean
bin/simple test test/03_system/feature/scilib/scipy_optimize_spec.spl --mode=interpreter --clean
bin/simple test test/03_system/feature/scilib/scipy_special_spec.spl --mode=interpreter --clean
```

## Cross-Agent Rules

- No agent may bypass the dependency chain.
- No `skip()` in required v1 specs.
- No TODO-to-NOTE conversion. Implement, defer with typed diagnostic, or file a
  concrete feature request/bug.
- Provider-dependent tests must be explicit about unavailable providers.
- Keep CPU/mock semantics as the source of truth.
- Keep GPU/CUDA and Fortran opt-in.
- Do not silently copy CPU arrays to GPU arrays or vice versa.

## Current Highest-Value Next Assignment

Assign **Agent A: Perf Sugar Gate** first.

Reason: all downstream scilib areas still inherit the `PERF-SUGAR-001`
allocation gate, and several later plans explicitly prohibit implementation
until this is fixed.
