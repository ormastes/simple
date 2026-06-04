# Agent Task File: scilib_port_claude_sonnet_single_agent

**Owner model:** Claude Sonnet, single agent
**Mode:** Sequential implementation, no parallel subagents
**Date:** 2026-05-18
**Status:** Completed — parallel pipeline ran 2026-05-18. Implementation committed a7e0cd9c2b (36 files, 4392 insertions).

## Purpose

Aggregate the existing scilib/science math plans into one executable task order
for a single Claude Sonnet agent. This is a routing and execution plan, not a
replacement for the detailed area plans.

Canonical design source:

- `doc/05_design/scilib_port_architecture.md`

Detailed task sources:

- `doc/03_plan/agent_tasks/scilib_port_perf_sugar.md`
- `doc/03_plan/agent_tasks/scilib_port_ndarray.md`
- `doc/03_plan/agent_tasks/scilib_port_blas.md`
- `doc/03_plan/agent_tasks/scilib_port_lapack.md`
- `doc/03_plan/agent_tasks/scilib_port_cuda_fortran.md`
- `doc/03_plan/agent_tasks/scilib_port_math_block.md`
- `doc/03_plan/agent_tasks/scilib_port_df.md`
- `doc/03_plan/agent_tasks/scilib_port_ml.md`

Supporting research:

- `doc/01_research/scilib_fortran_port/01_fortran_cuda_abi.md`
- `doc/01_research/scilib_fortran_port/02_python_api_surface.md`
- `doc/01_research/scilib_fortran_port/03_math_block_lowering.md`
- `doc/01_research/scilib_fortran_port/04_naming_harmony.md`
- `doc/01_research/scilib_fortran_port/05_perf_sugar_wedges.md`
- `doc/01_research/scilib_fortran_port/06_codex_risk_assessment.md`

Older umbrella context:

- `doc/02_requirements/feature/science_math_lib_set.md`
- `doc/02_requirements/nfr/science_math_lib_set.md`
- `doc/04_architecture/lib/science_math_lib_set.md`
- `doc/05_design/science_math_lib_set.md`

Do not use `doc/03_plan/agent_tasks/science_math_lib_set.md` as the
implementation-driving plan. It is research/design routing only.

## Scope Boundary

This task is not "full SciPy parity." The first deliverable is a stable
Simple-native scientific core with provider-backed acceleration:

1. Core numeric allocation and typed-array perf sugar.
2. NDArray, Vector, Matrix, Shape, Index, and dtype semantics.
3. BLAS provider boundary for common dense operations.
4. LAPACK provider boundary for solve/factorization wrappers.
5. CUDA/Fortran provider shims after CPU semantics and mocks are stable.
6. Math-block lowering and dataframe/ML consumers only after the numeric core
   is stable.

Out of scope for this single-agent pass:

- broad SciPy API parity,
- cuSOLVER-wide coverage,
- native CUDA kernels for every NDArray op,
- PyTorch zero-copy/DLPack integration,
- advanced sparse nD broadcasting,
- high-risk special functions such as hypergeometric or spheroidal functions.

## Global Execution Rules

The agent must work in this exact order:

```text
perf_sugar -> ndarray -> blas -> lapack -> cuda_fortran -> math_block -> df -> ml
```

Hard gates:

- Do not start NDArray until `T-PERFSUGAR-01` is fixed and verified.
- Do not start BLAS/LAPACK until NDArray core types compile and tests pass.
- Do not wire CUDA/Fortran real backends until BLAS/LAPACK mock and CPU paths
  pass.
- Do not wire math-block, dataframe, or ML consumers until BLAS/LAPACK public
  APIs are stable.

Provider policy:

- CPU/mock provider is mandatory.
- OpenBLAS/LAPACKE provider is optional but preferred.
- CUDA/cuBLAS/cuSOLVER provider is optional and must be opt-in.
- Fortran libraries must be called through explicit C-compatible wrappers.
- Do not silently transfer arrays between CPU and GPU.
- Start with LP64 BLAS/LAPACK integer ABI. Document ILP64 as a later extension.

## Worktree Safety

Before editing:

```bash
jj status
```

Do not modify unrelated dirty files. If unrelated files are present, leave them
untouched and mention them in the final report.

Use `apply_patch`-style edits. Do not rewrite generated/vendor files.

## Phase 0: Plan Reconciliation

Goal: ensure the agent understands current plan hierarchy and does not create a
second incompatible scilib plan.

Tasks:

1. Read `doc/05_design/scilib_port_architecture.md`.
2. Read each `doc/03_plan/agent_tasks/scilib_port_*.md`.
3. Read the six `doc/01_research/scilib_fortran_port/*.md` files.
4. Inspect `test/03_system/feature/scilib/` to map existing spec names to plan phases.
5. Produce a short local note in the final response only; do not create another
   architecture doc unless a contradiction is found.

Exit criteria:

- Agent can list the current gate order.
- Agent can identify which specs belong to each phase.
- Agent has not overwritten older umbrella docs.

## Phase 1: PERF-SUGAR-001

Goal: fix typed floating-array allocation/perf sugar blocker.

Primary plan:

- `doc/03_plan/agent_tasks/scilib_port_perf_sugar.md`

Expected ownership:

- typed array allocation helpers,
- runtime/extern surface for `rt_f64_array_alloc`,
- bootstrap rebuild if the plan requires it,
- focused tests for allocation, length, data preservation, and failure paths.

Tasks:

1. Locate current typed-array allocation code and failing tests.
2. Implement the smallest fix that makes `rt_f64_array_alloc` usable by NDArray.
3. Add or repair tests that prove allocation, indexing, and cleanup behavior.
4. Run the targeted check/test commands from the perf-sugar task plan.
5. Record any unresolved perf issue as a concrete bug under `doc/bugs/`.

Exit criteria:

- `T-PERFSUGAR-01` is marked done only after tests pass.
- No BLAS/LAPACK files are edited in this phase.

## Phase 2: NDArray Core

Goal: implement the common data model for all later scilib work.

Primary plan:

- `doc/03_plan/agent_tasks/scilib_port_ndarray.md`

Required API concepts:

- `NDArray<T>`
- `Vector<T>`
- `Matrix<T>`
- `Shape`
- `Index`
- dtype metadata
- shape/stride rules
- row-major public default
- explicit conversion for provider column-major calls

Tasks:

1. Implement construction, shape, stride, indexing, slicing, concat/stack, and
   reductions in the order specified by the NDArray task plan.
2. Keep dtype promotion explicit and documented in tests.
3. Add error paths for rank mismatch, shape mismatch, out-of-bounds access, and
   unsupported dtype.
4. Run all NDArray specs under `test/03_system/feature/scilib/ndarray_*_spec.spl`.

Exit criteria:

- NDArray tests pass in interpreter mode.
- Public API is stable enough for BLAS/LAPACK wrapper inputs.

## Phase 3: BLAS Provider Boundary

Goal: expose dense linear algebra operations through a provider boundary rather
than reimplementing all BLAS first.

Primary plan:

- `doc/03_plan/agent_tasks/scilib_port_blas.md`

First operation set:

- `axpy`
- `dot`
- `nrm2`
- `scal`
- `gemv`
- `gemm`

Tasks:

1. Implement mock CPU provider first.
2. Implement provider handle and diagnostics.
3. Implement row-major public wrappers and column-major provider conversion.
4. Add OpenBLAS/CBLAS boundary only after mock tests pass.
5. Keep cuBLAS naming and symbol plans aligned with CUDA/Fortran phase.

Required tests:

- `test/03_system/feature/scilib/blas_axpy_spec.spl`
- `test/03_system/feature/scilib/blas_gemm_spec.spl`
- `test/03_system/feature/scilib/linalg_backend_diagnostics_spec.spl`
- `test/03_system/feature/scilib/linalg_openblas_backend_spec.spl` when backend exists

Exit criteria:

- Mock path is green.
- Backend diagnostics clearly report unavailable native providers.
- No CUDA requirement for baseline pass.

## Phase 4: LAPACK Provider Boundary

Goal: add solve/factorization wrappers on top of NDArray and BLAS handles.

Primary plan:

- `doc/03_plan/agent_tasks/scilib_port_lapack.md`

First operation set:

- `gesv`
- `getrf`
- `getri`
- `inv`
- `solve`
- defer broad `syevd`, `gesvd`, and `geqrf` until the first solve/factorization
  path is stable.

Tasks:

1. Implement typed `LinalgError`, `LapackInfo`, pivot, and workspace wrappers.
2. Implement mock path for deterministic tests.
3. Add LAPACKE boundary after mock and NDArray tests pass.
4. Keep row-major/column-major conversion shared with BLAS helpers.
5. Add clear failure behavior for singular matrices and invalid shapes.

Required tests:

- `test/03_system/feature/scilib/lapack_gesv_spec.spl`
- `test/03_system/feature/scilib/lapack_inv_spec.spl`
- `test/03_system/feature/scilib/lapack_det_spec.spl`
- `test/03_system/feature/scilib/linalg_norm_spec.spl`

Exit criteria:

- `solve` and `inv` behavior is covered by real assertions.
- LAPACK backend absence produces a typed error, not a silent fallback mismatch.

## Phase 5: CUDA/Fortran Provider Shims

Goal: add optional accelerated providers without changing CPU semantics.

Primary plan:

- `doc/03_plan/agent_tasks/scilib_port_cuda_fortran.md`

Tasks:

1. Implement provider selection: mock -> CPU/OpenBLAS/LAPACKE -> CUDA when
   explicitly selected.
2. Keep Fortran calls behind C-compatible wrappers.
3. Add ABI tests for symbol naming, argument widths, and row/column-major
   conversion.
4. Add CUDA device-buffer and backend diagnostics tests.
5. Mark hardware tests as optional and skip-safe when no CUDA runtime exists.

Required tests:

- `test/03_system/feature/scilib/cuda_device_buffer_spec.spl`
- `test/03_system/feature/scilib/linalg_cuda_backend_spec.spl`
- existing CUDA unit/integration tests under `test/01_unit/lib/extended/`

Exit criteria:

- CPU/mock tests pass without CUDA.
- CUDA tests either pass on CUDA hosts or report a clear skip/unavailable state.
- No silent host/device transfer.

## Phase 6: Math Block Lowering

Goal: route math-block syntax and higher-level expressions through the stable
NDArray/BLAS/LAPACK APIs.

Primary plan:

- `doc/01_research/scilib_fortran_port/03_math_block_lowering.md`
- any existing `scilib_port_math_block.md`

Tasks:

1. Lower matmul to BLAS `gemm` only when shapes and dtypes are supported.
2. Lower `solve`/`inv` to LAPACK only after Phase 4 is stable.
3. Preserve scalar fallback or typed diagnostic for unsupported expressions.
4. Run `test/03_system/feature/scilib/math_block_matmul_spec.spl`.

Exit criteria:

- math-block lowering does not duplicate BLAS/LAPACK logic.
- Unsupported math-block forms fail with typed diagnostics.

## Phase 7: DataFrame And ML Consumers

Goal: consume the numeric core without making dataframe/ML own linear algebra.

Primary plans:

- `doc/03_plan/agent_tasks/scilib_port_df.md`
- `doc/03_plan/agent_tasks/scilib_port_ml.md`

Tasks:

1. Wire dataframe operations to NDArray where applicable.
2. Keep dataframe sorting/groupby/merge independent from BLAS/LAPACK.
3. Wire ML linear models to `linalg.solve` or `linalg.gesv`.
4. Run dataframe and ML-related scilib feature specs.

Exit criteria:

- dataframe code does not duplicate NDArray indexing/reduction logic.
- ML code does not implement its own solver.

## Verification Matrix

Always run after the related phase changes:

```bash
bin/simple check src/lib src/compiler
bin/simple test test/03_system/feature/scilib/ndarray_create_spec.spl --mode=interpreter --clean
bin/simple test test/03_system/feature/scilib/blas_axpy_spec.spl --mode=interpreter --clean
bin/simple test test/03_system/feature/scilib/blas_gemm_spec.spl --mode=interpreter --clean
bin/simple test test/03_system/feature/scilib/lapack_gesv_spec.spl --mode=interpreter --clean
bin/simple test test/03_system/feature/scilib/lapack_inv_spec.spl --mode=interpreter --clean
bin/simple test test/03_system/feature/scilib/linalg_backend_diagnostics_spec.spl --mode=interpreter --clean
bin/simple test test/05_perf/scilib_simd_ops_perf_spec.spl --mode=interpreter --clean
```

Hardware/provider tests:

```bash
bin/simple test test/03_system/feature/scilib/linalg_openblas_backend_spec.spl --mode=interpreter --clean
bin/simple test test/03_system/feature/scilib/linalg_cuda_backend_spec.spl --mode=interpreter --clean
bin/simple test test/03_system/feature/scilib/cuda_device_buffer_spec.spl --mode=interpreter --clean
```

Provider tests must be skip-safe or clearly unavailable on machines without the
native provider.

## Claude Sonnet Final Report Format

The single agent final report must include:

- phase completed,
- files changed,
- tests run with pass/fail counts,
- gates still closed,
- provider availability on the current machine,
- known deviations from SciPy/NumPy behavior,
- next exact task ID from the relevant `scilib_port_*` plan.

## Known Risks

- SciPy-scale API surface is too large for one pass.
- BLAS/LAPACK ABI width mismatch can corrupt calls; start LP64 only.
- Fortran ABI varies by compiler; use C wrappers.
- GPU backend support must be opt-in; avoid silent device transfers.
- Special functions have high precision risk; defer broad coverage.
- Sparse arrays should prioritize COO/CSR/CSC and avoid legacy matrix semantics.
