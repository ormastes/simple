<!-- codex-requirements -->
# Science Math Lib Set NFR Requirements

**Date:** 2026-05-05
**Status:** User-selected phased sequence.
**Selection:** NFR-A -> NFR-B -> NFR-C -> NFR-D.
**Research:** `doc/01_research/local/science_math_lib_set.md`, `doc/01_research/domain/science_math_lib_set.md`
**Design:** `doc/04_architecture/science_math_lib_set.md`, `doc/05_design/science_math_lib_set.md`

## Phase NFR-A: Portable Correctness Baseline

- **NFR-SCILIB-A-001:** Default verification must run on developer and CI machines without requiring OpenBLAS, CUDA, PyTorch/libtorch, or SIMD-specific hardware.
- **NFR-SCILIB-A-002:** Scalar science-lib feature specs must run in interpreter mode with deterministic mock backend behavior.
- **NFR-SCILIB-A-003:** Every public scalar API requirement must have real assertions and at least one error-path assertion where invalid input is possible.
- **NFR-SCILIB-A-004:** Placeholder specs, `pass_todo`, skipped examples, and always-true assertions are not acceptable for completed science-lib requirements.
- **NFR-SCILIB-A-005:** Optional acceleration work must not weaken scalar semantics or make scalar correctness depend on native dependencies.

## Phase NFR-B: Host Performance Baseline

- **NFR-SCILIB-B-001:** Host BLAS/LAPACK work must include warm startup, representative operation latency, and max RSS evidence on fixed dense linalg fixtures.
- **NFR-SCILIB-B-002:** OpenBLAS/LAPACKE backend verification must compare against scalar/mock results on deterministic fixtures.
- **NFR-SCILIB-B-003:** Performance thresholds must be machine-tolerant and documented with fixture sizes, backend name, and runtime environment.
- **NFR-SCILIB-B-004:** Host backend setup failures must report typed unavailable or missing-symbol diagnostics without failing scalar default verification.

## Phase NFR-C: Accelerator Readiness Baseline

- **NFR-SCILIB-C-001:** SIMD, CUDA, and PyTorch/libtorch backends must expose backend-unavailable diagnostics that are non-fatal on machines lacking the backend.
- **NFR-SCILIB-C-002:** Accelerated backends must share parity fixtures with scalar/mock paths wherever semantics overlap.
- **NFR-SCILIB-C-003:** CUDA and PyTorch paths must document ownership and transfer behavior before zero-copy or device mutation APIs are stabilized.
- **NFR-SCILIB-C-004:** CUDA mutating operations must include no-hidden-copy checks before release.
- **NFR-SCILIB-C-005:** Optional accelerator verification must be opt-in and availability-gated until dedicated hardware/runtime CI exists.

## Phase NFR-D: Full Accelerator Performance Gates

- **NFR-SCILIB-D-001:** SIMD, CUDA, OpenBLAS, and PyTorch paths must each define hard latency and RSS budgets before being called release-ready.
- **NFR-SCILIB-D-002:** Accelerator performance evidence must use realistic fixtures and include scalar fallback comparison.
- **NFR-SCILIB-D-003:** CUDA and PyTorch gates must record synchronization and transfer costs separately from kernel execution where possible.
- **NFR-SCILIB-D-004:** Release readiness for accelerated paths requires either CI coverage or a documented local hardware matrix with repeatable commands.
- **NFR-SCILIB-D-005:** Backend claims must be withdrawn or marked experimental if the corresponding performance and parity gates cannot run.
