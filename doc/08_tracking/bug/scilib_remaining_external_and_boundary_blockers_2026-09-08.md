# SciLib remaining boundary and external-host blockers

Status: active

Owner: SciLib maintainer
Reviewer: compiler/runtime maintainer

This record is the actionable handoff for acceptance rows which cannot honestly
be closed by the current macOS lane. A plan checkbox remains open until its
listed proof succeeds; this record is not completion evidence.

## ML public primitive boundary

- Gap: eight shipped public helpers in `src/lib/common/science_math/ml_{linear,metrics}.spl`
  expose `[f64]`/`f64`; the old acceptance scan omitted this source root.
- Prerequisite: select one canonical ML value/vector wrapper without breaking
  the existing public import surface.
- Resume: migrate those signatures and both `ml_*_spec.spl` copies, then run
  `src/compiler_rust/target/debug/simple test test/03_system/feature/scilib/ml_linear_spec.spl`
  and `ml_metrics_spec.spl`, followed by the ML plan acceptance spec.
- Retained artifact: corrected full-scope audit in
  `test/03_system/plan_acceptance/scilib_port_ml_spec.spl`.

## LAPACK typed boundary, workspace, and CPU CI

- Gap: Layer B still exposes primitive buffers/dimensions; `Workspace` is not
  driven by a backend buffer-size query; no protected CPU CI receipt proves the
  real LAPACKE path. PERF-SUGAR-011 remains `anticipated`.
- Prerequisite: agree on the Layer-B typed buffer carrier and add buffer-size
  entry points to every backend before replacing the current direct algorithms.
- Resume: implement the carrier/query lifecycle, run
  `sh scripts/check/check-scilib-runtime-shims.shs` on a Linux OpenBLAS host,
  then measure wrapper construction and promote PERF-SUGAR-011 only from data.
- Retained artifact: strengthened behavioral LAPACK acceptance spec, including
  real Singular and deterministic NotConverged paths.

## CUDA build and CI receipt

- Gap: this Darwin host has no `nvcc`; a CUDA >= 11.7 `_64` build and cuda-host
  CI receipt cannot be manufactured locally. Setup/bootstrap/test-runner and
  the requested three-leg CI matrix also remain unwired.
- Prerequisite: a maintained Linux CUDA >= 11.7 runner plus the CI owner’s
  runner labels and secret policy.
- Resume: on that runner execute
  `sh scripts/check/check-scilib-runtime-shims.shs`, build
  `src/runtime/scilib/{cublas,cusolver}_shim.c`, run
  `src/runtime/scilib/verify_symbols.shs` against mock/openblas/CUDA artifacts,
  and retain `nvcc --version`, symbol diff, smoke output, and max-RSS receipts.
- Retained artifact: C shim sources and the symbol verifier. The local gate now
  calls the shipped `.shs` verifier name instead of the nonexistent `.sh` path.

