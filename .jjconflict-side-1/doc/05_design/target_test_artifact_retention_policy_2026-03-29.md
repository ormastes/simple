<!-- codex-design -->
# Target/Test Artifact Cleanup and Retention Policy

Date: 2026-03-29
Owner: Task 7
Scope: local generated test evidence under `target/` and build/test byproducts that are directly adjacent to the test runner.

## Summary

This repo already has a stable artifact namespace for non-image test evidence:

- `build/test-artifacts/<spec-relative-path>/`
- `build/test-artifacts/<spec-relative-path>/scenarios/...`
- `build/coverage/`
- `build/artifacts/`
- `build/bootstrap/`

What is missing is a retention rule that distinguishes:

- ephemeral local evidence
- local debug artifacts intentionally kept by opt-in flags
- CI handoff artifacts needed only between jobs
- release artifacts that are meant to survive longer

The policy below keeps the existing paths, avoids churn in the current runner implementation, and sets clear ownership for future cleanup commands.

## Current State

### Observed local artifact writers

- Rust test runner writes per-spec evidence to `build/test-artifacts/`:
  - `src/compiler_rust/driver/src/cli/test_runner/artifact.rs`
  - `src/compiler_rust/driver/src/cli/test_runner/execution.rs`
- Rust test runner plans per-scenario evidence under `build/test-artifacts/.../scenarios/`:
  - `src/compiler_rust/driver/src/cli/test_runner/scenario_artifacts.rs`
- Simple test runner keeps temporary coverage wrappers only unless `--keep-artifacts` is set:
  - `src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl`
  - `src/lib/nogc_sync_mut/test_runner/test_runner_args.spl`
- Coverage output is written under `build/coverage/`:
  - `src/lib/nogc_sync_mut/test_runner/test_runner_coverage.spl`
  - `src/compiler/80.driver/build/coverage.spl`
- Build/bootstrap intermediates live under `build/artifacts/` and `build/bootstrap/`:
  - `src/compiler/70.backend/build_native_pipeline.spl`
  - `src/compiler/80.driver/build/bootstrap.spl`
  - `src/compiler/80.driver/build/orchestrator.spl`

### Observed CI artifact classes

- Job-to-job handoff artifacts: 1 to 3 days
- General build/test artifacts: 7 to 14 days
- Dashboard and FreeBSD build artifacts: 30 days
- T32 tool release artifacts: 90 days

Primary workflow touch points:

- `.github/workflows/test-isolation.yml`
- `.github/workflows/containerized-tests.yml`
- `.github/workflows/build-binaries.yml`
- `.github/workflows/release.yml`
- `.github/workflows/t32-tools-build.yml`
- `.github/workflows/t32-tools-release.yml`
- `.github/workflows/dashboard-ci.yml`
- `.github/workflows/freebsd-build.yml`

## Policy

### 1. Canonical local evidence roots

Use these roots only:

- `build/test-artifacts/` for per-spec and per-scenario test evidence
- `build/coverage/` for coverage summaries, baselines, and reports
- `build/artifacts/` for native-build intermediates
- `build/bootstrap/` for bootstrap stage outputs

Do not create new ad hoc top-level test output directories.

### 2. Default local retention

Default local retention is ephemeral:

- never commit `build/test-artifacts/`
- never commit `build/coverage/`
- never commit `build/artifacts/`
- never commit `build/bootstrap/`
- overwrite per-spec evidence in place on subsequent runs
- keep per-scenario directories only for the current spec run

Rationale: these trees are execution evidence, not source assets.

### 3. Opt-in debug retention

`--keep-artifacts` remains the only valid opt-in for keeping otherwise temporary runner outputs.

Policy for `--keep-artifacts`:

- allowed for local debugging only
- should preserve generated wrappers and intermediate files for the current run
- must not change artifact root layout
- should not be enabled by default in CI

### 4. Cleanup ownership

Cleanup responsibility should be split by producer:

- test runner owns `build/test-artifacts/`
- coverage commands own `build/coverage/`
- native build owns `build/artifacts/`
- bootstrap pipeline owns `build/bootstrap/`
- CI workflows own uploaded GitHub Actions artifacts

This avoids one cleanup command silently deleting another subsystem's retained evidence.

### 5. Recommended cleanup behavior

Near-term target behavior:

- `simple test`:
  - leaves `build/test-artifacts/` in place for the latest run
  - removes temporary wrappers unless `--keep-artifacts`
- future `simple test --clean-artifacts`:
  - deletes `build/test-artifacts/`
  - deletes test-runner temporary wrappers/checkpoints
- `simple build clean`:
  - deletes `build/coverage/`
  - deletes `build/artifacts/`
  - deletes `build/bootstrap/`
  - should not delete curated docs under `doc/spec/`

No change is required to the current artifact path schema to adopt this behavior.

### 6. CI retention classes

Use only these retention classes:

- 1 day:
  - job handoff artifacts
  - bootstrap seeds
  - container/test isolation pass-through bundles
- 7 days:
  - ordinary CI debug bundles
  - failing test logs needed for short investigation
- 14 days:
  - cross-platform validation outputs that may need a second pass
- 30 days:
  - milestone or dashboard artifacts that humans inspect outside the immediate CI run
- 90 days:
  - release-channel deliverables only

Avoid mixing release retention with routine test evidence in the same workflow.

## Exact Repo Touch Points

### Local writer paths that must keep using the canonical roots

- `src/compiler_rust/driver/src/cli/test_runner/artifact.rs`
- `src/compiler_rust/driver/src/cli/test_runner/scenario_artifacts.rs`
- `src/compiler_rust/driver/src/cli/test_runner/execution.rs`
- `src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl`
- `src/lib/nogc_sync_mut/test_runner/test_runner_coverage.spl`
- `src/compiler/80.driver/build/coverage.spl`
- `src/compiler/80.driver/build/bootstrap.spl`
- `src/compiler/70.backend/build_native_pipeline.spl`

### CLI and config surfaces that should describe retention behavior

- `src/compiler_rust/driver/src/cli/test_runner/args.rs`
- `src/compiler_rust/driver/src/cli/test_runner/types.rs`
- `src/lib/nogc_sync_mut/test_runner/test_runner_args.spl`
- `src/lib/nogc_sync_mut/test_runner/test_runner_types.spl`
- `src/lib/nogc_sync_mut/test_runner/main.spl`

### Documentation surfaces

- `doc/07_guide/testing/testing.md`
- `test/unit/app/tooling/evidence_layout_spec.spl`

### CI surfaces for later normalization

- `.github/workflows/test-isolation.yml`
- `.github/workflows/containerized-tests.yml`
- `.github/workflows/build-binaries.yml`
- `.github/workflows/release.yml`
- `.github/workflows/t32-tools-build.yml`
- `.github/workflows/t32-tools-release.yml`
- `.github/workflows/dashboard-ci.yml`
- `.github/workflows/freebsd-build.yml`

## Immediate Low-Risk Changes

These are safe now without changing runner semantics:

1. Keep Jujutsu ignore rules aligned with Git ignores for generated build/test trees.
2. Add this design note so future cleanup work has one concrete source of truth.

## Recommended Follow-Up

1. Add `simple test --clean-artifacts` that deletes `build/test-artifacts/` only.
2. Extend `simple build clean` to explicitly remove `build/coverage/`, `build/artifacts/`, and `build/bootstrap/` if any producer currently leaves them behind.
3. Normalize CI retention days to the five classes above and remove one-off values where they do not reflect release intent.
