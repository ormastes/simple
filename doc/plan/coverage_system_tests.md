# Plan: Coverage System Tests

**Status:** Draft
**Requirements:** [doc/requirement/coverage_system_tests.md](requirement/coverage_system_tests.md)
**Design:** [doc/design/coverage_system_tests.md](../design/coverage_system_tests.md)

---

## Goal

Achieve 100% test coverage of the 8 coverage-subsystem source files through
stub remediation, SSpec test creation, and verification.

## Phases

### Phase 8 -- Fix 3 Stubs

**Difficulty:** 4 | **Agent:** opus | **Satisfies:** REQ-COV-004

Fix the three stubs identified in the requirements so that the coverage
subsystem produces real data instead of placeholders.

| # | Stub | File | Action |
|---|------|------|--------|
| 1 | `CoverageCollector.stats` | `src/compiler/90.tools/coverage.spl` | Compute real aggregated statistics from internal counters. Return a populated `CoverageStats` with line, branch, and function counts. |
| 2 | `_load_coverage_data` | `src/lib/nogc_sync_mut/test_runner/test_runner_coverage.spl` | Deserialize coverage data from the file at the given path. Handle missing-file and corrupt-file cases by returning `Result`. |
| 3 | `parse_coverage_stats` | `src/compiler/90.tools/coverage.spl` | Parse raw coverage text into `CoverageStats`. Support the `lcov` and internal simple-coverage formats. |

**Exit criteria:** Each stub has a working implementation. No `pass_todo`
remains in any of the three functions.

### Phase 6+9 -- Create 6 Test Spec Files

**Difficulty:** 3 | **Agent:** sonnet | **Satisfies:** REQ-COV-001, REQ-COV-002, REQ-COV-003, REQ-COV-005

Create the following SSpec test files (see Design doc for file layout):

| # | Test File | Source(s) Covered |
|---|-----------|-------------------|
| 1 | `test/system/coverage/coverage_core_spec.spl` | `src/compiler/90.tools/coverage.spl` |
| 2 | `test/system/coverage/coverage_build_spec.spl` | `src/compiler/80.driver/build/coverage.spl` |
| 3 | `test/system/coverage/coverage_runner_spec.spl` | `src/lib/nogc_sync_mut/test_runner/test_runner_coverage.spl` |
| 4 | `test/system/coverage/coverage_check_api_spec.spl` | `src/lib/nogc_sync_mut/coverage.spl`, `src/lib/nogc_sync_mut/io/coverage_simple.spl`, `src/lib/nogc_sync_mut/ffi/coverage.spl` |
| 5 | `test/system/coverage/coverage_doc_stats_spec.spl` | `src/app/doc/public_check/statistics.spl` |
| 6 | `test/system/coverage/coverage_stats_types_spec.spl` | `src/compiler/90.tools/stats/types.spl` |

Each file must:
- Import the module under test using its canonical `use` path.
- Have `describe` blocks mirroring the public API.
- Name `it` blocks per REQ-COV-005 conventions.
- Cover construction (REQ-COV-001), happy paths (REQ-COV-002), and branches
  (REQ-COV-003).

**Exit criteria:** All 6 files parse without errors. All `it` blocks pass in
compiled mode.

### Phase 10 -- Add Sdoctests to Fixed Stubs

**Difficulty:** 2 | **Agent:** sonnet | **Depends on:** Phase 8

Add inline `sdoctest` examples to each of the 3 remediated stubs so that
`bin/simple test --doctest` validates them on every run.

**Exit criteria:** `bin/simple test --doctest` passes for all 3 functions.

### Phase 14 -- Full Suite Verification

**Difficulty:** 1 | **Agent:** sonnet | **Depends on:** Phase 6+9, Phase 10

Run the complete test suite and verify:

1. All 6 spec files pass (`bin/simple test test/system/coverage/`).
2. No regressions in existing tests (`bin/simple test`).
3. Coverage report shows 100% of public API exercised.

**Exit criteria:** CI-green full test run with coverage report attached.

---

## Dependency Graph

```
Phase 8 (fix stubs)
  |
  v
Phase 10 (sdoctests) ----+
                          |
Phase 6+9 (spec files) ---+---> Phase 14 (verify)
```

## Risk

| Risk | Mitigation |
|------|------------|
| FFI tests require compiled mode | Mark FFI-dependent `it` blocks; skip gracefully in interpreter mode |
| Name collisions (3 `CoverageStats`) | Use qualified imports; see Design doc |
| Stub fix breaks downstream | Run full suite after each stub fix (Phase 8) |
