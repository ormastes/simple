# Requirements: Coverage System Tests

**Status:** Draft
**Related:** [Plan](../plan/coverage_system_tests.md) | [Design](../design/coverage_system_tests.md)

---

## Scope

Define requirements for comprehensive SPipe test coverage of the 8 source files
that compose the coverage measurement subsystem.

## Source Files Under Test

| # | Path | Role |
|---|------|------|
| 1 | `src/compiler/90.tools/coverage.spl` | Core coverage data structures and algorithms |
| 2 | `src/compiler/80.driver/build/coverage.spl` | Build-system integration for coverage passes |
| 3 | `src/lib/nogc_sync_mut/test_runner/test_runner_coverage.spl` | Test-runner coverage collection and reporting |
| 4 | `src/lib/nogc_sync_mut/coverage.spl` | Public check API for coverage queries |
| 5 | `src/lib/nogc_sync_mut/io/coverage_simple.spl` | Runtime FFI bridge for coverage counters |
| 6 | `src/lib/nogc_sync_mut/ffi/coverage.spl` | Minimal FFI declarations for native coverage |
| 7 | `src/app/doc/public_check/statistics.spl` | Documentation statistics aggregation |
| 8 | `src/compiler/90.tools/stats/types.spl` | Stats type definitions shared across tools |

---

## Requirements

### REQ-COV-001: Struct/Class Construction Tests

Every public `struct` or `class` exported by the 8 source files listed above
must have at least one SPipe test that exercises its constructor. The test must
verify that all fields are initialized to their documented defaults or to
explicitly provided values.

**Acceptance:** For each public struct/class, a corresponding `describe` block
exists whose first `it` creates an instance and asserts field values with
`to_equal`.

### REQ-COV-002: Method/Function Happy-Path Tests

Every public `fn` or `me` method in the 8 source files must have at least one
test that invokes it with valid inputs and asserts the expected return value or
observable side-effect.

**Acceptance:** Each public function appears as the subject of at least one `it`
block with a passing assertion.

### REQ-COV-003: Branch Coverage Tests

Every branch point (`if`/`else`, `match` arm, guard clause, early `return`) in
the 8 source files must have tests that exercise each arm. Where exhaustive
testing is impractical, a justification comment must appear in the test file.

**Acceptance:** Each conditional has tests for the true and false paths (or all
match arms). Guard-clause early returns have a test that triggers the guard.

### REQ-COV-004: Stub Remediation

Three known stubs must be replaced with working implementations before tests
can fully pass:

1. **`CoverageCollector.stats`** -- returns placeholder data; must compute real
   aggregated statistics from collected counters.
2. **`_load_coverage_data`** -- no-op; must load serialized coverage data from
   the file path provided.
3. **`parse_coverage_stats`** -- returns empty result; must parse the
   line/branch/function stats from the raw coverage text format.

**Acceptance:** Each stub is replaced with a working implementation that passes
its corresponding SPipe tests without `pass_todo`.

### REQ-COV-005: Tests as Living Documentation

Test names must follow the pattern `"<subject> <verb>s <observable behavior>"`
(e.g., `"CoverageCollector merges overlapping regions"`). Describe blocks must
mirror the source file's public API structure.

**Acceptance:** All `it` and `describe` strings are human-readable sentences
that a new contributor can use to understand the coverage subsystem without
reading source code.

---

## Traceability

| Requirement | Plan Phase | Design Section |
|-------------|-----------|----------------|
| REQ-COV-001 | Phase 6+9 | Test File Organization |
| REQ-COV-002 | Phase 6+9 | Testing Strategy |
| REQ-COV-003 | Phase 6+9 | Branch Coverage Strategy |
| REQ-COV-004 | Phase 8 | Stub Remediation |
| REQ-COV-005 | Phase 6+9 | Naming Conventions |
