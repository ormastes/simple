# Design: Coverage System Tests

**Status:** Draft
**Requirements:** [doc/requirement/coverage_system_tests.md](../plan/requirement/coverage_system_tests.md)
**Plan:** [doc/03_plan/coverage_system_tests.md](../plan/coverage_system_tests.md)

---

## Test File Organization

All test files live under `test/system/coverage/`. Each file targets one or
more source files from the coverage subsystem.

```
test/system/coverage/
  coverage_core_spec.spl          # coverage.spl (core)
  coverage_build_spec.spl         # build/coverage.spl
  coverage_runner_spec.spl        # test_runner_coverage.spl
  coverage_check_api_spec.spl     # coverage.spl (check) + io + ffi
  coverage_doc_stats_spec.spl     # statistics.spl
  coverage_stats_types_spec.spl   # stats/types.spl
```

## Import Paths

Each test file imports its subject via the canonical `use` path:

| Test File | Import |
|-----------|--------|
| `coverage_core_spec.spl` | `use compiler.tools.coverage` |
| `coverage_build_spec.spl` | `use compiler.driver.build.coverage` |
| `coverage_runner_spec.spl` | `use std.test_runner.test_runner_coverage` |
| `coverage_check_api_spec.spl` | `use std.coverage` |
| `coverage_doc_stats_spec.spl` | `use app.doc.public_check.statistics` |
| `coverage_stats_types_spec.spl` | `use compiler.tools.stats.types` |

All tests additionally import:
```simple
use std.spec.SSpec
```

## Testing Strategy for Private Functions

Private functions (prefixed with `_` or declared without `pub`) cannot be
imported directly. The strategy is **indirect testing through the public API**:

1. Identify every private function in the source file.
2. Determine which public function calls the private one.
3. Write tests against the public function with inputs crafted to exercise the
   private function's branches.
4. If a private function is unreachable from any public API, flag it for
   removal (dead code).

Example: `_load_coverage_data` (private) is called by
`CoverageRunner.collect()` (public). Tests call `collect()` with a path to a
fixture file and assert the loaded data matches expectations.

## Handling FFI-Dependent Tests

Three files involve FFI calls that only work in compiled mode:

- `src/lib/nogc_sync_mut/io/coverage_simple.spl` -- runtime counter FFI
- `src/lib/nogc_sync_mut/ffi/coverage.spl` -- native coverage declarations
- `src/lib/nogc_sync_mut/test_runner/test_runner_coverage.spl` -- file I/O

**Approach:**

1. Group FFI-dependent tests in a dedicated `describe "FFI integration"` block.
2. At the top of that block, check `std.runtime.is_compiled()`. If false,
   print a skip notice and return early.
3. Non-FFI tests (pure struct construction, parsing, stat computation) run in
   both interpreter and compiled modes.

This ensures `bin/simple test` in interpreter mode still runs the majority of
tests while FFI integration is validated in compiled mode and CI.

## Name Collision Avoidance

Three distinct types share the name `CoverageStats`:

| Type | Module | Role |
|------|--------|------|
| `CoverageStats` | `compiler.tools.coverage` | Core stats (lines, branches, functions) |
| `CoverageStats` | `compiler.tools.stats.types` | Stats-subsystem stats (doc coverage, etc.) |
| `CoverageStats` | `std.coverage` | Public API stats (simplified view) |

Two types share the name `CoverageResult`:

| Type | Module | Role |
|------|--------|------|
| `CoverageResult` | `compiler.tools.coverage` | Detailed per-file result |
| `CoverageResult` | `std.test_runner.test_runner_coverage` | Runner-level result |

**Resolution:** Use qualified imports in any test file that needs more than one
variant:

```simple
use compiler.tools.coverage as core_cov
use compiler.tools.stats.types as stats_types
use std.coverage as check_cov

# Access as core_cov.CoverageStats, stats_types.CoverageStats, etc.
```

Each of the 6 test files only imports the module it tests, so collisions only
arise if a test must compare values across modules. In that case, use the
qualified alias pattern above.

## Describe/It Structure Convention

Each test file follows this structure:

```simple
describe "CoverageCollector":
    describe "construction":
        it "initializes with empty counters":
            # REQ-COV-001
    describe "collect":
        it "records line hits from instrumented code":
            # REQ-COV-002
        it "returns empty stats for uninstrumented file":
            # REQ-COV-003 (branch: no data)
    describe "stats":
        it "computes line coverage percentage":
            # REQ-COV-002, REQ-COV-004 (post-stub-fix)
```

This mirrors the source file's public API and satisfies REQ-COV-005 (living
documentation).

## Fixture Data

Test fixture files live in `test/system/coverage/fixtures/`:

- `sample_lcov.info` -- minimal lcov-format coverage data
- `sample_simple.cov` -- simple-coverage internal format
- `empty.cov` -- empty file for edge-case testing
- `corrupt.cov` -- malformed data for error-path testing

Fixtures are read via `std.fs.read_text()` in compiled-mode tests.
