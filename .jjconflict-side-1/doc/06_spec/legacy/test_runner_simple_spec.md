# Test Runner Simple Specification

*Source: `test/unit/app/tooling/test_runner_simple_spec.spl`*
*Last Updated: 2026-03-29*

---

## Overview

Documentation was generated from executable SSpec scenarios.

## Evidence

### Artifacts

- build/test-artifacts/unit/app/tooling/test_runner_simple/summary.txt

### Logs

- build/test-artifacts/unit/app/tooling/test_runner_simple/output.log

## Test Summary

| Metric | Count |
|--------|-------|
| Scenarios | 64 |
| Slow Scenarios | 0 |
| Skipped Scenarios | 0 |

## Scenarios

- defaults to test/ path when no path given
- parses --mode smf flag
- parses --mode=native equals syntax
- parses --timeout flag with seconds
- parses --fail-fast flag
- parses --only-slow flag
- parses --only-skipped flag
- parses --seed flag
- parses --list-ignored flag
- parses --safe-mode flag
- parses --force-rebuild flag
- parses --keep-artifacts flag
- parses --all flag
- parses --doc format flag
- parses --format doc flag
- parses --list-skip-features flag
- parses --planned-only flag
- identifies spec files by _spec. pattern
- identifies test files by _test. pattern
- rejects non-spl files
- filters unit tests by excluding integration and system paths
- filters integration tests by path
- filters system tests by path
- extracts passed count from examples line
- handles zero failures
- falls back to exit code when no output parsed
- marks non-zero exit as failure when no output parsed
- tracks skipped count separately
- writes summaries under build/test-artifacts
- writes safe-mode subprocess output to output.log
- converts seconds to milliseconds
- detects timeout by exit_code -1
- normal exit code is not timeout
- env var name is SIMPLE_TEST_RUNNER_RUST
- guard value is 1
- Rust runner detects guard and skips Simple dispatch
- falls back for --watch flag
- falls back for --parallel flag
- falls back for --json flag
- does not fall back for --doc flag
- does not fall back for --list flag
- does not fall back for --seed flag
- does not fall back for --list-skip-features
- interpreter mode runs file directly
- SMF mode compiles then runs .smf
- native mode compiles then runs binary
- hash produces consistent result for same input
- different seeds produce different hashes
- default format shows PASS prefix
- default format shows FAIL prefix
- default format shows TOUT prefix for timeout
- doc format shows basename only
- sets SIMPLE_TEST_MODE for interpreter
- sets SIMPLE_TEST_MODE for smf
- sets SIMPLE_TEST_FILTER for slow
- sets SIMPLE_TEST_FILTER for skipped
- sets SIMPLE_TEST_SHOW_TAGS to 1
- extracts feature IDs from file header
- extracts category from file header
- extracts status from file header
- planned-only filters by status
- run record contains pass and fail counts
- run record uses microsecond timestamp as run_id
- run record status is completed
