# Duplicate Check Regression System Specification

| Field | Value |
|---|---|
| Feature IDs | #DUPCHECK-CLI-REG, #DUPCHECK-NOISE-REG, #DUPCHECK-INCR-REG, #DUPCHECK-SEM-REG |
| Category | Tooling \| Compiler |
| Status | Implemented |
| Plan | `doc/03_plan/sys_test/duplicate_check_regression.md` |
| Executable Spec | `test/system/duplicate_check/duplicate_check_regression_system_spec.spl` |

## Objective

Protect the duplicate-check refactor against regressions in the executable user path and the refactored formatter and semantic reporting seams.

## Required Behaviors

1. The duplicate-check CLI must scan a directory and surface grouped duplicates in text mode.
2. Low-signal boilerplate must not be promoted into cosine similarity duplicate groups.
3. Incremental cache entries must remain reusable for unchanged files and invalidate after file changes.
4. Semantic analysis must degrade to text-based similarity when the Ollama endpoint is unavailable.

## Pass Criteria

- The system spec completes with all assertions passing.
- CLI and semantic fallback cases run through the real duplicate-check entrypoint.
- Incremental assertions operate on a real on-disk cache file and real file mtimes.
