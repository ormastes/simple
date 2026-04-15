# Database Resource Specification

## At a Glance

| Field | Value |
|-------|-------|
| Source | `test/feature/app/database_resource_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Documentation was generated from executable SSpec scenarios.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/app/database_resource/result.json` |

## Scenarios

- returns empty list for new database
- returns stats for empty database
- returns error for non-existent bug
- adds bug via JSON
- retrieves added bug
- updates bug status
- fails to add bug without id
- gets open bugs only
- gets critical bugs only
- calculates correct stats
- returns empty list for new database
- returns stats for empty database
- adds feature via JSON
- retrieves added feature
- updates feature status
- gets features by category
- gets features by status
- returns empty list for new database
- returns stats for empty database
- starts a test run
- ends a test run
- records test result
- returns empty flaky tests for new database
- returns empty slow tests for new database
- database operations are atomic
- escapes special characters in JSON
- handles empty strings
