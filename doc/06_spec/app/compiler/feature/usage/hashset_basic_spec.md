# HashSet Basic Operations

Tests HashSet basic operations using a self-contained implementation. Covers set creation and initialization, element insertion with deduplication, membership testing via contains and remove, collection mutations like clear, and array conversion via to_vec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | In Progress |
| Source | `test/feature/usage/hashset_basic_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Tests HashSet basic operations using a self-contained implementation. Covers set creation
and initialization, element insertion with deduplication, membership testing via contains
and remove, collection mutations like clear, and array conversion via to_vec.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/hashset_basic/result.json` |

## Scenarios

- creates new HashSet
- inserts elements
- handles duplicate insertions
- checks if element exists
- removes elements
- clears all elements
- converts to vector
