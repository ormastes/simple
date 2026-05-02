# HashMap Basic Operations Specification

System tests for basic HashMap operations through the FFI layer.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Stdlib |
| Status | Implemented |
| Source | `test/feature/usage/hashmap_basic_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

System tests for basic HashMap operations through the FFI layer.
Tests creation, insertion, retrieval, and collection operations.

## Integration Scope

HashMap + Collections FFI

## Complexity

Low

## Coverage Impact

hashmap.rs (0%→40%), collections FFI

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/hashmap_basic/result.json` |

## Scenarios

- creates new HashMap
- inserts and retrieves values
- handles multiple insertions
- checks if key exists
- removes keys
- gets all keys
- clears all entries
- gets all values
