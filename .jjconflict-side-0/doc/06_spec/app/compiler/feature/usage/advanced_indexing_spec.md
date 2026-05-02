# Advanced Indexing and Slicing Specification

Tests for advanced indexing features including:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #1015, #1016, #1017 |
| Category | Language, Collections |
| Status | Complete |
| Source | `test/feature/usage/advanced_indexing_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

Tests for advanced indexing features including:
- Negative indexing (Python-style -1, -2, etc.)
- Slice operations with start:end:step syntax
- String slicing
- Multi-dimensional indexing

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/advanced_indexing/result.json` |

## Scenarios

- accesses last element with -1
- accesses second-to-last with -2
- accesses first element with negative index
- works with strings
- negative indexing with single element
- slices with start and end
- slices from beginning
- slices to end
- slices with step
- reverses with negative step
- slices with start:end:step
- empty slice
- slices substring
- slices from end
- slices middle
- reverses string
- handles UTF-8 characters
- slices with negative start
- slices with negative end
- slices with both negative
- negative indices in string slice
