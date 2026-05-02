# Reference Counted Pointers Specification

Reference counted pointers provide safe sharing of data with automatic

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SHARED-PTR |
| Category | Runtime |
| Status | Implemented |
| Source | `test/feature/usage/shared_pointers_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

Reference counted pointers provide safe sharing of data with automatic
memory management through reference counting.

## Key Behaviors

- Reference count incremented on clone, decremented on drop
- Value is deallocated when reference count reaches zero
- Cloning creates shallow copy with incremented reference count

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/shared_pointers/result.json` |

## Scenarios

- creates pointer
- pointer arithmetic
- multiple references
- tracks multiple references
- clones underlying data
- dict references work correctly
- data remains valid while referenced
- strings are valid
- nested data structures work
