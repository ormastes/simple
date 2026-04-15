# Dictionary Types Specification

Tests for dictionary (map) types and their operations.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #1002 |
| Category | Language |
| Status | In Progress |
| Source | `test/feature/usage/dictionary_types_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

Tests for dictionary (map) types and their operations.
Verifies dictionary creation, access, modification, and iteration.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/dictionary_types/result.json` |

## Scenarios

- creates empty dictionary
- creates dictionary with initial values
- creates dictionary with string keys and values
- retrieves value by key
- returns null for missing key
- checks key existence
- adds new key-value pair
- updates existing value
- removes entry by key
- iterates over keys
- iterates over values
- iterates over entries
- gets dictionary size
- checks if dictionary is empty
- clears dictionary
- creates copy of dictionary
- stores different value types
- accesses values with correct types
- sets key with functional update
- merges two dictionaries
- gets value or default
- gets existing value instead of default
- creates dict from comprehension
