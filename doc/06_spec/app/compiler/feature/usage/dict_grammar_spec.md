# Dictionary Grammar and Syntax Specification

Tests for dictionary literal syntax, ensuring correct grammar is used.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #1002, #1018 |
| Category | Language, Syntax |
| Status | Complete |
| Source | `test/feature/usage/dict_grammar_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

Tests for dictionary literal syntax, ensuring correct grammar is used.
Verifies that {"key": value} syntax works correctly.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/dict_grammar/result.json` |

## Scenarios

- creates dict with string keys
- creates dict with integer values
- creates dict with mixed value types
- creates nested dicts
- creates empty dict
- stores arrays as values
- stores nested structures
- inserts new key-value pair
- updates existing value
- checks key existence
- gets keys
- gets values
- stores optional values
- uses optional chaining with dict access
- returns nil for missing key with ?
- annotates string to int dict
- annotates string to string dict
- annotates complex value types
