# Enum Types Specification

Tests for enumeration types and pattern matching on enums.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #1003 |
| Category | Language |
| Status | Complete |
| Source | `test/feature/usage/enums_spec.spl` |
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

Tests for enumeration types and pattern matching on enums.
Verifies enum definition, construction, and exhaustive pattern matching.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/enums/result.json` |

## Scenarios

- defines simple enum with variants
- constructs enum variants
- matches on enum variants
- defines enum with tuple variants
- constructs variant with associated values
- extracts values from enum variant
- matches and binds enum values
- requires exhaustive pattern matching
- handles all enum variants in match
- supports wildcard patterns in match
- matches enum in conditional guards
- defines enum with enum variants
- matches nested enum variants
- handles enum with generic variants
- calls methods on enum instances
- implements trait for enum
- enumerates all variants
- creates Option variants
- matches on Option
- creates Result variants
- matches on Result with error handling
