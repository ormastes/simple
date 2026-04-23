# Unit Types Specification

Tests for semantic unit types that add compile-time dimensional safety to numeric values.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #UNIT-001 |
| Category | Language \| Types |
| Status | Implemented |
| Source | `test/feature/usage/unit_types_spec.spl` |
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

## Overview

Tests for semantic unit types that add compile-time dimensional safety
to numeric values.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/unit_types/result.json` |

## Scenarios

- defines standalone unit type
- performs arithmetic with units
- gets value from unit
- gets suffix from unit
- converts unit to string
- defines unit family
- allows same-family addition
- allows same-family subtraction
- allows scaling by scalar
- allows comparison always
- defines compound unit
- computes velocity from division
- cancels same units in division
- defines area from multiplication
- uses kilo prefix
- uses mega prefix
- uses milli prefix
- accepts correct unit parameter
- returns correct unit type
- uses unit wrappers in public function signatures
- supports helper methods on semantic wrapper units
