# Underscore Wildcard Specification

Tests for underscore (_) as a wildcard placeholder in various contexts:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TBD |
| Category | Syntax |
| Status | Implemented |
| Source | `test/feature/usage/underscore_wildcard_spec.spl` |
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

Tests for underscore (_) as a wildcard placeholder in various contexts:
- Lambda parameters: `\_: expr` to ignore arguments
- For loop patterns: `for _ in items:` to iterate without binding
- Match patterns: `case _:` as a catch-all wildcard

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/underscore_wildcard/result.json` |

## Scenarios

- ignores single argument
- works in map to transform values
- iterates without binding
- uses sum_n_times helper
- works with list iteration
- catches unmatched cases
- ignores enum payload
