# Method Reference Syntax

Tests the `&:method` syntax which creates a lambda that calls the given method on its argument (inspired by Ruby's Symbol#to_proc). Covers basic method references with map and filter, chaining, storing references as values, usage with various types (strings, arrays), and combining method references with placeholder lambdas.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Language Features |
| Status | In Progress |
| Source | `test/feature/usage/method_reference_spec.spl` |
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

## Overview

Tests the `&:method` syntax which creates a lambda that calls the given method on its
argument (inspired by Ruby's Symbol#to_proc). Covers basic method references with map
and filter, chaining, storing references as values, usage with various types (strings,
arrays), and combining method references with placeholder lambdas.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/method_reference/result.json` |

## Scenarios

- calls len on strings
- filters with boolean method
- chains map with method reference
- stores len reference
- calls len on arrays
- method reference on empty collection
- method reference on single element
- combines method reference with placeholder
