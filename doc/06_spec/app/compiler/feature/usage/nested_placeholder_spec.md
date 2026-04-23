# Nested Placeholder Scoping

Tests that placeholder lambdas in nested call arguments maintain independent scoping at each nesting level. Verifies that inner and outer placeholders are independent, chained placeholders with nested any/all/filter work correctly, map with nested filter preserves scope, deeply nested chaining, string method placeholders, and edge cases like empty inner lists.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Language Features |
| Status | In Progress |
| Source | `test/feature/usage/nested_placeholder_spec.spl` |
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

## Overview

Tests that placeholder lambdas in nested call arguments maintain independent scoping at
each nesting level. Verifies that inner and outer placeholders are independent, chained
placeholders with nested any/all/filter work correctly, map with nested filter preserves
scope, deeply nested chaining, string method placeholders, and edge cases like empty
inner lists.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/nested_placeholder/result.json` |

## Scenarios

- scopes inner and outer placeholders independently
- filters arrays that have all elements above threshold
- chains outer filter with inner any
- maps then filters within nested context
- outer placeholder is independent of inner
- chained operations maintain separate scopes
- handles three levels of nesting via chaining
- filters strings containing substrings
- nested placeholder on empty inner list
