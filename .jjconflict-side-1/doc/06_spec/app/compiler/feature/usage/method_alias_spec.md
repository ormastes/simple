# Method Alias Forwarding Specification

Tests that `alias fn` and `alias me` in class bodies desugar into correct forwarding methods. The desugar transforms: `alias fn len = inner.len`       -> `fn len(): self.inner.len()` `alias fn push(item) = inner.push` -> `fn push(item): self.inner.push(item)` `alias me increment = inner.increment` -> `me increment(): self.inner.increment()`

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #FWD-002 |
| Category | Syntax |
| Difficulty | 3/5 |
| Status | In Progress |
| Source | `test/feature/usage/method_alias_spec.spl` |
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

Tests that `alias fn` and `alias me` in class bodies desugar into
correct forwarding methods. The desugar transforms:
`alias fn len = inner.len`       -> `fn len(): self.inner.len()`
`alias fn push(item) = inner.push` -> `fn push(item): self.inner.push(item)`
`alias me increment = inner.increment` -> `me increment(): self.inner.increment()`

These tests verify the generated delegation patterns work correctly
by writing the equivalent hand-expanded code.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/method_alias/result.json` |

## Scenarios

- forwards no-arg method
- forwards method with argument
- forwards zero value correctly
- forwards no-arg mutable method
- forwards mutable method with argument
- chains multiple mutable forwards
- reads after mutation reflect changes
