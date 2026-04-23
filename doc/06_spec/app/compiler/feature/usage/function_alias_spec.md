# Function Alias (Deprecated Delegation)

Tests the deprecated `fn name = target` function alias syntax that the desugar pipeline transforms into explicit delegation. Validates basic alias calling, return value preservation for text and integer types, alias chaining (alias of alias), and that original functions remain callable alongside their aliases.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #FWD-001 |
| Category | Syntax |
| Status | Active |
| Source | `test/feature/usage/function_alias_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Tests the deprecated `fn name = target` function alias syntax that the desugar
pipeline transforms into explicit delegation. Validates basic alias calling,
return value preservation for text and integer types, alias chaining (alias of
alias), and that original functions remain callable alongside their aliases.

## Syntax

```simple
fn sum(a: i64, b: i64) -> i64:
add(a, b)
val result = sum(3, 4)  # calls add(3, 4) via delegation
```
Function Alias Specification

Feature IDs: #FWD-001
Category: Syntax
Difficulty: 2/5
Status: DEPRECATED - use explicit delegation instead

The `fn name = target` syntax is deprecated. The desugar pipeline
transforms it into explicit delegation: `fn name(params): target(params)`.
This test verifies the delegation pattern works correctly.

Example (deprecated):  fn println = print
Preferred:             fn println(msg: text): print(msg)

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/function_alias/result.json` |

## Scenarios

- calls target function
- works with zero arguments
- works with negative arguments
- preserves return value for text
- preserves return value for integer
- alias of alias works
- intermediate alias also works
- original still works
- alias and original return same result
- void alias is callable
