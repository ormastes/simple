# Null Coalescing and Try Operator Parser Specification

Tests for the `??` (null coalescing) and `?` (try) operators in various contexts. These operators should work correctly in:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PARSER-NULL-001 |
| Category | Parser / Operators |
| Difficulty | 3/5 |
| Status | In Progress |
| Source | `test/feature/usage/null_coalescing_try_operator_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Tests for the `??` (null coalescing) and `?` (try) operators in various contexts.
These operators should work correctly in:
- Simple expressions
- Return statements
- For loop bodies
- If expression bodies
- Match arms

## Known Issues

The following patterns cause parse errors:
1. `val x = expr ?? return Err(...)` - "expected expression, found Return"
2. `val x = expr?` inside for loop body - may cause issues
3. `val x = if cond: Some(fn()?) else: None` - "expected identifier, found Val"

## Workarounds

Use explicit if/else or match instead of operators in these contexts.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/null_coalescing_try_operator/result.json` |

## Scenarios

- returns left value when present
- returns right value when None
- chains multiple coalescing
- evaluates right side lazily
- calls right side when None
- unwraps Ok value
- propagates Err
- unwraps Some value
- propagates None
- explicit if/else instead of ?? return
- match instead of ? in for loop
- explicit match for optional config
- ? in if-expression body
- ? in for loop with Result
- ?? return Err pattern
