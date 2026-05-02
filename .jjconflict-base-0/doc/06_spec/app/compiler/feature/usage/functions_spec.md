# Function Definitions Specification

Tests for function definition and invocation.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #1004 |
| Category | Language |
| Status | In Progress |
| Source | `test/feature/usage/functions_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

Tests for function definition and invocation.
Verifies function parameters, return types, implicit returns, and various calling patterns.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/functions/result.json` |

## Scenarios

- defines function with explicit return type
- uses implicit return of last expression
- calls function with no parameters
- passes multiple parameters
- uses type inference for parameters
- uses named arguments
- returns single value
- returns early with explicit return
- returns without explicit type annotation
- executes function with side effects
- calls function multiple times
- accepts function parameter
- uses lambda function
- returns function
- defines generic function
- uses generic with constraints
- uses multiple type parameters
- defines recursive factorial function
- uses tail recursion
