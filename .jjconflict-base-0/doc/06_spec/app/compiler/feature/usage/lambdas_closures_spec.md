# Lambdas and Closures Specification

Lambdas (anonymous functions) and closures enable functional programming patterns.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #2300 |
| Category | Language |
| Status | Implemented |
| Source | `test/feature/usage/lambdas_closures_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

Lambdas (anonymous functions) and closures enable functional programming patterns.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Lambda | Anonymous function defined inline with `\` syntax |
| Closure | Function that captures variables from enclosing scope |
| Higher-Order Function | Function taking or returning other functions |

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/lambdas_closures/result.json` |

## Scenarios

- creates simple lambda
- creates lambda with multiple params
- creates lambda with no params
- invokes lambda immediately
- captures outer variable
- captures multiple variables
- nested lambda calls
- maps with lambda
- filters with lambda
- reduces with lambda
- lambda returning lambda
- lambda as function parameter
- lambda with conditional
