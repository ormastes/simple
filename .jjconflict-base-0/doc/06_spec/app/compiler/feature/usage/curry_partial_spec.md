# Curry Partial Specification

Curry and Partial Application

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #FUNC-010 |
| Category | Functional Programming |
| Status | Active |
| Source | `test/feature/usage/curry_partial_spec.spl` |
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

Curry and Partial Application

Standard library functions for currying and partial application.
`curry2(f)` converts a 2-arg function into nested single-arg lambdas.
`partial1(f, a)` fixes the first argument of a 2-arg function.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/curry_partial/result.json` |

## Scenarios

- curries a two-argument function
- curries multiply
- applies both arguments
- curries a three-argument function
- partial application of curry3
- fixes first argument
- creates increment function
- works with map
- fixes first two arguments
- fixes different values
