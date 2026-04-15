# Implicit Multiplication Specification

Implicit multiplication in m{} math blocks:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #2240-2245 |
| Category | Syntax |
| Status | Implemented |
| Source | `test/feature/usage/implicit_mul_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

Implicit multiplication in m{} math blocks:
- `2x` → `2 * x`
- `2(x+1)` → `2 * (x+1)`
- `(a)(b)` → `(a) * (b)`
- `(x+1)y` → `(x+1) * y`

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/implicit_mul/result.json` |

## Scenarios

- treats 2x as 2*x
- treats 3y as 3*y
- works with floats
- treats 2(x+1) as 2*(x+1)
- works in complex expressions
- treats (a)(b) as (a)*(b)
- chains multiple groups
- treats (x+1)y as (x+1)*y
- computes quadratic with implicit mul
- computes polynomial
- mixes explicit and implicit mul
- handles scientific notation style
- multiplies coefficient and matrix
- works in linear algebra
- implicit mul has same precedence as explicit
- power binds tighter
- does NOT allow implicit mul outside m{}
- preserves function call syntax
- handles negative coefficient
- handles subtraction vs negative
- works without spaces
- works with spaces
