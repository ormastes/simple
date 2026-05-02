# Placeholder Lambda Expressions

Placeholder lambdas let the programmer write concise anonymous functions by using `_` as a stand-in for each successive parameter. The compiler desugars `_ * 2` into `\__p0: __p0 * 2` and `_ + _` into `\__p0, __p1: __p0 + __p1`. This spec covers the full surface area: comparison operators, arithmetic (including unary negation), method access on the placeholder (`_.len()`), chaining of `filter` and `map`, compound expressions like `_ * 2 + 1`, and quantifier methods (`any`, `all`). Edge cases for empty and single-element collections are also tested.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SYNTAX-009 |
| Category | Syntax |
| Status | Active |
| Source | `test/feature/usage/placeholder_lambda_spec.spl` |
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

## Overview

Placeholder lambdas let the programmer write concise anonymous functions by using
`_` as a stand-in for each successive parameter. The compiler desugars `_ * 2`
into `\__p0: __p0 * 2` and `_ + _` into `\__p0, __p1: __p0 + __p1`. This spec
covers the full surface area: comparison operators, arithmetic (including unary
negation), method access on the placeholder (`_.len()`), chaining of `filter` and
`map`, compound expressions like `_ * 2 + 1`, and quantifier methods (`any`,
`all`). Edge cases for empty and single-element collections are also tested.

## Syntax

```simple
val evens = [1, 2, 3, 4, 5].filter(_ % 2 == 0)   # => [2, 4, 6]

val doubled = [1, 2, 3].map(_ * 10)                # => [10, 20, 30]

val negated = [1, 2, 3].map(-_)                    # => [-1, -2, -3]

val long = ["hi", "hello", "hey"].filter(_.len() > 3)  # => ["hello"]

val result = [1, 2, 3, 4, 5].filter(_ > 2).map(_ * 2)  # => [6, 8, 10]
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Placeholder `_` | Each `_` in an expression becomes a new auto-named lambda parameter |
| Desugaring | `_ op expr` is rewritten to `\__pN: __pN op expr` before evaluation |
| Method access | `_.method()` desugars to `\__p0: __p0.method()` for member calls |
| Chaining | Successive `.filter(_)` and `.map(_)` calls each introduce independent lambdas |

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/placeholder_lambda/result.json` |

## Scenarios

- filters with less than
- filters with greater than
- filters with less than or equal
- filters with greater than or equal
- filters with equality
- filters with not equal
- maps with multiply
- maps with add
- maps with subtract
- maps with negate
- chains filter then map
- chains map then filter
- filters strings by length
- uses placeholder in modulo
- uses placeholder in compound expression
- works with any
- works with all
- works with all returning false
- filter on empty returns empty
- map on empty returns empty
- filter matching single element
- filter non-matching single element
