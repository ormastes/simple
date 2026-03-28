# Placeholder Lambda Expressions

**Feature ID:** #SYNTAX-009 | **Category:** Syntax | **Status:** Active

_Source: `test/feature/usage/placeholder_lambda_spec.spl`_

---

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
# Filter with comparison placeholder
val evens = [1, 2, 3, 4, 5].filter(_ % 2 == 0)   # => [2, 4, 6]

# Map with arithmetic placeholder
val doubled = [1, 2, 3].map(_ * 10)                # => [10, 20, 30]

# Unary negation placeholder
val negated = [1, 2, 3].map(-_)                    # => [-1, -2, -3]

# Method call on placeholder
val long = ["hi", "hello", "hey"].filter(_.len() > 3)  # => ["hello"]

# Chained placeholders
val result = [1, 2, 3, 4, 5].filter(_ > 2).map(_ * 2)  # => [6, 8, 10]
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Placeholder `_` | Each `_` in an expression becomes a new auto-named lambda parameter |
| Desugaring | `_ op expr` is rewritten to `\__pN: __pN op expr` before evaluation |
| Method access | `_.method()` desugars to `\__p0: __p0.method()` for member calls |
| Chaining | Successive `.filter(_)` and `.map(_)` calls each introduce independent lambdas |

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 22 |

## Test Structure

### Placeholder Lambda

#### filter with comparison

- ✅ filters with less than
- ✅ filters with greater than
- ✅ filters with less than or equal
- ✅ filters with greater than or equal
- ✅ filters with equality
- ✅ filters with not equal
#### map with arithmetic

- ✅ maps with multiply
- ✅ maps with add
- ✅ maps with subtract
- ✅ maps with negate
#### chaining

- ✅ chains filter then map
- ✅ chains map then filter
#### string operations

- ✅ filters strings by length
#### complex expressions

- ✅ uses placeholder in modulo
- ✅ uses placeholder in compound expression
#### with different collection methods

- ✅ works with any
- ✅ works with all
- ✅ works with all returning false
#### empty collections

- ✅ filter on empty returns empty
- ✅ map on empty returns empty
#### single element

- ✅ filter matching single element
- ✅ filter non-matching single element

