# Implicit Multiplication Specification

**Feature ID:** #2240-2245 | **Category:** Syntax | **Status:** Implemented

_Source: `test/feature/usage/implicit_mul_spec.spl`_

---

use std.text.{NL}

Implicit multiplication in m{} math blocks:
- `2x` → `2 * x`
- `2(x+1)` → `2 * (x+1)`
- `(a)(b)` → `(a) * (b)`
- `(x+1)y` → `(x+1) * y`

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 22 |

## Test Structure

### Implicit Multiplication in m{}

#### number followed by identifier

- ✅ treats 2x as 2*x
- ✅ treats 3y as 3*y
- ✅ works with floats
#### number followed by parentheses

- ✅ treats 2(x+1) as 2*(x+1)
- ✅ works in complex expressions
#### parentheses followed by parentheses

- ✅ treats (a)(b) as (a)*(b)
- ✅ chains multiple groups
#### parentheses followed by identifier

- ✅ treats (x+1)y as (x+1)*y
#### complex expressions

- ✅ computes quadratic with implicit mul
- ✅ computes polynomial
- ✅ mixes explicit and implicit mul
- ✅ handles scientific notation style
#### matrix expressions

- ✅ multiplies coefficient and matrix
- ✅ works in linear algebra
#### precedence

- ✅ implicit mul has same precedence as explicit
- ✅ power binds tighter
#### outside m{} blocks

- ✅ does NOT allow implicit mul outside m{}
### Implicit Multiplication Edge Cases

#### function calls are NOT implicit mul

- ✅ preserves function call syntax
#### negative numbers

- ✅ handles negative coefficient
- ✅ handles subtraction vs negative
#### whitespace

- ✅ works without spaces
- ✅ works with spaces

