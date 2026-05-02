# Math Language Specification

**Feature ID:** #2200-2205 | **Category:** Syntax | **Status:** Implemented

_Source: `test/feature/usage/math_language_spec.spl`_

---

use std.text.{NL}

Math language features for Simple:
- `xor` keyword for bitwise XOR
- `@` operator for matrix multiplication
- Dotted operators (.+, .-, .*, ./, .^) for broadcasting
- `m{}` math blocks with `^` power operator

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 22 |

## Test Structure

### xor Keyword

#### basic operations

- ✅ computes bitwise XOR of two integers
- ✅ returns identity when XOR with 0
- ✅ returns 0 when XOR with itself
#### precedence

- ✅ has lower precedence than and
- ✅ has higher precedence than or
### @ MatMul Operator

#### basic operations

- ✅ parses @ as matrix multiply
#### precedence

- ✅ binds tighter than addition
- ✅ binds looser than multiplication
### Dotted Broadcast Operators

#### .+ broadcast add

- ✅ parses .+ as broadcast add
#### .- broadcast sub

- ✅ parses .- as broadcast sub
#### .* broadcast mul

- ✅ parses .* as broadcast mul
#### ./ broadcast div

- ✅ parses ./ as broadcast div
#### .^ broadcast pow

- ✅ parses .^ as broadcast pow
### m{} Math Blocks

#### power operator inside m{}

- ✅ allows ^ as power inside math block
- ✅ computes quadratic expression
- ✅ handles nested exponentiation
#### complex expressions

- ✅ computes distance formula
- ✅ mixes ^ and ** equivalently
#### nested braces

- ✅ handles nested braces in math block
### Power Operator Behavior

#### ** operator

- ✅ works outside math blocks
- ✅ works inside math blocks
- ✅ is right-associative

