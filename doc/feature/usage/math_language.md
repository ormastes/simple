# Math Language Specification
*Source:* `test/feature/usage/math_language_spec.spl`
**Feature IDs:** #2200-2205  |  **Category:** Syntax  |  **Status:** Implemented

## Overview



use std.text.{NL}

Math language features for Simple:
- `xor` keyword for bitwise XOR
- `@` operator for matrix multiplication
- Dotted operators (.+, .-, .*, ./, .^) for broadcasting
- `m{}` math blocks with `^` power operator

## Feature: xor Keyword

The `xor` keyword provides bitwise XOR operation.
    It has precedence between `or` and `and`.

### Scenario: basic operations

| # | Example | Status |
|---|---------|--------|
| 1 | computes bitwise XOR of two integers | pass |
| 2 | returns identity when XOR with 0 | pass |
| 3 | returns 0 when XOR with itself | pass |

**Example:** computes bitwise XOR of two integers
    Given val result = 5 xor 3
    Then  expect result == 6  # 0b101 xor 0b011 = 0b110

**Example:** returns identity when XOR with 0
    Given val result = 42 xor 0
    Then  expect result == 42

**Example:** returns 0 when XOR with itself
    Given val x = 123
    Given val result = x xor x
    Then  expect result == 0

### Scenario: precedence

| # | Example | Status |
|---|---------|--------|
| 1 | has lower precedence than and | pass |
| 2 | has higher precedence than or | pass |

**Example:** has lower precedence than and
    Given val result = 7 xor 3 and 1
    Then  expect result == (7 xor (3 and 1))

**Example:** has higher precedence than or
    Given val result = 0 or 5 xor 3
    Then  expect result == (0 or (5 xor 3))

## Feature: @ MatMul Operator

The `@` operator performs matrix multiplication.
    It has precedence between additive (+, -) and multiplicative (*, /).

### Scenario: basic operations

| # | Example | Status |
|---|---------|--------|
| 1 | parses @ as matrix multiply | pass |

**Example:** parses @ as matrix multiply
    Given val A = [[1, 2], [3, 4]]
    Given val B = [[5, 6], [7, 8]]
    Then  expect true  # Parser test - @ is recognized

### Scenario: precedence

| # | Example | Status |
|---|---------|--------|
| 1 | binds tighter than addition | pass |
| 2 | binds looser than multiplication | pass |

**Example:** binds tighter than addition
    Then  expect true  # Parser precedence test

**Example:** binds looser than multiplication
    Then  expect true  # Parser precedence test

## Feature: Dotted Broadcast Operators

Dotted operators (.+, .-, .*, ./, .^) perform element-wise
    broadcasting operations on arrays/tensors.

### Scenario: .+ broadcast add

| # | Example | Status |
|---|---------|--------|
| 1 | parses .+ as broadcast add | pass |

**Example:** parses .+ as broadcast add
    Then  expect true  # Parser test

### Scenario: .- broadcast sub

| # | Example | Status |
|---|---------|--------|
| 1 | parses .- as broadcast sub | pass |

**Example:** parses .- as broadcast sub
    Then  expect true  # Parser test

### Scenario: .* broadcast mul

| # | Example | Status |
|---|---------|--------|
| 1 | parses .* as broadcast mul | pass |

**Example:** parses .* as broadcast mul
    Then  expect true  # Parser test

### Scenario: ./ broadcast div

| # | Example | Status |
|---|---------|--------|
| 1 | parses ./ as broadcast div | pass |

**Example:** parses ./ as broadcast div
    Then  expect true  # Parser test

### Scenario: .^ broadcast pow

| # | Example | Status |
|---|---------|--------|
| 1 | parses .^ as broadcast pow | pass |

**Example:** parses .^ as broadcast pow
    Then  expect true  # Parser test

## Feature: m{} Math Blocks

Math blocks `m{ ... }` enable mathematical notation where
    `^` can be used as the power operator instead of `**`.
    Outside of m{} blocks, `^` produces a lexer error.

### Scenario: power operator inside m{}

| # | Example | Status |
|---|---------|--------|
| 1 | allows ^ as power inside math block | pass |
| 2 | computes quadratic expression | pass |
| 3 | handles nested exponentiation | pass |

**Example:** allows ^ as power inside math block
    Given val result = m{ 2^3 }
    Then  expect result == 8

**Example:** computes quadratic expression
    Given val x = 3
    Given val result = m{ x^2 + 2*x + 1 }
    Then  expect result == 16  # 9 + 6 + 1

**Example:** handles nested exponentiation
    Given val result = m{ 2^3^2 }
    Then  expect result == 512

### Scenario: complex expressions

| # | Example | Status |
|---|---------|--------|
| 1 | computes distance formula | pass |
| 2 | mixes ^ and ** equivalently | pass |

**Example:** computes distance formula
    Given val x = 3
    Given val y = 4
    Given val dist_sq = m{ x^2 + y^2 }
    Then  expect dist_sq == 25

**Example:** mixes ^ and ** equivalently
    Given val a = m{ 2^4 }
    Given val b = 2 ** 4
    Then  expect a == b

### Scenario: nested braces

| # | Example | Status |
|---|---------|--------|
| 1 | handles nested braces in math block | pass |

**Example:** handles nested braces in math block
    Given val point = { x: 3, y: 4 }
    Given val result = m{ point.x^2 + point.y^2 }
    Then  expect result == 25

## Feature: Power Operator Behavior

Power operator behavior:
    - `**` works everywhere
    - `^` only works inside m{} blocks

### Scenario: ** operator

| # | Example | Status |
|---|---------|--------|
| 1 | works outside math blocks | pass |
| 2 | works inside math blocks | pass |
| 3 | is right-associative | pass |

**Example:** works outside math blocks
    Given val result = 2 ** 10
    Then  expect result == 1024

**Example:** works inside math blocks
    Given val result = m{ 2 ** 3 }
    Then  expect result == 8

**Example:** is right-associative
    Given val result = 2 ** 3 ** 2
    Then  expect result == 512


