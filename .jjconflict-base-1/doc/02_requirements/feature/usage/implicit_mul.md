# Implicit Multiplication Specification
*Source:* `test/feature/usage/implicit_mul_spec.spl`
**Feature IDs:** #2240-2245  |  **Category:** Syntax  |  **Status:** Implemented

## Overview



use std.text.{NL}

Implicit multiplication in m{} math blocks:
- `2x` → `2 * x`
- `2(x+1)` → `2 * (x+1)`
- `(a)(b)` → `(a) * (b)`
- `(x+1)y` → `(x+1) * y`

## Feature: Implicit Multiplication in m{}

Implicit multiplication allows writing mathematical expressions
    without explicit * operator in m{} blocks only.

### Scenario: number followed by identifier

| # | Example | Status |
|---|---------|--------|
| 1 | treats 2x as 2*x | pass |
| 2 | treats 3y as 3*y | pass |
| 3 | works with floats | pass |

**Example:** treats 2x as 2*x
    Given val x = 5
    Given val result = m{ 2x }
    Then  expect result == 10

**Example:** treats 3y as 3*y
    Given val y = 7
    Given val result = m{ 3y }
    Then  expect result == 21

**Example:** works with floats
    Given val x = 4.0
    Given val result = m{ 2.5x }
    Then  expect result == 10.0

### Scenario: number followed by parentheses

| # | Example | Status |
|---|---------|--------|
| 1 | treats 2(x+1) as 2*(x+1) | pass |
| 2 | works in complex expressions | pass |

**Example:** treats 2(x+1) as 2*(x+1)
    Given val x = 3
    Given val result = m{ 2(x + 1) }
    Then  expect result == 8

**Example:** works in complex expressions
    Given val x = 2
    Given val result = m{ 3(x + 1)^2 }
    Then  expect result == 27  # 3 * (3)^2 = 3 * 9

### Scenario: parentheses followed by parentheses

| # | Example | Status |
|---|---------|--------|
| 1 | treats (a)(b) as (a)*(b) | pass |
| 2 | chains multiple groups | pass |

**Example:** treats (a)(b) as (a)*(b)
    Given val a = 2
    Given val b = 3
    Given val result = m{ (a + 1)(b - 1) }
    Then  expect result == 6  # (3) * (2)

**Example:** chains multiple groups
    Given val a = 2
    Given val result = m{ (a)(a)(a) }
    Then  expect result == 8  # 2 * 2 * 2

### Scenario: parentheses followed by identifier

| # | Example | Status |
|---|---------|--------|
| 1 | treats (x+1)y as (x+1)*y | pass |

**Example:** treats (x+1)y as (x+1)*y
    Given val x = 2
    Given val y = 4
    Given val result = m{ (x + 1)y }
    Then  expect result == 12  # (3) * 4

### Scenario: complex expressions

| # | Example | Status |
|---|---------|--------|
| 1 | computes quadratic with implicit mul | pass |
| 2 | computes polynomial | pass |
| 3 | mixes explicit and implicit mul | pass |
| 4 | handles scientific notation style | pass |

**Example:** computes quadratic with implicit mul
    Given val x = 3
    Given val result = m{ 2x^2 + 3x + 1 }
    Then  expect result == 28  # 2*9 + 3*3 + 1

**Example:** computes polynomial
    Given val x = 2
    Given val result = m{ x^3 + 2x^2 + 3x + 4 }
    Then  expect result == 26  # 8 + 8 + 6 + 4

**Example:** mixes explicit and implicit mul
    Given val x = 3
    Given val result = m{ 2x * 3 }
    Then  expect result == 18  # (2*3) * 3

**Example:** handles scientific notation style
    Given val pi = 3.14159
    Given val r = 2
    Given val area = m{ pi r^2 }
    Then  expect area.approx(12.566, epsilon: 0.01)

### Scenario: matrix expressions

| # | Example | Status |
|---|---------|--------|
| 1 | multiplies coefficient and matrix | pass |
| 2 | works in linear algebra | pass |

**Example:** multiplies coefficient and matrix
    Given val A = [[1, 2], [3, 4]]
    Given val result = m{ 2A }
    Then  expect result == [[2, 4], [6, 8]]

**Example:** works in linear algebra
    Given val A = [[1, 0], [0, 1]]
    Given val x = [1, 2]
    Given val b = [3, 4]
    Given val result = m{ 2(A @ x) + b }
    Then  expect result == [5, 8]

### Scenario: precedence

| # | Example | Status |
|---|---------|--------|
| 1 | implicit mul has same precedence as explicit | pass |
| 2 | power binds tighter | pass |

**Example:** implicit mul has same precedence as explicit
    Given val x = 2
    Given val y = 3
    Given val result = m{ 2x + 3y }
    Then  expect result == 13  # 4 + 9

**Example:** power binds tighter
    Given val x = 2
    Given val result = m{ 2x^3 }
    Then  expect result == 16  # 2 * 8

### Scenario: outside m{} blocks

| # | Example | Status |
|---|---------|--------|
| 1 | does NOT allow implicit mul outside m{} | pass |

**Example:** does NOT allow implicit mul outside m{}
    Given val x = 5
    Given val result = 2 * x  # Must use explicit *
    Then  expect result == 10

## Feature: Implicit Multiplication Edge Cases

Edge cases and potential ambiguities.

### Scenario: function calls are NOT implicit mul

| # | Example | Status |
|---|---------|--------|
| 1 | preserves function call syntax | pass |

**Example:** preserves function call syntax
    Given val x = 5
    Given val result = double(x)
    Then  expect result == 10

### Scenario: negative numbers

| # | Example | Status |
|---|---------|--------|
| 1 | handles negative coefficient | pass |
| 2 | handles subtraction vs negative | pass |

**Example:** handles negative coefficient
    Given val x = 3
    Given val result = m{ -2x }
    Then  expect result == -6

**Example:** handles subtraction vs negative
    Given val x = 3
    Given val y = 2
    Given val result = m{ -x y }
    Then  expect result == -6

### Scenario: whitespace

| # | Example | Status |
|---|---------|--------|
| 1 | works without spaces | pass |
| 2 | works with spaces | pass |

**Example:** works without spaces
    Given val x = 5
    Given val result = m{ 2x+3 }
    Then  expect result == 13

**Example:** works with spaces
    Given val x = 5
    Given val result = m{ 2 x + 3 }
    Then  expect result == 13


