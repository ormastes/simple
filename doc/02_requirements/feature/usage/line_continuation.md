# Line Continuation Specification
*Source:* `test/feature/usage/line_continuation_spec.spl`
**Feature IDs:** #2400  |  **Category:** Syntax  |  **Status:** Implemented

## Overview



Line continuation allows long expressions and function calls to span multiple lines
using explicit backslash (`\`) at end of line. This enables clean formatting of
complex expressions without exceeding line length limits.

## Syntax

```simple
# Explicit continuation with backslash
val sum = value1 + \
    value2 + \
    value3

# Function call with continuation
val result = add(1, \
    2, \
    3)
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Explicit Continuation | Backslash at line end forces continuation to next line |
| Nesting | Multiple levels of continuation allowed |
| Indentation | Improves readability but not required for continuation |

## Behavior

Line continuation:
- Backslash at end of line continues expression to next line
- Multiple continuations can be chained
- Works in expressions and function calls
- Preserves semantic meaning across line boundaries

## Note

Implicit continuation (just newlines inside parentheses/brackets/braces) is not
currently supported. Use explicit backslash continuation instead.

## Feature: Line Continuation

## Line Continuation Specification

    This test suite verifies explicit backslash line continuation behavior.

### Scenario: explicit continuation with backslash

### Scenario: Backslash Line Continuation

        Tests explicit line continuation using backslash at end of line.

| # | Example | Status |
|---|---------|--------|
| 1 | continues expression with backslash | pass |
| 2 | continues function call with backslash | pass |
| 3 | combines backslash and arithmetic | pass |
| 4 | chains multiple continuations | pass |

**Example:** continues expression with backslash
    Given val result = 1 + 2 + \
    Then  expect result == 10

**Example:** continues function call with backslash
    Given val result = add(1, \
    Then  expect result == 6

**Example:** combines backslash and arithmetic
    Given val a = 10
    Given val b = 20
    Given val c = 30
    Given val result = a + \
    Then  expect result == 60

**Example:** chains multiple continuations
    Given val result = 1 + \
    Then  expect result == 15

### Scenario: continuation in various expressions

| # | Example | Status |
|---|---------|--------|
| 1 | continues binary operation | pass |
| 2 | continues comparison | pass |
| 3 | continues string concatenation | pass |

**Example:** continues binary operation
    Given val x = 100 + \
    Then  expect x == 300

**Example:** continues comparison
    Given val a = 5
    Given val b = 10
    Given val result = a < \
    Given var r = 0
    Then  expect r == 1

**Example:** continues string concatenation
    Given val s = "Hello" + \
    Given var result = 0
    Then  expect result == 1

### Scenario: continuation with indentation

| # | Example | Status |
|---|---------|--------|
| 1 | works with any indentation level | pass |
| 2 | continues deeply indented code | pass |

**Example:** works with any indentation level
    Given val result = 10 + \
    Then  expect result == 60

**Example:** continues deeply indented code
    Given val x = 1 + \
    Then  expect outer() == 3

### Scenario: practical examples

| # | Example | Status |
|---|---------|--------|
| 1 | formats long arithmetic expression | pass |
| 2 | formats function with many arguments | pass |

**Example:** formats long arithmetic expression
    Given val total = 100 + \
    Then  expect total == 1000

**Example:** formats function with many arguments
    Given val result = sum5(1, \
    Then  expect result == 15


