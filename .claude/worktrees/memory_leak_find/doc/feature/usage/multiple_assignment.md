# Multiple Assignment (Destructuring) Specification
*Source:* `test/feature/usage/multiple_assignment_spec.spl`
**Feature IDs:** #MULTIPLE-ASSIGNMENT  |  **Category:** Syntax  |  **Status:** Implemented

## Overview



use std.text.{NL}

Multiple assignment (destructuring) allows binding multiple variables from
compound values like tuples, arrays, and structs in a single statement.
This provides concise syntax for unpacking data structures.

## Syntax

```simple
# Tuple destructuring
val (x, y) = get_point()
val (first, second, ...rest) = items

# Array destructuring
val [a, b, c] = triple

# Struct destructuring
val {name, age} = person
```

## Key Behaviors

- Pattern must match the structure of the value
- Variables are bound in the order they appear
- Wildcards `_` can ignore unwanted values
- Rest patterns `...rest` capture remaining elements

## Feature: Multiple Assignment (Destructuring)

## Destructuring Assignment Specification

    Multiple assignment provides concise syntax for extracting values from
    compound data types. This test suite verifies:
    - Tuple destructuring with `val (a, b) = tuple`
    - Array destructuring with `val [x, y, z] = array`
    - Nested destructuring for complex structures
    - Wildcard patterns to ignore values
    - Mutable destructuring with `var`

### Scenario: tuple destructuring

| # | Example | Status |
|---|---------|--------|
| 1 | destructures a pair | pass |
| 2 | destructures a triple | pass |
| 3 | uses destructured values in expressions | pass |
| 4 | destructures function return value | pass |

**Example:** destructures a pair
    Given val pair = (10, 20)
    Given val (a, b) = pair
    Then  expect a == 10
    Then  expect b == 20

**Example:** destructures a triple
    Given val triple = (1, 2, 3)
    Given val (x, y, z) = triple
    Then  expect x == 1
    Then  expect y == 2
    Then  expect z == 3

**Example:** uses destructured values in expressions
    Given val point = (3, 4)
    Given val (x, y) = point
    Given val distance_squared = x * x + y * y
    Then  expect distance_squared == 25

**Example:** destructures function return value
    Given val (x, y) = get_coordinates()
    Then  expect x == 100
    Then  expect y == 200

### Scenario: tuple destructuring with wildcards

| # | Example | Status |
|---|---------|--------|
| 1 | ignores first element with wildcard | pass |
| 2 | ignores middle element with wildcard | pass |
| 3 | ignores last element with wildcard | pass |
| 4 | ignores multiple elements | pass |

**Example:** ignores first element with wildcard
    Given val triple = (1, 2, 3)
    Given val (_, b, c) = triple
    Then  expect b == 2
    Then  expect c == 3

**Example:** ignores middle element with wildcard
    Given val triple = (1, 2, 3)
    Given val (a, _, c) = triple
    Then  expect a == 1
    Then  expect c == 3

**Example:** ignores last element with wildcard
    Given val triple = (1, 2, 3)
    Given val (a, b, _) = triple
    Then  expect a == 1
    Then  expect b == 2

**Example:** ignores multiple elements
    Given val quad = (1, 2, 3, 4)
    Given val (a, _, _, d) = quad
    Then  expect a == 1
    Then  expect d == 4

### Scenario: nested tuple destructuring

| # | Example | Status |
|---|---------|--------|
| 1 | destructures nested tuples | pass |
| 2 | destructures deeply nested tuples | pass |

**Example:** destructures nested tuples
    Given val nested = ((1, 2), 3)
    Given val ((a, b), c) = nested
    Then  expect a == 1
    Then  expect b == 2
    Then  expect c == 3

**Example:** destructures deeply nested tuples
    Given val deep = (((1, 2), 3), 4)
    Given val (((a, b), c), d) = deep
    Then  expect a == 1
    Then  expect b == 2
    Then  expect c == 3
    Then  expect d == 4

### Scenario: array destructuring

| # | Example | Status |
|---|---------|--------|
| 1 | destructures fixed-size array | pass |
| 2 | destructures with wildcard | pass |

**Example:** destructures fixed-size array
    Given val arr = [10, 20, 30]
    Given val [a, b, c] = arr
    Then  expect a == 10
    Then  expect b == 20
    Then  expect c == 30

**Example:** destructures with wildcard
    Given val arr = [1, 2, 3]
    Given val [x, _, z] = arr
    Then  expect x == 1
    Then  expect z == 3

### Scenario: mutable destructuring

| # | Example | Status |
|---|---------|--------|
| 1 | creates mutable bindings | pass |
| 2 | allows partial mutation | pass |

**Example:** creates mutable bindings
    Given val pair = (5, 10)
    Given var (a, b) = pair
    Then  expect a == 6
    Then  expect b == 11

**Example:** allows partial mutation
    Given val triple = (1, 2, 3)
    Given var (x, y, z) = triple
    Then  expect x == 10
    Then  expect y == 2
    Then  expect z == 3

### Scenario: mixed type destructuring

| # | Example | Status |
|---|---------|--------|
| 1 | destructures tuples with different types | pass |
| 2 | destructures nested mixed types | pass |

**Example:** destructures tuples with different types
    Given val mixed = ("hello", 42)
    Given val (name, count) = mixed
    Then  expect name == "hello"
    Then  expect count == 42

**Example:** destructures nested mixed types
    Given val data = (("Alice", 30), true)
    Given val ((name, age), active) = data
    Then  expect name == "Alice"
    Then  expect age == 30
    Then  expect active == true

### Scenario: destructuring in loops

| # | Example | Status |
|---|---------|--------|
| 1 | destructures in for loop | pass |
| 2 | uses destructured values for computation | pass |

**Example:** destructures in for loop
    Given val pairs = [(1, 2), (3, 4), (5, 6)]
    Given var sum = 0
    Then  expect sum == 21

**Example:** uses destructured values for computation
    Given val points = [(0, 0), (3, 4), (6, 8)]
    Given var total_distance = 0
    Then  expect total_distance == 21


