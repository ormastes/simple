# Tuple Types Specification
*Source:* `test/feature/usage/tuple_types_spec.spl`
**Feature IDs:** #TBD  |  **Category:** Language  |  **Status:** Implemented

## Overview



## Overview

Tuple types are ordered collections of heterogeneous values with fixed length.
They allow grouping multiple values of different types without defining a
named struct, useful for returning multiple values or temporary groupings.

## Syntax

```simple
val point = (3, 4)
val mixed = ("hello", 42, true)
val (x, y) = point  # Destructuring
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Tuple | Fixed-size heterogeneous collection |
| Tuple Type | Type annotation like `(T1, T2, T3)` |
| Destructuring | Pattern matching to extract tuple elements |
| Unit Type | Empty tuple `()` representing no value |

## Behavior

- Tuples have fixed length determined at compile time
- Elements accessed by index: `tuple[0]`, `tuple[1]`
- Support pattern matching and destructuring
- Unit type `()` is the zero-element tuple

## Feature: Tuple Types

## Core Tuple Functionality

    Tests for tuple creation, access, destructuring, and type annotations.
    Validates tuple behavior with various element types.

### Scenario: tuple creation

### Scenario: Tuple Creation

        Creates tuples with various element types and sizes.

| # | Example | Status |
|---|---------|--------|
| 1 | creates tuple literal | pass |
| 2 | gets tuple length | pass |

**Example:** creates tuple literal
    Given val t = (10, 20, 30)
    Then  expect t[1] == 20

**Example:** gets tuple length
    Given val t = (1, 2, 3, 4)
    Then  expect t.len() == 4

### Scenario: tuple access

### Scenario: Tuple Element Access

        Accesses individual tuple elements by index.

| # | Example | Status |
|---|---------|--------|
| 1 | accesses elements by index | pass |

**Example:** accesses elements by index
    Given val t = (5, 10, 15)
    Then  expect t[0] == 5
    Then  expect t[2] == 15

### Scenario: tuple destructuring

### Scenario: Tuple Destructuring

        Extracts tuple elements into variables.

| # | Example | Status |
|---|---------|--------|
| 1 | destructures tuple into variables | pass |
| 2 | swaps values with tuple destructuring | pass |
| 3 | destructures from array | pass |

**Example:** destructures tuple into variables
    Given val (a, b, c) = (10, 20, 30)
    Then  expect a + b + c == 60

**Example:** swaps values with tuple destructuring
    Given val a = 10
    Given val b = 20
    Given val (x, y) = (b, a)
    Then  expect x == 20

**Example:** destructures from array
    Given val arr = [5, 10, 15]
    Given val (first, second, third) = arr
    Then  expect second == 10

## Feature: Tuple Pattern Matching

## Pattern Matching with Tuples

    Tests for tuple patterns in match expressions.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | matches tuple pattern | pass |
| 2 | uses wildcard for unmatched tuples | pass |

**Example:** matches tuple pattern
    Given val t = (1, 2)
    Given val result = match t:
    Then  expect result == 20

**Example:** uses wildcard for unmatched tuples
    Given val t = (5, 5)
    Given val result = match t:
    Then  expect result == 99


