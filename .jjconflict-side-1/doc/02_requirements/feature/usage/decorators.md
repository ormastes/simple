# Decorators Specification
*Source:* `test/feature/usage/decorators_spec.spl`
**Feature IDs:** #DECO-001  |  **Category:** Language | Functions  |  **Status:** Implemented

## Overview



## Overview

Decorators are functions that transform other functions, enabling
aspect-oriented programming patterns like logging, caching, and validation.

## Syntax

```simple
# Basic decorator
@double_result
fn add_one(x):
    return x + 1

# Decorator with arguments
@multiply_by(3)
fn increment(x):
    return x + 1
```

## Feature: Decorators

## Function Decorators

    Tests for decorator syntax and function wrapping.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | applies basic decorator | pass |
| 2 | applies decorator with arguments | pass |
| 3 | stacks multiple decorators | pass |
| 4 | uses decorator without parentheses | pass |

**Example:** applies basic decorator
    Then  expect add_one(5) == 12

**Example:** applies decorator with arguments
    Then  expect increment(10) == 33

**Example:** stacks multiple decorators
    Then  expect identity(5) == 20  # 5 -> double -> 10 -> add_ten -> 20

**Example:** uses decorator without parentheses
    Then  expect square(4) == 21  # 16 + 5

## Feature: Attributes

## Compile-Time Attributes

    Tests for attribute syntax that provides metadata to the compiler.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | uses inline attribute | pass |
| 2 | uses deprecated attribute | pass |
| 3 | uses deprecated with message | pass |
| 4 | stacks multiple attributes | pass |

**Example:** uses inline attribute
    Then  expect add(3, 4) == 7

**Example:** uses deprecated attribute
    Then  expect old_api(10) == 20

**Example:** uses deprecated with message
    Then  expect legacy(5) == 6

**Example:** stacks multiple attributes
    Then  expect double(21) == 42

## Feature: Context Managers

## With Statement

    Tests for context manager protocol and with blocks.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | executes basic with block | pass |
| 2 | binds value with as clause | pass |

**Example:** executes basic with block
    Given var counter = 0
    Then  expect counter == 1

**Example:** binds value with as clause
    Given val value = x + 1
    Then  expect value == 43


