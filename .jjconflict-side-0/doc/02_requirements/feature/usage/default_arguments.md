# Default Arguments Specification
*Source:* `test/feature/usage/default_arguments_spec.spl`
**Feature IDs:** #DEFARG-001  |  **Category:** Language | Functions  |  **Status:** Implemented

## Overview



## Overview

Tests for function default argument values.

## Syntax

```simple
fn greet(name, greeting="Hello"):
    print "{greeting}, {name}!"

greet("Alice")           # Uses default: "Hello, Alice!"
greet("Bob", "Hi")       # Override: "Hi, Bob!"
```

## Feature: Default Arguments

## Function Default Parameter Values

    Tests for default values in function parameters.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | uses default argument when not provided | pass |
| 2 | overrides default argument when provided | pass |
| 3 | uses multiple default arguments | pass |
| 4 | overrides some default arguments | pass |

**Example:** uses default argument when not provided
    Then  expect add(5) == 15

**Example:** overrides default argument when provided
    Then  expect add(5, b=20) == 25

**Example:** uses multiple default arguments
    Then  expect calc(1) == 7

**Example:** overrides some default arguments
    Then  expect calc(1, c=10) == 21


