# Named Arguments Specification
*Source:* `test/feature/usage/named_arguments_spec.spl`
**Feature IDs:** #NAMED-ARGS-001  |  **Category:** Language | Functions  |  **Status:** Implemented

## Overview



## Overview

Tests for named argument support allowing function calls with explicit
parameter names, improving code clarity and enabling flexible argument ordering.

## Syntax

```simple
fn create_user(name: str, email: str, age: i64) -> User:
    User(name: name, email: email, age: age)

# Call with positional arguments
val user1 = create_user("Alice", "alice@example.com", 30)

# Call with named arguments
val user2 = create_user(age=25, name="Bob", email="bob@example.com")

# Mixed positional and named
val user3 = create_user("Charlie", email="charlie@example.com", age=35)
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Named Argument | Explicitly passing parameter by name |
| Positional Argument | Passing argument by position order |
| Argument Reordering | Non-positional order with named arguments |
| Default Values | Optional parameters with defaults |
| Clarity | Improved code readability with explicit parameter names |

## Behavior

- Named arguments can be passed in any order
- Positional arguments must precede named arguments (if mixed)
- Parameter names are part of the function signature
- Type checking applies to named arguments like positional
- Named arguments cannot be repeated in a single call
- Works with constructors and regular functions

## Feature: Named Arguments Basic Usage

## Named Parameter Passing

    Verifies that functions accept named arguments and properly
    map them to their corresponding parameters.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | calls function with named arguments | pass |
| 2 | passes values correctly with named arguments | pass |
| 3 | works with string values | pass |

**Example:** calls function with named arguments
    Then  expect greet(name="world", greeting="hello") == 1

**Example:** passes values correctly with named arguments
    Then  expect add(a=10, b=20) == 30

**Example:** works with string values
    Given val result = concat(first="Hello", second=" World")
    Given var r = 0
    Then  expect r == 1

## Feature: Named Arguments Reordering

## Argument Reordering

    Tests that named arguments can be passed in any order,
    regardless of parameter definition order.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | allows reversed argument order | pass |
| 2 | reorders three arguments | pass |
| 3 | reorders with different calculation | pass |

**Example:** allows reversed argument order
    Then  expect sub(b=10, a=30) == 20

**Example:** reorders three arguments
    Then  expect calc(z=4, x=2, y=3) == 14

**Example:** reorders with different calculation
    Then  expect compute(third=3, first=1, second=2) == 123

## Feature: Mixed Positional and Named Arguments

## Mixing Argument Styles

    Tests combining positional arguments with named arguments
    in the same function call.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | mixes positional and named arguments | pass |
| 2 | uses positional first then named | pass |
| 3 | uses single positional with multiple named | pass |

**Example:** mixes positional and named arguments
    Then  expect calc(2, z=4, y=3) == 14

**Example:** uses positional first then named
    Then  expect process(5, c=7, b=3) == 22

**Example:** uses single positional with multiple named
    Then  expect combine(10, add=5, mult=2) == 25

## Feature: Named Arguments with Defaults

## Default Parameter Values

    Tests named arguments combined with default parameter values.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | uses default when argument not provided | pass |
| 2 | overrides default with named argument | pass |
| 3 | works with multiple defaults | pass |

**Example:** uses default when argument not provided
    Then  expect add(5) == 15

**Example:** overrides default with named argument
    Then  expect add(5, b=20) == 25

**Example:** works with multiple defaults
    Then  expect calculate(1) == 7
    Then  expect calculate(1, y=5) == 16
    Then  expect calculate(1, z=10) == 21

## Feature: Named Arguments in Methods

## Method Calls with Named Arguments

    Tests named arguments when calling methods on objects.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | uses named arguments with class methods | pass |
| 2 | reorders method arguments | pass |

**Example:** uses named arguments with class methods
    Given val calc = Calculator {}
    Then  expect calc.compute(a=6, b=7) == 42

**Example:** reorders method arguments
    Given val m = Math {}
    Then  expect m.subtract(subtrahend=15, minuend=50) == 35

## Feature: Named Arguments Edge Cases

## Special Cases

    Tests edge cases and boundary conditions for named arguments.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | handles single named argument | pass |
| 2 | handles many named arguments | pass |
| 3 | works with nested function calls | pass |

**Example:** handles single named argument
    Then  expect identity(x=42) == 42

**Example:** handles many named arguments
    Then  expect sum5(e=5, d=4, c=3, b=2, a=1) == 15

**Example:** works with nested function calls
    Then  expect add(a=double(x=5), b=double(x=3)) == 16


