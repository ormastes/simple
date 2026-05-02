# Function Definitions Specification
*Source:* `test/feature/usage/functions_spec.spl`
**Feature IDs:** #1004  |  **Category:** Language  |  **Status:** In Progress

## Overview




Tests for function definition and invocation.
Verifies function parameters, return types, implicit returns, and various calling patterns.

## Feature: Function Definitions

Tests for function definitions, parameter handling, and return behavior.
    Verifies function signatures, parameter passing, type inference, and implicit returns.

### Scenario: basic function definition

### Scenario: Simple Functions

        Tests basic function definitions with parameters and return types.

| # | Example | Status |
|---|---------|--------|
| 1 | defines function with explicit return type | pass |
| 2 | uses implicit return of last expression | pass |
| 3 | calls function with no parameters | pass |

**Example:** defines function with explicit return type
    Then  expect add(2, 3) == 5

**Example:** uses implicit return of last expression
    Then  expect multiply(3, 4) == 12

**Example:** calls function with no parameters
    Then  expect get_greeting() == "Hello, World!"

### Scenario: function parameters

### Scenario: Parameter Handling

        Tests various parameter styles and type inference.

| # | Example | Status |
|---|---------|--------|
| 1 | passes multiple parameters | pass |
| 2 | uses type inference for parameters | pass |
| 3 | uses named arguments | pass |

**Example:** passes multiple parameters
    Then  expect combine(1, 2, 3) == 6

**Example:** uses type inference for parameters
    Then  expect double(5) == 10

**Example:** uses named arguments
    Then  expect create_point(x: 3, y: 4) == "3, 4"

### Scenario: function return types

### Scenario: Return Behavior

        Tests function return types and implicit returns.

| # | Example | Status |
|---|---------|--------|
| 1 | returns single value | pass |
| 2 | returns early with explicit return | pass |
| 3 | returns without explicit type annotation | pass |

**Example:** returns single value
    Then  expect square(5) == 25

**Example:** returns early with explicit return
    Then  expect get_sign(-5) == "negative"

**Example:** returns without explicit type annotation
    Then  expect concat("hello", "world") == "helloworld"

### Scenario: function with no return

### Scenario: Void Functions

        Tests functions that perform actions without returning values.

| # | Example | Status |
|---|---------|--------|
| 1 | executes function with side effects | pass |
| 2 | calls function multiple times | pass |

**Example:** executes function with side effects
    Given var counter = 0
    Given val increment = \:
    Then  expect counter == 1

**Example:** calls function multiple times
    Given var value = 0
    Then  expect value == 42

### Scenario: higher-order functions

### Scenario: Functions as Arguments

        Tests passing functions as parameters and returning functions.

| # | Example | Status |
|---|---------|--------|
| 1 | accepts function parameter | pass |
| 2 | uses lambda function | pass |
| 3 | returns function | pass |

**Example:** accepts function parameter
    Then  expect apply(double, 5) == 10

**Example:** uses lambda function
    Then  expect apply({NL}: n + 10, 5) == 15

**Example:** returns function
    Given val add_five = make_adder(5)
    Then  expect add_five(3) == 8

### Scenario: generic functions

### Scenario: Parametric Functions

        Tests generic functions with type parameters.

| # | Example | Status |
|---|---------|--------|
| 1 | defines generic function | pass |
| 2 | uses generic with constraints | pass |
| 3 | uses multiple type parameters | pass |

**Example:** defines generic function
    Then  expect identity(42) == 42

**Example:** uses generic with constraints
    Given val first = get_first([1, 2, 3])
    Then  expect first == Some(1)

**Example:** uses multiple type parameters
    Then  expect pair(1, "hello") == "pair"

### Scenario: recursive functions

### Scenario: Recursion

        Tests recursive function definitions and termination.

| # | Example | Status |
|---|---------|--------|
| 1 | defines recursive factorial function | pass |
| 2 | uses tail recursion | pass |

**Example:** defines recursive factorial function
    Then  expect factorial(5) == 120

**Example:** uses tail recursion
    Then  expect sum_to(10) == 55


