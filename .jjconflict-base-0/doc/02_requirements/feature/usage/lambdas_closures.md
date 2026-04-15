# Lambdas and Closures Specification
*Source:* `test/feature/usage/lambdas_closures_spec.spl`
**Feature IDs:** #2300  |  **Category:** Language  |  **Status:** Implemented

## Overview



use std.text.{NL}

Lambdas (anonymous functions) and closures enable functional programming patterns.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Lambda | Anonymous function defined inline with `\` syntax |
| Closure | Function that captures variables from enclosing scope |
| Higher-Order Function | Function taking or returning other functions |

## Feature: Basic Lambdas

## Basic Lambda Definition

    Tests simple lambda creation and invocation.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | creates simple lambda | pass |
| 2 | creates lambda with multiple params | pass |
| 3 | creates lambda with no params | pass |
| 4 | invokes lambda immediately | pass |

**Example:** creates simple lambda
    Given val double = \x: x * 2
    Then  expect double(21) == 42

**Example:** creates lambda with multiple params
    Given val add = \x, y: x + y
    Then  expect add(15, 27) == 42

**Example:** creates lambda with no params
    Given val answer = \: 42
    Then  expect answer() == 42

**Example:** invokes lambda immediately
    Given val result = (\x: x + 5)(37)
    Then  expect result == 42

## Feature: Closures

## Closure Variable Capture

    Tests closures capturing variables from outer scope.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | captures outer variable | pass |
| 2 | captures multiple variables | pass |
| 3 | nested lambda calls | pass |

**Example:** captures outer variable
    Given val multiplier = 10
    Given val multiply = \x: x * multiplier
    Then  expect multiply(4) == 40

**Example:** captures multiple variables
    Given val a = 10
    Given val b = 5
    Given val calc = \x: x * a + b
    Then  expect calc(3) == 35

**Example:** nested lambda calls
    Given val double = \x: x * 2
    Given val add_one = \x: x + 1
    Then  expect add_one(double(20)) == 41

## Feature: Lambdas with Collections

## Higher-Order Functions

    Tests lambdas with collection methods.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | maps with lambda | pass |
| 2 | filters with lambda | pass |
| 3 | reduces with lambda | pass |

**Example:** maps with lambda
    Given val numbers = [1, 2, 3]
    Given val doubled = numbers.map(\x: x * 2)
    Then  expect doubled[0] == 2
    Then  expect doubled[1] == 4
    Then  expect doubled[2] == 6

**Example:** filters with lambda
    Given val numbers = [1, 2, 3, 4, 5, 6]
    Given val evens = numbers.filter(\x: x % 2 == 0)
    Then  expect evens.len() == 3

**Example:** reduces with lambda
    Given val numbers = [1, 2, 3, 4]
    Given val sum = numbers.reduce(0, \acc, x: acc + x)
    Then  expect sum == 10

## Feature: Lambda Edge Cases

## Special Cases

    Tests edge cases for lambda behavior.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | lambda returning lambda | pass |
| 2 | lambda as function parameter | pass |
| 3 | lambda with conditional | pass |

**Example:** lambda returning lambda
    Given val add_five = make_adder(5)
    Then  expect add_five(10) == 15

**Example:** lambda as function parameter
    Then  expect apply(\x: x * 2, 21) == 42

**Example:** lambda with conditional
    Given val abs = \x: if x < 0: -x else: x
    Then  expect abs(-5) == 5
    Then  expect abs(5) == 5


