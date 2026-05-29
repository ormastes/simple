# Async Features Specification
*Source:* `test/feature/usage/async_features_spec.spl`
**Feature IDs:** #ASYNC-001 to #ASYNC-063  |  **Category:** Runtime | Async  |  **Status:** Implemented

## Overview




Tests async features including:
- Lambda expressions
- Future creation and await
- Async functions
- Generators and yield
- Codegen/interpreter parity

Features not supported by runtime parser:
- async fn syntax
- await keyword
- spawn keyword
- yield keyword
- generator() function

## Feature: Lambda Expressions

## Lambda Syntax

    Tests lambda expression parsing and execution.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | basic lambda with single param | pass |
| 2 | lambda with multiple params | pass |
| 3 | lambda capturing outer variable | pass |
| 4 | immediately invoked lambda | pass |
| 5 | nested lambda calls | pass |
| 6 | lambda with no params | pass |

**Example:** basic lambda with single param
    Given val double = \x: x * 2

**Example:** lambda with multiple params
    Given val add = \x, y: x + y

**Example:** lambda capturing outer variable
    Given val multiplier = 10
    Given val multiply = \x: x * multiplier

**Example:** nested lambda calls
    Given val double = \x: x * 2
    Given val add_one = \x: x + 1

**Example:** lambda with no params
    Given val answer = \: 42

## Feature: Basic Futures

## Future Creation and Await

    Tests future() creation and await semantics.
    Skipped because await keyword is not supported by runtime parser.

## Feature: Async Functions

## Async Function Semantics

    Tests async fn declaration and execution.
    Skipped because async fn syntax is not supported by runtime parser.

## Feature: Basic Generators

## Generator Creation and Iteration

    Tests generator() creation and next() semantics.
    Skipped because generator/yield syntax is not supported by runtime parser.

## Feature: Await Non-Future Error

## Type Checking for Await

    Tests that await requires Future type.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | await requires future type | pass |

## Feature: Generator State Machine

## State Preservation

    Tests generator state preservation across yields.

## Feature: Future with Captures

## Closure Capture in Futures

    Tests future capturing outer variables.

## Feature: Actor Spawn

## Basic Actor Creation

    Tests spawn for actor creation.

## Feature: Generator with State and Capture

## Combined State and Capture

    Tests generators with both state machine and captures.

## Feature: Control Flow Parity

## Interpreter/Codegen Parity

    Tests that control flow works in both modes.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | nested control flow | pass |
| 2 | recursive function | pass |

**Example:** nested control flow
    Given var sum = 0
    Given var i = 0

## Feature: Data Structure Parity

## Struct/Enum/Array Parity

    Tests data structures in both modes.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | struct field access | pass |
| 2 | array operations | pass |
| 3 | dictionary access | pass |

**Example:** struct field access
    Given val p = Point(x: 10, y: 20)

**Example:** array operations
    Given val arr = [10, 20, 30, 40, 50]
    Given var sum = 0
    Given var i = 0

**Example:** dictionary access
    Given val d = {"a": 10, "b": 20, "c": 30}

## Feature: Function Parity

## Function Call Parity

    Tests function calls in both modes.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | function composition | pass |
| 2 | early return | pass |
| 3 | boolean logic | pass |

**Example:** early return
    Given var i = 1


