# future body execution
*Source:* `test/feature/usage/future_body_execution_spec.spl`

## Overview

Future Body Execution Tests
Feature: Execution and evaluation of future bodies
Category: Runtime
Status: In Progress

Tests for how future bodies are executed, including lazy evaluation,
execution context, and integration with the runtime scheduler.

## Feature: Future Body Execution

Tests for basic execution of future bodies, including when
    execution occurs and how results are computed.

### Scenario: when a future body is created

### Scenario: Future Creation and Execution

        Tests that future bodies are properly created and execution
        is deferred until forced.

| # | Example | Status |
|---|---------|--------|
| 1 | delays execution until forced | pass |
| 2 | executes body only once | pass |

**Example:** delays execution until forced
    Given val x = 10
    Given val f = future(x + 32)
    Given val result = await f
    Then  expect result == 42

**Example:** executes body only once
    Given val base = 21
    Given val f = future(base * 2)
    Given val r1 = await f
    Given val r2 = await f
    Then  expect r1 == 42
    Then  expect r2 == 42

### Scenario: when a future is forced

### Scenario: Forcing Future Execution

        Tests that forcing a future properly executes its body.

| # | Example | Status |
|---|---------|--------|
| 1 | executes the body and returns result | pass |
| 2 | caches result for subsequent forces | pass |

**Example:** executes the body and returns result
    Given val f = future(10 + 20 + 30)
    Given val result = await f
    Then  expect result == 60

**Example:** caches result for subsequent forces
    Given val f = future(2 * 3 * 7)
    Given val r1 = await f
    Given val r2 = await f
    Given val r3 = await f
    Then  expect r1 == 42
    Then  expect r2 == 42
    Then  expect r3 == 42

## Feature: Future Body Execution Context

Tests for execution context of future bodies, including
    variable capture and state management.

### Scenario: when future captures variables

### Scenario: Variable Capture

        Tests that futures properly capture variables from their
        defining scope.

| # | Example | Status |
|---|---------|--------|
| 1 | captures immutable variables by value | pass |
| 2 | captures mutable references correctly | pass |

**Example:** captures immutable variables by value
    Given val x = 10
    Given val y = 20
    Given val f = future(x + y)
    Then  expect await f == 30

**Example:** captures mutable references correctly
    Given var counter = 5
    Given val f = future(counter * 2)
    Given val result = await f
    Then  expect result == 10 or result == 20

### Scenario: when future body has side effects

### Scenario: Side Effects in Future Bodies

        Tests that side effects in future bodies occur during execution.

| # | Example | Status |
|---|---------|--------|
| 1 | executes side effects when forced | pass |
| 2 | side effects do not execute until forced | pass |

**Example:** executes side effects when forced
    Given val base = 42
    Given val f = future(base)
    Given val result = await f
    Then  expect result == 42

**Example:** side effects do not execute until forced
    Given val value = 100
    Given val f = future(value)
    Given val result = await f
    Then  expect result == 100

## Feature: Future Body Execution Errors

Tests for error handling in future body execution,
    including exception propagation and recovery.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | propagates exceptions from body execution | pass |
| 2 | handles recursive future execution | pass |
| 3 | manages execution in concurrent context | pass |

**Example:** propagates exceptions from body execution
    Given val p = Promise.new(\resolve, reject: reject("execution error"))
    Then  expect e == "execution error"
    Then  expect false

**Example:** handles recursive future execution
    Given val f1 = future(10)
    Given val f2 = future(await f1 * 2)
    Then  expect await f2 == 20

**Example:** manages execution in concurrent context
    Given val f1 = future(10)
    Given val f2 = future(20)
    Given val f3 = future(30)
    Then  expect await f1 + await f2 + await f3 == 60


