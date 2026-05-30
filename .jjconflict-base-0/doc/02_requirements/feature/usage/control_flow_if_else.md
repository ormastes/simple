# Control Flow - If/Else Specification
*Source:* `test/feature/usage/control_flow_if_else_spec.spl`
**Feature IDs:** #1001  |  **Category:** Language  |  **Status:** In Progress

## Overview



use std.text.{NL}

Tests for conditional control flow using if/else statements.
Verifies correct evaluation of conditions and execution of appropriate branches.

## Feature: Control Flow - If/Else

Tests for if/else conditional statements and branching behavior.
    Verifies that conditions are properly evaluated and the correct branch executes.

### Scenario: basic if statements

### Scenario: Basic If Condition

        Tests simple if statements with true and false conditions.

| # | Example | Status |
|---|---------|--------|
| 1 | executes if body when condition is true | pass |
| 2 | skips if body when condition is false | pass |

**Example:** executes if body when condition is true
    Given val x = 5
    Given var result = 0
    Then  expect result == 10

**Example:** skips if body when condition is false
    Given val x = -5
    Given var result = 0
    Then  expect result == 0

### Scenario: if-else statements

### Scenario: If-Else Branches

        Tests that if-else correctly selects between two branches.

| # | Example | Status |
|---|---------|--------|
| 1 | executes if body when condition is true | pass |
| 2 | executes else body when condition is false | pass |

**Example:** executes if body when condition is true
    Given val x = 10
    Given var result = ""
    Then  expect result == "greater"

**Example:** executes else body when condition is false
    Given val x = 3
    Given var result = ""
    Then  expect result == "less"

### Scenario: nested if statements

### Scenario: Nested Conditions

        Tests nested if-else statements with multiple levels of conditions.

| # | Example | Status |
|---|---------|--------|
| 1 | handles nested if statements | pass |
| 2 | handles nested if-else | pass |

**Example:** handles nested if statements
    Given val x = 10
    Given val y = 20
    Given var result = 0
    Then  expect result == 1

**Example:** handles nested if-else
    Given val x = 3
    Given val y = 20
    Given var result = 0
    Then  expect result == 2

### Scenario: if-else-if chains

### Scenario: Multiple Conditions

        Tests chaining multiple else-if conditions.

| # | Example | Status |
|---|---------|--------|
| 1 | evaluates first matching condition | pass |
| 2 | executes final else when no conditions match | pass |

**Example:** evaluates first matching condition
    Given val x = 15
    Given var result = ""
    Then  expect result == "medium"

**Example:** executes final else when no conditions match
    Given val x = 100
    Given var result = ""
    Then  expect result == "high"

### Scenario: if with boolean expressions

### Scenario: Complex Conditions

        Tests if statements with compound boolean expressions.

| # | Example | Status |
|---|---------|--------|
| 1 | evaluates AND conditions | pass |
| 2 | evaluates OR conditions | pass |
| 3 | evaluates NOT conditions | pass |

**Example:** evaluates AND conditions
    Given val a = 5
    Given val b = 10
    Given var result = false
    Then  expect result == true

**Example:** evaluates OR conditions
    Given val a = -5
    Given val b = 10
    Given var result = false
    Then  expect result == true

**Example:** evaluates NOT conditions
    Given val x = 5
    Given var result = false
    Then  expect result == true


