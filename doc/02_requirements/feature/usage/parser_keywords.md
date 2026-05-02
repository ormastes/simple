# Parser Keywords Specification
*Source:* `test/feature/usage/parser_keywords_spec.spl`
**Feature IDs:** #PARSER-KW-001 to #PARSER-KW-020  |  **Category:** Infrastructure | Parser  |  **Status:** Implemented

## Overview


use std.text.{NL}

Tests that all Simple language keywords are correctly recognized and
parsed in their appropriate contexts.

## Feature: Variable Keyword Parsing

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | val declares immutable variable | pass |
| 2 | var declares mutable variable | pass |

**Example:** val declares immutable variable
    Given val x = 42
    Then  expect x == 42

**Example:** var declares mutable variable
    Given var x = 0
    Then  expect x == 42

## Feature: Control Flow Keyword Parsing

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses if statement | pass |
| 2 | parses elif statement | pass |
| 3 | parses while loop | pass |
| 4 | parses for loop | pass |
| 5 | parses break in loop | pass |
| 6 | parses continue in loop | pass |
| 7 | parses return statement | pass |
| 8 | parses match expression | pass |

**Example:** parses if statement
    Given val result = if true:
    Then  expect result == 1

**Example:** parses elif statement
    Given val x = 2
    Given val result = if x == 1:
    Then  expect result == "two"

**Example:** parses while loop
    Given var x = 0
    Then  expect x == 3

**Example:** parses for loop
    Given var sum = 0
    Then  expect sum == 6

**Example:** parses break in loop
    Given var x = 0
    Then  expect x == 5

**Example:** parses continue in loop
    Given var sum = 0
    Then  expect sum == 12

**Example:** parses return statement
    Then  expect early_return(-1) == 0
    Then  expect early_return(5) == 5

**Example:** parses match expression
    Given val result = match 42:
    Then  expect result == "forty-two"

## Feature: Logic Keyword Parsing

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses and operator | pass |
| 2 | parses or operator | pass |
| 3 | parses not operator | pass |
| 4 | parses in operator | pass |

**Example:** parses and operator
    Then  expect (true and true) == true
    Then  expect (true and false) == false
    Then  expect (false and true) == false

**Example:** parses or operator
    Then  expect (true or true) == true
    Then  expect (true or false) == true
    Then  expect (false or false) == false

**Example:** parses not operator
    Then  expect (not false) == true
    Then  expect (not true) == false

**Example:** parses in operator
    Then  expect 2 in [1, 2, 3]
    Then  expect not (5 in [1, 2, 3])

## Feature: Special Keyword Parsing

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses true | pass |
| 2 | parses false | pass |
| 3 | parses nil | pass |
| 4 | parses self in method | pass |

**Example:** parses true
    Given val x = true
    Then  expect x

**Example:** parses false
    Given val x = false
    Then  expect not x

**Example:** parses nil
    Given val x = nil
    Then  expect x == nil

**Example:** parses self in method
    Given val p = TestPoint(x: 42, y: 10)
    Then  expect p.get_x() == 42
    Then  expect p.get_y() == 10

## Feature: Function Keyword Parsing

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses fn declaration | pass |
| 2 | parses nested function | pass |
| 3 | parses lambda expression | pass |
| 4 | parses higher-order function | pass |

**Example:** parses fn declaration
    Then  expect add(3, 4) == 7

**Example:** parses nested function
    Then  expect outer(5) == 11

**Example:** parses lambda expression
    Given val double = \x: x * 2
    Then  expect double(5) == 10

**Example:** parses higher-order function
    Then  expect apply({NL}: n + 1, 5) == 6


