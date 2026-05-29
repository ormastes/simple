# parser edge cases
*Source:* `test/feature/usage/parser_edge_cases_spec.spl`

## Overview

Parser Edge Cases Tests
Feature: Parser Edge Cases (Operators, Keywords, FFI)
Category: System, Parser
Status: In Progress

Tests for parser edge cases including:
- Matrix multiplication (@) operator
- Bitwise XOR (xor) keyword
- super keyword in inheritance
- Array type syntax [T]

## Feature: Parser Edge Cases

Tests for parser edge cases and bug fixes.

### Scenario: Matrix Multiplication Operator

| # | Example | Status |
|---|---------|--------|
| 1 | parses @ operator in expressions | pass |
| 2 | parses @ operator with variables | pass |

**Example:** parses @ operator in expressions
    Given val result = 3 @ 4
    Then  expect result == 12

**Example:** parses @ operator with variables
    Given val a = 2
    Given val b = 5
    Given val result = a @ b
    Then  expect result == 10

### Scenario: Bitwise XOR Keyword

| # | Example | Status |
|---|---------|--------|
| 1 | parses xor keyword in expressions | pass |
| 2 | parses xor keyword with variables | pass |
| 3 | parses xor in complex expressions | pass |

**Example:** parses xor keyword in expressions
    Given val result = 5 xor 3
    Then  expect result == 6

**Example:** parses xor keyword with variables
    Given val a = 12
    Given val b = 7
    Given val result = a xor b
    Then  expect result == 11

**Example:** parses xor in complex expressions
    Given val result = (5 xor 3) xor 1
    Then  expect result == 7

### Scenario: Array Type Syntax

| # | Example | Status |
|---|---------|--------|
| 1 | parses array types with square brackets | pass |
| 2 | parses array return types | pass |

**Example:** parses array types with square brackets
    Given val nums = [1, 2, 3]
    Given val result = takes_array(nums)
    Then  expect result.length() == 3

**Example:** parses array return types
    Given val result = make_array()
    Then  expect result[0] == "a"

### Scenario: Operator Precedence

| # | Example | Status |
|---|---------|--------|
| 1 | handles @ and xor together | pass |
| 2 | handles multiple operators | pass |

**Example:** handles @ and xor together
    Given val result = (3 @ 2) xor 5
    Then  expect result == 3  # (3 @ 2) = 6, 6 xor 5 = 3

**Example:** handles multiple operators
    Given val a = 10
    Given val b = 3
    Given val c = (a xor b) @ 2
    Then  expect c == 18  # 10 xor 3 = 9, 9 @ 2 = 18


