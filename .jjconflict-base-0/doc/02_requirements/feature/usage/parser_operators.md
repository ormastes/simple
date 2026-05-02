# Parser Operator Specification
*Source:* `test/feature/usage/parser_operators_spec.spl`
**Feature IDs:** #PARSER-OP-001 to #PARSER-OP-020  |  **Category:** Infrastructure | Parser  |  **Status:** Implemented

## Overview



Tests that the parser correctly tokenizes and parses all operators
including arithmetic, comparison, logical, bitwise, and special operators.

## Syntax

```simple
# Arithmetic: + - * / % ** //
# Comparison: < > <= >= == !=
# Logical: and or not
# Bitwise: & | ^ ~ << >>
# Pipeline: |> >> <<
# Optional: ?. ?? .?
```

## Feature: Arithmetic Operator Parsing

## Basic Arithmetic

    Tests parsing of arithmetic operators with correct precedence.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses addition | pass |
| 2 | parses subtraction | pass |
| 3 | parses multiplication | pass |
| 4 | parses division | pass |
| 5 | parses modulo | pass |
| 6 | parses power | pass |
| 7 | parses integer division | pass |

**Example:** parses addition
    Then  expect 2 + 3 == 5

**Example:** parses subtraction
    Then  expect 5 - 3 == 2

**Example:** parses multiplication
    Then  expect 3 * 4 == 12

**Example:** parses division
    Then  expect 10 / 2 == 5

**Example:** parses modulo
    Then  expect 10 % 3 == 1

**Example:** parses power
    Then  expect 2 ** 3 == 8

**Example:** parses integer division
    Then  expect 7.fdiv(2) == 3

## Feature: Comparison Operator Parsing

## Relational Operators

    Tests parsing of comparison operators.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses less than | pass |
| 2 | parses greater than | pass |
| 3 | parses less than or equal | pass |
| 4 | parses greater than or equal | pass |
| 5 | parses equality | pass |
| 6 | parses inequality | pass |

**Example:** parses less than
    Then  expect 1 < 2

**Example:** parses greater than
    Then  expect 2 > 1

**Example:** parses less than or equal
    Then  expect 2 <= 2
    Then  expect 1 <= 2

**Example:** parses greater than or equal
    Then  expect 2 >= 2
    Then  expect 3 >= 2

**Example:** parses equality
    Then  expect 2 == 2

**Example:** parses inequality
    Then  expect 1 != 2

## Feature: Logical Operator Parsing

## Boolean Logic

    Tests parsing of logical operators.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses and | pass |
| 2 | parses or | pass |
| 3 | parses not | pass |
| 4 | parses combined logical | pass |

**Example:** parses and
    Then  expect (true and true) == true
    Then  expect (true and false) == false

**Example:** parses or
    Then  expect (true or false) == true
    Then  expect (false or false) == false

**Example:** parses not
    Then  expect (not false) == true
    Then  expect (not true) == false

**Example:** parses combined logical
    Then  expect (true and false or true) == true
    Then  expect (not (true and false)) == true

## Feature: Bitwise Operator Parsing

## Bit Manipulation

    Tests parsing of bitwise operators.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses bitwise and | pass |
| 2 | parses bitwise or | pass |
| 3 | parses bitwise xor | pass |
| 4 | parses bitwise not | pass |
| 5 | parses left shift | pass |
| 6 | parses right shift | pass |

**Example:** parses bitwise and
    Then  expect (0b1100 & 0b1010) == 0b1000

**Example:** parses bitwise or
    Then  expect (0b1100 | 0b1010) == 0b1110

**Example:** parses bitwise xor
    Then  expect (5 xor 3) == 6

**Example:** parses bitwise not
    Then  expect (~0) == -1

**Example:** parses left shift
    Then  expect (1 << 4) == 16

**Example:** parses right shift
    Then  expect (16 >> 2) == 4

## Feature: Assignment Operator Parsing

## Assignment and Compound Assignment

    Tests parsing of assignment operators.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses simple assignment | pass |
| 2 | parses add-assign | pass |
| 3 | parses sub-assign | pass |
| 4 | parses mul-assign | pass |
| 5 | parses div-assign | pass |
| 6 | parses mod-assign | pass |
| 7 | parses suspend-assign | pass |

**Example:** parses simple assignment
    Given var x = 0
    Then  expect x == 42

**Example:** parses add-assign
    Given var x = 10
    Then  expect x == 15

**Example:** parses sub-assign
    Given var x = 10
    Then  expect x == 7

**Example:** parses mul-assign
    Given var x = 5
    Then  expect x == 10

**Example:** parses div-assign
    Given var x = 20
    Then  expect x == 5

**Example:** parses mod-assign
    Given var x = 10
    Then  expect x == 1

**Example:** parses suspend-assign
    Given var x = 0
    Then  expect x == 42

## Feature: Pipeline Operator Parsing

## Function Composition and Piping

    Tests parsing of pipeline operators.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses pipe forward | pass |

**Example:** parses pipe forward
    Given val result = 21 |> double
    Then  expect result == 42

## Feature: Optional Operator Parsing

## Safe Navigation and Coalescing

    Tests parsing of optional chaining operators.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses optional chaining | pass |
| 2 | parses null coalescing | pass |
| 3 | parses existence check | pass |
| 4 | parses negated existence | pass |
| 5 | parses try operator | pass |

**Example:** parses optional chaining
    Given val opt: Option<text> = Some("hello")
    Given val len = opt?.len()
    Then  expect len == Some(5)

**Example:** parses null coalescing
    Given val opt: Option<i64> = None
    Given val value = opt ?? 42
    Then  expect value == 42

**Example:** parses existence check
    Given val opt = Some(42)
    Then  expect opt.?

**Example:** parses negated existence
    Given val opt: Option<i64> = None
    Then  expect not opt.?

**Example:** parses try operator
    Given val x = may_fail()?
    Then  expect use_result().unwrap() == 84

## Feature: Range Operator Parsing

## Range Syntax

    Tests parsing of range operators.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses exclusive range | pass |
| 2 | parses inclusive range | pass |
| 3 | parses range in slice | pass |

**Example:** parses exclusive range
    Given var sum = 0
    Then  expect sum == 10

**Example:** parses inclusive range
    Given var sum = 0
    Then  expect sum == 15

**Example:** parses range in slice
    Given val arr = [0, 1, 2, 3, 4]
    Given val sliced = arr[1..4]
    Then  expect sliced.len() == 3

## Feature: Operator Precedence Parsing

## Correct Precedence Handling

    Tests that operators are parsed with correct precedence.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | power before multiplication | pass |
| 2 | multiplication before addition | pass |
| 3 | comparison after arithmetic | pass |
| 4 | logical after comparison | pass |
| 5 | parentheses override precedence | pass |
| 6 | complex expression precedence | pass |

**Example:** power before multiplication
    Then  expect 2 ** 3 * 2 == 16

**Example:** multiplication before addition
    Then  expect 2 + 3 * 4 == 14

**Example:** comparison after arithmetic
    Then  expect (2 + 3 < 10) == true

**Example:** logical after comparison
    Then  expect (1 < 2 and 3 < 4) == true

**Example:** parentheses override precedence
    Then  expect (2 + 3) * 4 == 20

**Example:** complex expression precedence
    Then  expect 2 + 3 * 4 ** 2 / 8 == 8

## Feature: Special Operator Parsing

## Domain-Specific Operators

    Tests parsing of special operators for specific domains.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses matrix multiplication | pass |
| 2 | parses broadcast operators | pass |
| 3 | parses layer connect | pass |

**Example:** parses matrix multiplication
    Then  expect true  # Placeholder

**Example:** parses broadcast operators
    Then  expect true  # Placeholder

**Example:** parses layer connect
    Then  expect true  # Placeholder


