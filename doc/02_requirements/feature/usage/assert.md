# Assert Statement Specification
*Source:* `test/feature/usage/assert_spec.spl`
**Feature IDs:** #ASSERT-001 to #ASSERT-012  |  **Category:** Language | Contracts  |  **Status:** Implemented

## Overview



Tests assert statement support including:
- Basic assert with boolean condition
- Assert with custom error message
- Assert in functions
- Assert with expressions and boolean logic
- Assert in control flow (if blocks, loops)
- Assert combined with function contracts

## Syntax

```simple
# Basic assert
expect(x > 0).to_equal(true)

# Assert with message
expect(x > 0, "x must be positive").to_equal(true)

# Assert in function
fn validate(x: i64) -> i64:
    expect(x >= 0, "input must be non-negative").to_equal(true)
    x * 2
```

## Feature: Basic Assert Statement

## Simple Assertions

    Tests basic assert statement syntax.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | basic assert compiles | pass |
| 2 | assert with message compiles | pass |
| 3 | multiple assert conditions | pass |

**Example:** basic assert compiles
    Given val x = 10
    Then  expect(x > 0).to_equal(true)
    Then  expect x == 10

**Example:** assert with message compiles
    Given val x = 10
    Then  expect(x > 0, "x must be positive").to_equal(true)
    Then  expect x == 10

**Example:** multiple assert conditions
    Given val x = 5
    Then  expect(x < 100).to_equal(true)
    Then  expect(x >= 0, "x must be non-negative").to_equal(true)
    Then  expect x == 5

## Feature: Assert in Functions

## Function Body Assertions

    Tests assert inside function bodies.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | assert in function body | pass |
| 2 | multiple asserts in function | pass |

**Example:** assert in function body
    Then  expect(x >= 0, "input must be non-negative").to_equal(true)
    Then  expect(x < 1000).to_equal(true)
    Then  expect validate_and_compute(50) == 100

**Example:** multiple asserts in function
    Then  expect(x > 0).to_equal(true)
    Then  expect(y > 0).to_equal(true)
    Then  expect(x).to_not_equal(y, "x and y must be different")
    Then  expect validate(10, 20) == 30

## Feature: Assert with Expressions

## Complex Assert Conditions

    Tests assert with comparison and boolean expressions.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | assert with comparison | pass |
| 2 | assert with boolean logic | pass |

**Example:** assert with comparison
    Given val a = 10
    Given val b = 20
    Then  expect(a < b).to_equal(true)
    Then  expect(a + b).to_equal(30)
    Then  expect(a * 2).to_equal(b)
    Then  expect true

**Example:** assert with boolean logic
    Given val x = 10
    Given val y = 20
    Then  expect(x > 0 and y > 0).to_equal(true)
    Then  expect(x < 100 or y < 100).to_equal(true)
    Then  expect(not (x < 0)).to_equal(true)
    Then  expect true

## Feature: Assert in Control Flow

## Assertions in Branches and Loops

    Tests assert inside if blocks and loops.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | assert in if block | pass |
| 2 | assert in loop | pass |

**Example:** assert in if block
    Then  expect(x < 1000, "must be under 1000 in positive branch").to_equal(true)
    Then  expect(x >= -100, "must be at least -100").to_equal(true)
    Then  expect process(50) == 100

**Example:** assert in loop
    Given var total = 0
    Given var i = 0
    Then  expect(i >= 0, "iteration counter must be non-negative").to_equal(true)
    Then  expect sum_with_validation(5) == 10

## Feature: Assert with Function Contracts

## Combining Assert and Contracts

    Tests assert used alongside function contracts.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | assert combined with contracts | pass |

**Example:** assert combined with contracts
    Then  expect(x < 1000, "x must be reasonable").to_equal(true)
    Then  expect compute(50) == 60


