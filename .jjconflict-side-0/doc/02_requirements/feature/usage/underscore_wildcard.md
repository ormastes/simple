# Underscore Wildcard Specification
*Source:* `test/feature/usage/underscore_wildcard_spec.spl`
**Feature IDs:** #TBD  |  **Category:** Syntax  |  **Status:** Implemented

## Overview



## Overview

Tests for underscore (_) as a wildcard placeholder in various contexts:
- Lambda parameters: `\_: expr` to ignore arguments
- For loop patterns: `for _ in items:` to iterate without binding
- Match patterns: `case _:` as a catch-all wildcard

## Feature: Underscore Wildcard Support

## Wildcard Pattern Tests

    Verifies that underscore (_) works correctly as a wildcard pattern
    in lambdas, for loops, and match expressions.

## Feature: in lambda parameters

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | ignores single argument | pass |
| 2 | works in map to transform values | pass |

**Example:** ignores single argument
    Given val f = \_: 42
    Then  expect(f(100)).to_equal(42)
    Then  expect(f(0)).to_equal(42)
    Then  expect(f(-5)).to_equal(42)

**Example:** works in map to transform values
    Given val items = [1, 2, 3, 4, 5]
    Given val result = items.map(\_: 0)
    Then  expect(result.len()).to_equal(5)

## Feature: in for loop patterns

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | iterates without binding | pass |
| 2 | uses sum_n_times helper | pass |
| 3 | works with list iteration | pass |

**Example:** iterates without binding
    Given var total = 0
    Then  expect(total).to_equal(5)

**Example:** uses sum_n_times helper
    Then  expect(sum_n_times(value=10, n=3)).to_equal(30)
    Then  expect(sum_n_times(value=5, n=4)).to_equal(20)

**Example:** works with list iteration
    Given var count = 0
    Then  expect(count).to_equal(3)

## Feature: in match patterns

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | catches unmatched cases | pass |
| 2 | ignores enum payload | pass |

**Example:** catches unmatched cases
    Then  expect(classify_number(0)).to_equal("zero")
    Then  expect(classify_number(1)).to_equal("one")
    Then  expect(classify_number(2)).to_equal("two")
    Then  expect(classify_number(100)).to_equal("many")
    Then  expect(classify_number(-1)).to_equal("many")

**Example:** ignores enum payload
    Then  expect(is_some(MyOption.Some(42))).to_equal(true)
    Then  expect(is_some(MyOption.Some(0))).to_equal(true)
    Then  expect(is_some(MyOption.Nil)).to_equal(false)


