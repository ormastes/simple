# Simple Language Metaprogramming - Test Specification
*Source:* `test/feature/usage/metaprogramming_spec.spl`
**Feature IDs:** Various  |  **Status:** Partial Implementation

## Overview



**Source:** metaprogramming.md
**Type:** Extracted Examples
**Last Updated:** 2026-02-08

## Overview

This file contains executable test cases for metaprogramming features that are
currently implemented in Simple's runtime.

Tests cover: comprehensions, indexing, pattern matching, and basic error handling.

**Note:** Advanced features (DSL blocks, decorators, slicing, context managers, move closures)
are not yet fully implemented.

## Feature: Metaprogramming Spec

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | list comprehensions | pass |
| 2 | list comprehensions - transformation | pass |
| 3 | array indexing - basic | pass |
| 4 | array indexing - last element | pass |
| 5 | pattern matching - guard patterns | pass |
| 6 | pattern matching - simple matching | pass |
| 7 | error handling - safe division | pass |
| 8 | error handling - option pattern | pass |

**Example:** list comprehensions
    Given val evens = [for x in 0..10 if x % 2 == 0: x]
    Then  expect(evens[0]).to_equal(0)
    Then  expect(evens[1]).to_equal(2)
    Then  expect(evens[2]).to_equal(4)

**Example:** list comprehensions - transformation
    Given val squares = [for x in 1..6: x * x]
    Then  expect(squares[0]).to_equal(1)
    Then  expect(squares[1]).to_equal(4)
    Then  expect(squares[2]).to_equal(9)

**Example:** array indexing - basic
    Given val arr = [10, 20, 30, 40, 50]
    Then  expect(arr[0]).to_equal(10)
    Then  expect(arr[2]).to_equal(30)
    Then  expect(arr[4]).to_equal(50)

**Example:** array indexing - last element
    Given val arr = [10, 20, 30, 40, 50]
    Given val last = arr[arr.len() - 1]
    Then  expect(last).to_equal(50)

**Example:** pattern matching - guard patterns
    Then  expect(classify(-5)).to_equal("negative")
    Then  expect(classify(0)).to_equal("zero")
    Then  expect(classify(10)).to_equal("positive")

**Example:** pattern matching - simple matching
    Given val numbers = [10, 20, 30]
    Then  expect(find_value(numbers, 20)).to_equal("found")
    Then  expect(find_value(numbers, 99)).to_equal("not found")

**Example:** error handling - safe division
    Given val result1 = safe_divide(10, 2)
    Given val result2 = safe_divide(10, 0)
    Then  expect(result1).to_equal(5)
    Then  expect(result2).to_equal(0)

**Example:** error handling - option pattern
    Given val numbers = [1, 3, 6, 9]
    Given val result = find_first_even(numbers)
    Then  expect(result).to_equal(6)
    Given val odd_only = [1, 3, 5]
    Given val not_found = find_first_even(odd_only)
    Then  expect(not_found).to_equal(-1)


