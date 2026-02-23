# Simple Language Type System - Test Specification
*Source:* `test/feature/usage/types_spec.spl`
**Feature IDs:** #20-29  |  **Status:** Stable (Basic Features)

## Overview


**Last Updated:** 2026-02-08
**Topics:** type-system
**Migrated From:** doc/spec/types.md

## Overview

Executable tests for Simple's type system basics: primitives, mutability, generics, and type inference.

Note: Advanced features (unit types, capability effects, suspension operators) are not yet implemented.

## Feature: Types Spec

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | basic type literals | pass |
| 2 | mutability rules - val and const | pass |
| 3 | mutable variables | pass |
| 4 | generic container - array | pass |
| 5 | option type basic usage | pass |

**Example:** basic type literals
    Given val s = "hello"
    Given val i = 42
    Given val b = true
    Given val f = 3.14
    Then  expect(s).to_equal("hello")
    Then  expect(i).to_equal(42)
    Then  expect(b).to_equal(true)

**Example:** mutability rules - val and const
    Given val y = 20
    Then  expect(y).to_equal(20)
    Then  expect(MAX).to_equal(100)

**Example:** mutable variables
    Given var count = 0
    Then  expect(count).to_equal(2)

**Example:** generic container - array
    Given val numbers = [1, 2, 3, 4, 5]
    Given val strings = ["a", "b", "c"]
    Then  expect(numbers[0]).to_equal(1)
    Then  expect(strings[1]).to_equal("b")

**Example:** option type basic usage
    Given val some_val = 42
    Given val none_val = nil
    Then  expect(some_val).to_equal(42)


