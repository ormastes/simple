# Pattern Matching Specification
*Source:* `test/feature/usage/pattern_matching_spec.spl`
**Feature IDs:** #PATTERN-MATCH  |  **Category:** Language  |  **Status:** Implemented

## Overview



Pattern matching provides a way to extract and deconstruct values using patterns.

## Key Behaviors

- Pattern matching deconstructs values into their components
- Variables bound in patterns are available in match arm bodies
- Patterns include literals, enums, tuples, records, and wildcards

## Feature: Basic Pattern Matching

## Literal and Wildcard Patterns

    Tests fundamental pattern matching with literals and wildcards.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | matches exact literal values | pass |
| 2 | matches with wildcard pattern | pass |
| 3 | binds value to variable | pass |

**Example:** matches exact literal values
    Then  expect classify(0) == 0
    Then  expect classify(1) == 1
    Then  expect classify(42) == 99

**Example:** matches with wildcard pattern
    Then  expect always_match(100) == 42
    Then  expect always_match(-1) == 42

**Example:** binds value to variable
    Then  expect double_it(5) == 10
    Then  expect double_it(0) == 0

## Feature: Tuple Pattern Matching

## Tuple Destructuring

    Tests pattern matching on tuples.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | matches tuple and extracts elements | pass |
| 2 | matches nested tuples | pass |
| 3 | matches with partial wildcard | pass |

**Example:** matches tuple and extracts elements
    Then  expect sum_pair((10, 20)) == 30

**Example:** matches nested tuples
    Then  expect extract_first(((5, 10), 20)) == 5

**Example:** matches with partial wildcard
    Then  expect get_first((42, 100)) == 42

## Feature: Enum Pattern Matching

## Enum Variant Matching

    Tests pattern matching on enum variants.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | matches Option Some variant | pass |
| 2 | matches Option None variant | pass |
| 3 | matches Result Ok variant | pass |

**Example:** matches Option Some variant
    Given val opt = Some(42)
    Given var result = 0
    Then  expect result == 42

**Example:** matches Option None variant
    Given val opt = nil
    Given var result = 0
    Then  expect result == -1

**Example:** matches Result Ok variant
    Given val res = Ok(100)
    Given var result = 0
    Then  expect result == 100

## Feature: Pattern Matching in Functions

## Function Return with Match

    Tests pattern matching integrated with function returns.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | uses match as expression | pass |
| 2 | matches multiple patterns | pass |

**Example:** uses match as expression
    Then  expect sign(10) == 1
    Then  expect sign(-5) == -1
    Then  expect sign(0) == 0

**Example:** matches multiple patterns
    Then  expect is_special(0) == true
    Then  expect is_special(1) == true
    Then  expect is_special(5) == false


