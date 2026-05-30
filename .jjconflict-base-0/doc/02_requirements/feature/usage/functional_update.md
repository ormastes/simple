# functional update
*Source:* `test/feature/usage/functional_update_spec.spl`

## Overview

Functional Update Syntax Tests
Feature: Functional update syntax for immutable records and structs
Category: Language
Status: Implemented

Tests for the functional update syntax that allows creating modified copies
of structs and records without mutation, supporting immutable programming patterns.

## Feature: Functional Update Syntax

Tests for basic functional update patterns on structs and records.
    Verifies that copies are created with specific field modifications.

### Scenario: when updating a struct field

### Scenario: Single Field Update

        Tests updating a single field in a struct via functional update.

| # | Example | Status |
|---|---------|--------|
| 1 | creates new struct with updated field | pass |
| 2 | leaves original struct unchanged | pass |

**Example:** creates new struct with updated field
    Given var arr = [1, 2]
    Then  expect arr.len() == 4

**Example:** leaves original struct unchanged
    Given var arr = [1, 2, 3]
    Then  expect arr[1] == 4

### Scenario: when updating multiple fields

### Scenario: Multi-Field Update

        Tests updating several fields in a single functional update expression.

| # | Example | Status |
|---|---------|--------|
| 1 | updates all specified fields | pass |
| 2 | preserves unmodified fields | pass |

**Example:** updates all specified fields
    Given var arr = [1, 2, 3, 4, 5]
    Then  expect arr.len() == 3

**Example:** preserves unmodified fields
    Given var d = {"a": 1}
    Then  expect d.len() == 2

## Feature: Functional Update with Nesting

Tests for functional updates on nested structures,
    including lens-like patterns and deep updates.

### Scenario: when updating nested struct fields

### Scenario: Nested Functional Update

        Tests updating fields in nested structures.

| # | Example | Status |
|---|---------|--------|
| 1 | updates nested field values | pass |
| 2 | preserves sibling fields in nested structures | pass |

**Example:** updates nested field values
    Given var arr = [1, 2, 3]
    Then  expect arr.len() == 2

**Example:** preserves sibling fields in nested structures
    Given var d = {"x": 1, "y": 2}
    Then  expect d["x"] == 1
    Then  expect d["z"] == 3

### Scenario: when chaining functional updates

### Scenario: Update Chaining

        Tests chaining multiple functional updates in sequence.

| # | Example | Status |
|---|---------|--------|
| 1 | applies updates in correct order | pass |
| 2 | maintains immutability through chain | pass |

**Example:** applies updates in correct order
    Given var arr = [1, 2, 3]
    Then  expect arr == [3, 4]

**Example:** maintains immutability through chain
    Given var original = [1, 2, 3, 4, 5]
    Then  expect original == [20, 40]

## Feature: Functional Update Advanced Patterns

Tests for advanced functional update patterns,
    including conditional updates and integration with other features.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | works with generic types | pass |
| 2 | supports computed field values in update | pass |
| 3 | handles update expressions with side effects | pass |

**Example:** works with generic types
    Given var numbers = [10, 20, 30]
    Then  expect numbers == [1, 2, 3]

**Example:** supports computed field values in update
    Given var arr = [1, 2, 3, 4, 5]
    Given val threshold = 2
    Then  expect arr.len() == 3

**Example:** handles update expressions with side effects
    Given var items = [5, 10, 15, 20]
    Then  expect items == [5, 10, 15]


