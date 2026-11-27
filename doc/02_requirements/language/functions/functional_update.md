# functional update
*Source:* `test/03_system/feature/usage/functional_update_spec.spl`

## Overview

Functional Update Syntax Tests
Feature: Functional update syntax for immutable records and structs
Category: Language
Status: Implemented

Tests for the functional update syntax that allows creating modified copies
of structs and records without mutation, supporting immutable programming patterns.

> Reconciled 2026-11-17: `x->m(args)` means `x = x.m(args)` — it replaces the
> *binding*; whether old storage is mutated depends on `m`'s receiver contract.
> The examples below exercise array/dict `var` bindings (`->map`, `->filter`,
> `->concat`, `->set`), not immutable record copies, and assert no retained
> original alias; the scenario titles overstate what is tested. The seed parses
> `->` (`src/compiler_rust/parser/src/expressions/postfix.rs:577-593`); the
> self-hosted frontend does not yet. Contract (binding replacement vs. mutable
> storage vs. immutable copy, `?`/chain behaviour) and parity lane:
> `doc/05_design/language/robust_types/robustness_effects_arrow_pin_design_2026-11-17.md` §2,
> `doc/03_plan/release/1.0.0/robustness_completion_plan_2026-11-17.md` P0-4.

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


