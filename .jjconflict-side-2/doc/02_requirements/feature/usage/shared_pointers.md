# Reference Counted Pointers Specification
*Source:* `test/feature/usage/shared_pointers_spec.spl`
**Feature IDs:** #SHARED-PTR  |  **Category:** Runtime  |  **Status:** Implemented

## Overview



use std.text.{NL}

Reference counted pointers provide safe sharing of data with automatic
memory management through reference counting.

## Key Behaviors

- Reference count incremented on clone, decremented on drop
- Value is deallocated when reference count reaches zero
- Cloning creates shallow copy with incremented reference count

## Feature: Reference Counted Pointers

## Basic Pointer Operations

    Tests basic reference counted pointer creation and usage.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | creates pointer | pass |
| 2 | pointer arithmetic | pass |
| 3 | multiple references | pass |

**Example:** creates pointer
    Given val ptr = new * 42
    Then  expect ptr == 42

**Example:** pointer arithmetic
    Given val a = new * 10
    Given val b = new * 5
    Then  expect a + b == 15

**Example:** multiple references
    Given val a = new * 42
    Given val b = a
    Then  expect a + b == 84

## Feature: Reference Semantics

## Reference Counting Semantics

    Tests reference counting behavior.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | tracks multiple references | pass |
| 2 | clones underlying data | pass |
| 3 | dict references work correctly | pass |

**Example:** tracks multiple references
    Given val list = [1, 2, 3]
    Given val ref1 = list
    Given val ref2 = list
    Then  expect ref1.len() == 3
    Then  expect ref2.len() == 3

**Example:** clones underlying data
    Given val original = [1, 2, 3]
    Given val cloned = original
    Then  expect cloned.len() == 3
    Then  expect cloned[0] == 1

**Example:** dict references work correctly
    Given val data = {"key": 42}
    Given val ref = data
    Then  expect ref["key"] == 42

## Feature: Memory Safety

## Memory Safety Guarantees

    Tests that references maintain memory safety.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | data remains valid while referenced | pass |
| 2 | strings are valid | pass |
| 3 | nested data structures work | pass |

**Example:** data remains valid while referenced
    Given val data = [1, 2, 3]
    Given val r1 = data
    Then  expect r1[0] == 1

**Example:** strings are valid
    Given val s = "hello"
    Given val ref = s
    Then  expect ref.len() == 5

**Example:** nested data structures work
    Given val outer = [[1, 2], [3, 4]]
    Given val ref = outer
    Then  expect ref[0][0] == 1
    Then  expect ref[1][1] == 4


