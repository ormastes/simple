# hashset basic
*Source:* `test/feature/usage/hashset_basic_spec.spl`
**Category:** System/Collections  |  **Status:** Active

## Overview

HashSet Basic Operations System Test


## Description

Integration tests for HashSet basic operations through the FFI layer.

Tests cover:
- Set creation and initialization
- Element insertion and deduplication
- Membership testing (contains/remove)
- Collection mutations (clear)
- Array conversion

**Integration Scope:** HashSet + Collections FFI
**Complexity:** Low
**Coverage Impact:** hashset.rs (0%→40%), collections FFI

## Feature: HashSet basic operations

System-level tests for HashSet operations.

    Validates HashSet behaves correctly through the Rust FFI layer,
    including insertion, deduplication, removal, and iteration.

### Scenario: Creation and insertion

| # | Example | Status |
|---|---------|--------|
| 1 | creates new HashSet | pass |
| 2 | inserts elements | pass |
| 3 | handles duplicate insertions | pass |

**Example:** creates new HashSet
    Given var set = HashSet.new()
    Then  expect(set).not_to(be_nil())
    Then  expect(set.is_empty()).to_equal(true)

**Example:** inserts elements
    Given var set = HashSet.new()
    Then  expect(set.len()).to_equal(3)
    Then  expect(set.contains("1")).to_equal(true)
    Then  expect(set.contains("2")).to_equal(true)

**Example:** handles duplicate insertions
    Given var set = HashSet.new()
    Then  expect(set.len()).to_equal(2)
    Then  expect(set.contains("cat")).to_equal(true)
    Then  expect(set.contains("dog")).to_equal(true)

### Scenario: Membership testing

| # | Example | Status |
|---|---------|--------|
| 1 | checks if element exists | pass |
| 2 | removes elements | pass |

**Example:** checks if element exists
    Given var set = HashSet.new()
    Then  expect(set.contains("exists")).to_equal(true)
    Then  expect(set.contains("missing")).to_equal(false)

**Example:** removes elements
    Given var set = HashSet.new()
    Given val removed = set.remove("42")
    Then  expect(removed).to_equal(true)
    Then  expect(set.contains("42")).to_equal(false)

### Scenario: Collection operations

| # | Example | Status |
|---|---------|--------|
| 1 | clears all elements | pass |
| 2 | converts to vec | pass |

**Example:** clears all elements
    Given var set = HashSet.new()
    Then  expect(set.is_empty()).to_equal(true)
    Then  expect(set.len()).to_equal(0)

**Example:** converts to vec
    Given var set = HashSet.new()
    Given val arr = set.to_vec()
    Then  expect(arr.len()).to_equal(3)


