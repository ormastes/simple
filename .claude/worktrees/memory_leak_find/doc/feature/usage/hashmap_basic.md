# HashMap Basic Operations Specification
*Source:* `test/feature/usage/hashmap_basic_spec.spl`
**Category:** Stdlib  |  **Status:** Implemented

## Overview



System tests for basic HashMap operations through the FFI layer.
Tests creation, insertion, retrieval, and collection operations.

## Integration Scope

HashMap + Collections FFI

## Complexity

Low

## Coverage Impact

hashmap.rs (0%→40%), collections FFI

## Feature: HashMap Basic Operations

Verifies basic HashMap functionality through the FFI layer.
    Covers creation, insertion, retrieval, key operations, and collection methods.

## Feature: Creation and insertion

Tests HashMap initialization and basic insert/retrieve operations.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | creates new HashMap | pass |
| 2 | inserts and retrieves values | pass |
| 3 | handles multiple insertions | pass |

**Example:** creates new HashMap
    Given var map = HashMap.new()
    Then  expect(map).not_to(be_nil())
    Then  expect(map.is_empty()).to_equal(true)

**Example:** inserts and retrieves values
    Given var map = HashMap.new()
    Given val result = map.get("key1")
    Then  expect(result).to_equal(Some("value1"))

**Example:** handles multiple insertions
    Given var map = HashMap.new()
    Then  expect(map.len()).to_equal(3)
    Then  expect(map.get("a")).to_equal(Some(1))
    Then  expect(map.get("b")).to_equal(Some(2))
    Then  expect(map.get("c")).to_equal(Some(3))

## Feature: Key operations

Tests key-related operations like existence checks and removal.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | checks if key exists | pass |
| 2 | removes keys | pass |
| 3 | gets all keys | pass |

**Example:** checks if key exists
    Given var map = HashMap.new()
    Then  expect(map.contains_key("exists")).to_equal(true)
    Then  expect(map.contains_key("missing")).to_equal(false)

**Example:** removes keys
    Given var map = HashMap.new()
    Given val removed = map.remove("key")
    Then  expect(removed).to_equal(Some("value"))
    Then  expect(map.contains_key("key")).to_equal(false)

**Example:** gets all keys
    Given var map = HashMap.new()
    Given val keys = map.keys()
    Then  expect(keys.len()).to_equal(2)

## Feature: Collection methods

Tests collection-level operations like clear and values retrieval.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | clears all entries | pass |
| 2 | gets all values | pass |

**Example:** clears all entries
    Given var map = HashMap.new()
    Then  expect(map.is_empty()).to_equal(true)
    Then  expect(map.len()).to_equal(0)

**Example:** gets all values
    Given var map = HashMap.new()
    Given val values = map.values()
    Then  expect(values.len()).to_equal(2)


