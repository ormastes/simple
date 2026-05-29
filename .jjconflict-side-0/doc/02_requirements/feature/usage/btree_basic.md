# btree basic
*Source:* `test/feature/usage/btree_basic_spec.spl`
**Category:** System/Collections  |  **Status:** Active

## Overview

BTreeMap Basic Operations System Test


## Description

Integration tests for BTreeMap (ordered map) basic operations through the FFI layer.

Tests cover:
- Map creation and initialization
- Key-value insertion and retrieval
- Key ordering maintenance
- Key existence checking and removal
- Collection mutations (clear)
- Array/collection views (keys, values)

**Integration Scope:** BTreeMap + Collections FFI
**Complexity:** Low
**Coverage Impact:** btreemap.rs (0%→40%), collections FFI

## Feature: BTreeMap basic operations

System-level tests for BTreeMap operations.

    Validates BTreeMap maintains sorted order while supporting
    insertion, retrieval, removal, and iteration through the Rust FFI layer.

### Scenario: Creation and insertion

| # | Example | Status |
|---|---------|--------|
| 1 | creates new BTreeMap | pass |
| 2 | inserts and retrieves values | pass |
| 3 | maintains sorted order | pass |

**Example:** creates new BTreeMap
    Given val map = BTreeMap.new()
    Then  expect(map).not_to(be_nil())
    Then  expect(map.is_empty()).to_equal(true)

**Example:** inserts and retrieves values
    Given var map = BTreeMap.new()
    Given val result = map.get("key1")
    Then  expect(result).to_equal("value1")

**Example:** maintains sorted order
    Given var map = BTreeMap.new()
    Given val keys = map.keys()
    Then  expect(keys.len()).to_equal(3)

### Scenario: Key operations

| # | Example | Status |
|---|---------|--------|
| 1 | checks if key exists | pass |
| 2 | removes keys | pass |

**Example:** checks if key exists
    Given var map = BTreeMap.new()
    Then  expect(map.contains_key("exists")).to_equal(true)
    Then  expect(map.contains_key("missing")).to_equal(false)

**Example:** removes keys
    Given var map = BTreeMap.new()
    Then  expect(map.contains_key("key")).to_equal(false)
    Then  expect(map.len()).to_equal(0)

### Scenario: Collection methods

| # | Example | Status |
|---|---------|--------|
| 1 | clears all entries | pass |
| 2 | gets all values | pass |

**Example:** clears all entries
    Given var map = BTreeMap.new()
    Then  expect(map.is_empty()).to_equal(true)

**Example:** gets all values
    Given var map = BTreeMap.new()
    Given val values = map.values()
    Then  expect(values.len()).to_equal(2)


