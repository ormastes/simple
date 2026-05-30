# Dictionary Types Specification
*Source:* `test/feature/usage/dictionary_types_spec.spl`
**Feature IDs:** #1002  |  **Category:** Language  |  **Status:** In Progress

## Overview



use std.text.{NL}

Tests for dictionary (map) types and their operations.
Verifies dictionary creation, access, modification, and iteration.

## Feature: Dictionary Types

Tests for dictionary/map types and their fundamental operations.
    Verifies creation, key-value access, modification, and iteration over dictionaries.

### Scenario: dictionary creation

### Scenario: Creating Dictionaries

        Tests various ways to create dictionaries with different types.

| # | Example | Status |
|---|---------|--------|
| 1 | creates empty dictionary | pass |
| 2 | creates dictionary with initial values | pass |
| 3 | creates dictionary with string keys and values | pass |

**Example:** creates empty dictionary
    Given val empty: Dict<text, i32> = {}
    Then  expect empty.len() == 0

**Example:** creates dictionary with initial values
    Given val dict = {"a": 1, "b": 2, "c": 3}
    Then  expect dict.len() == 3

**Example:** creates dictionary with string keys and values
    Given val dict = {"name": "Alice", "city": "NYC"}
    Then  expect dict.len() == 2

### Scenario: dictionary access

### Scenario: Accessing Dictionary Values

        Tests retrieving values by key and checking key existence.

| # | Example | Status |
|---|---------|--------|
| 1 | retrieves value by key | pass |
| 2 | returns null for missing key | pass |
| 3 | checks key existence | pass |

**Example:** retrieves value by key
    Given val dict = {"a": 1, "b": 2}
    Then  expect dict["a"] == 1

**Example:** returns null for missing key
    Given val dict = {"a": 1}
    Given val value = dict.get("missing")
    Then  expect value == nil

**Example:** checks key existence
    Given val dict = {"a": 1, "b": 2}
    Then  expect dict.contains("a") == true
    Then  expect dict.contains("c") == false

### Scenario: dictionary modification

### Scenario: Modifying Dictionary Content

        Tests adding, updating, and removing entries.

| # | Example | Status |
|---|---------|--------|
| 1 | adds new key-value pair | pass |
| 2 | updates existing value | pass |
| 3 | removes entry by key | pass |

**Example:** adds new key-value pair
    Given var dict = {"a": 1}
    Then  expect dict["b"] == 2
    Then  expect dict.len() == 2

**Example:** updates existing value
    Given var dict = {"a": 1}
    Then  expect dict["a"] == 10
    Then  expect dict.len() == 1

**Example:** removes entry by key
    Given var dict = {"a": 1, "b": 2}
    Then  expect dict.contains("a") == false
    Then  expect dict.len() == 1

### Scenario: dictionary iteration

### Scenario: Iterating Over Dictionaries

        Tests various ways to iterate through dictionary entries.

| # | Example | Status |
|---|---------|--------|
| 1 | iterates over keys | pass |
| 2 | iterates over values | pass |
| 3 | iterates over entries | pass |

**Example:** iterates over keys
    Given val dict = {"a": 1, "b": 2, "c": 3}
    Given var count = 0
    Then  expect count == 3

**Example:** iterates over values
    Given val dict = {"a": 1, "b": 2, "c": 3}
    Given var sum = 0
    Then  expect sum == 6

**Example:** iterates over entries
    Given val dict = {"a": 1, "b": 2}
    Given var count = 0
    Then  expect count == 2

### Scenario: dictionary methods

### Scenario: Dictionary Utility Methods

        Tests built-in dictionary methods for manipulation and inspection.

| # | Example | Status |
|---|---------|--------|
| 1 | gets dictionary size | pass |
| 2 | checks if dictionary is empty | pass |
| 3 | clears dictionary | pass |
| 4 | creates copy of dictionary | pass |

**Example:** gets dictionary size
    Given val dict = {"a": 1, "b": 2, "c": 3}
    Then  expect dict.len() == 3

**Example:** checks if dictionary is empty
    Given val empty: Dict<text, i32> = {}
    Given val full = {"a": 1}
    Then  expect empty.is_empty() == true
    Then  expect full.is_empty() == false

**Example:** clears dictionary
    Given var dict = {"a": 1, "b": 2}
    Then  expect dict.len() == 0
    Then  expect dict.is_empty() == true

**Example:** creates copy of dictionary
    Given val original = {"a": 1, "b": 2}
    Given val copy = original.clone()
    Then  expect copy["a"] == 1
    Then  expect copy.len() == original.len()

### Scenario: dictionary with multiple types

### Scenario: Mixed Value Types

        Tests dictionaries with different value types.

| # | Example | Status |
|---|---------|--------|
| 1 | stores different value types | pass |
| 2 | accesses values with correct types | pass |

**Example:** stores different value types
    Given val mixed = {"int": 1, "text": "hello", "float": 3.14}
    Then  expect mixed.len() == 3

**Example:** accesses values with correct types
    Given val dict = {"count": 5}
    Given val value = dict["count"]
    Then  expect value == 5

## Feature: Functional Dictionary Methods

Tests for functional-style dictionary operations.

### Scenario: set and merge

| # | Example | Status |
|---|---------|--------|
| 1 | sets key with functional update | pass |
| 2 | merges two dictionaries | pass |

**Example:** sets key with functional update
    Given var d = {"a": 1}
    Then  expect d["b"] == 2

**Example:** merges two dictionaries
    Given var d1 = {"a": 1}
    Given val d2 = {"b": 2}
    Then  expect d1.len() == 2

### Scenario: get with default

| # | Example | Status |
|---|---------|--------|
| 1 | gets value or default | pass |
| 2 | gets existing value instead of default | pass |

**Example:** gets value or default
    Given val d = {"a": 10}
    Then  expect d.get_or("b", 99) == 99

**Example:** gets existing value instead of default
    Given val d = {"a": 10}
    Then  expect d.get_or("a", 99) == 10

## Feature: Dictionary Comprehension

Tests for dict comprehension syntax.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | creates dict from comprehension | pass |

**Example:** creates dict from comprehension
    Given val arr = [1, 2, 3]
    Given val d = {x: x * x for x in arr}
    Then  expect d[2] == 4


