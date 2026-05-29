# Dictionary Grammar and Syntax Specification
*Source:* `test/feature/usage/dict_grammar_spec.spl`
**Feature IDs:** #1002, #1018  |  **Category:** Language, Syntax  |  **Status:** Complete

## Overview



use std.text.{NL}

Tests for dictionary literal syntax, ensuring correct grammar is used.
Verifies that {"key": value} syntax works correctly.

## Feature: Dictionary Grammar

Tests for dictionary literal syntax and grammar.
    Ensures proper key-value syntax is enforced.

### Scenario: basic dict syntax

### Scenario: Dictionary Literal Syntax

        Dictionaries use {"key": value} syntax with quoted keys.

| # | Example | Status |
|---|---------|--------|
| 1 | creates dict with string keys | pass |
| 2 | creates dict with integer values | pass |
| 3 | creates dict with mixed value types | pass |
| 4 | creates nested dicts | pass |
| 5 | creates empty dict | pass |

**Example:** creates dict with string keys
    Given val config = {"name": "Alice", "age": 30}
    Then  expect config["name"] == "Alice"
    Then  expect config["age"] == 30

**Example:** creates dict with integer values
    Given val scores = {"math": 95, "science": 87, "history": 92}
    Then  expect scores["math"] == 95

**Example:** creates dict with mixed value types
    Given val data = {"count": 42, "name": "test", "active": true}
    Then  expect data["count"] == 42
    Then  expect data["active"] == true

**Example:** creates nested dicts
    Given val nested = {"outer": {"inner": 123}}
    Then  expect nested["outer"]["inner"] == 123

**Example:** creates empty dict
    Given val empty: Dict<text, i32> = {}
    Then  expect empty.len() == 0

### Scenario: dict with arrays

### Scenario: Dictionaries Containing Arrays

        Tests dicts with array values.

| # | Example | Status |
|---|---------|--------|
| 1 | stores arrays as values | pass |
| 2 | stores nested structures | pass |

**Example:** stores arrays as values
    Given val data = {"numbers": [1, 2, 3], "letters": ["a", "b", "c"]}
    Then  expect data["numbers"][0] == 1
    Then  expect data["letters"][2] == "c"

**Example:** stores nested structures
    Given val complex = {
    Then  expect complex["users"][0]["name"] == "Alice"

### Scenario: dict operations

### Scenario: Dictionary Operations

        Tests insertion, update, deletion, and iteration.

| # | Example | Status |
|---|---------|--------|
| 1 | inserts new key-value pair | pass |
| 2 | updates existing value | pass |
| 3 | checks key existence | pass |
| 4 | gets keys | pass |
| 5 | gets values | pass |

**Example:** inserts new key-value pair
    Given var dict = {"a": 1}
    Then  expect dict["b"] == 2

**Example:** updates existing value
    Given var dict = {"x": 10}
    Then  expect dict["x"] == 20

**Example:** checks key existence
    Given val dict = {"key": "value"}
    Then  expect dict.contains_key("key")
    Then  expect not dict.contains_key("missing")

**Example:** gets keys
    Given val dict = {"a": 1, "b": 2, "c": 3}
    Given val keys = dict.keys()
    Then  expect keys.len() == 3

**Example:** gets values
    Given val dict = {"a": 1, "b": 2}
    Given val values = dict.values()
    Then  expect values.len() == 2

### Scenario: dict with optional chaining

### Scenario: Dict with Optional Values

        Using dicts with Option types and optional chaining.

| # | Example | Status |
|---|---------|--------|
| 1 | stores optional values | pass |
| 2 | uses optional chaining with dict access | pass |
| 3 | returns None for missing key with ? | pass |

**Example:** stores optional values
    Given val dict = {"present": Some(42), "absent": None}
    Then  expect dict["present"]? == Some(42)

**Example:** uses optional chaining with dict access
    Given val dict = {"key": Some("value")}
    Then  expect dict["key"]?.to_string() == Some("value")

**Example:** returns None for missing key with ?
    Given val dict = {"a": 1}
    Then  expect dict.get("missing") == None

### Scenario: dict type annotations

### Scenario: Dict Type Annotations

        Explicit type annotations for dictionaries.

| # | Example | Status |
|---|---------|--------|
| 1 | annotates string to int dict | pass |
| 2 | annotates string to string dict | pass |
| 3 | annotates complex value types | pass |

**Example:** annotates string to int dict
    Given val dict: Dict<text, i32> = {"one": 1, "two": 2}
    Then  expect dict["one"] == 1

**Example:** annotates string to string dict
    Given val dict: Dict<text, text> = {"greeting": "hello"}
    Then  expect dict["greeting"] == "hello"

**Example:** annotates complex value types
    Given val dict: Dict<text, [i32]> = {"nums": [1, 2, 3]}
    Then  expect dict["nums"].len() == 3


