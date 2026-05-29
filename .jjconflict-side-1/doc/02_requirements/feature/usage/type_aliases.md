# Type Aliases Specification
*Source:* `test/feature/usage/type_aliases_spec.spl`
**Feature IDs:** #TYPE-ALIAS-001 to #TYPE-ALIAS-012  |  **Category:** Language  |  **Status:** Implemented

## Overview



## Overview

Type aliases allow creating alternative names for existing types, improving
code readability and maintainability. They enable domain-specific naming
without introducing new types, and support generic type aliases for
parameterized type shortcuts.

## Syntax

```simple
type UserId = i64
type IntList = [i64]
type StringMap = {str: str}
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Type Alias | Alternative name for an existing type |
| Collection Alias | Alias for array or dict types |
| Alias Chain | Alias that references another alias |

## Behavior

- Type aliases are fully interchangeable with their target type
- Aliases can reference collection types
- Aliases do not create new types (unlike newtypes)
- Aliases can reference other aliases (chaining)

## Feature: Type Aliases

## Core Type Alias Functionality

    Tests for defining and using type aliases including simple aliases,
    collection aliases, and alias chains.

### Scenario: with simple aliases

### Scenario: Simple Type Alias

        Creates an alternative name for an existing type.

| # | Example | Status |
|---|---------|--------|
| 1 | aliases primitive types | pass |
| 2 | allows alias in function signature | pass |
| 3 | is interchangeable with base type | pass |

**Example:** aliases primitive types
    Given val user: UserId = 42
    Then  expect user to eq(42)

**Example:** allows alias in function signature
    Given val result = double_score(21)
    Then  expect result to eq(42)

**Example:** is interchangeable with base type
    Given val age: Age = 25
    Given val result = process_int(age)
    Then  expect result to eq(35)

### Scenario: with collection aliases

### Scenario: Collection Type Alias

        Creates aliases for array and dict types.

| # | Example | Status |
|---|---------|--------|
| 1 | aliases array types | pass |
| 2 | aliases dict types | pass |
| 3 | allows nested collection aliases | pass |

**Example:** aliases array types
    Given val numbers: IntList = [1, 2, 3, 4, 5]
    Then  expect numbers.len() to eq(5)

**Example:** aliases dict types
    Given val data: StringMap = {"key": "value"}
    Then  expect data["key"] to eq("value")

**Example:** allows nested collection aliases
    Given val m: Matrix = [[1, 2], [3, 4]]
    Then  expect m[0][0] to eq(1)
    Then  expect m[1][1] to eq(4)

### Scenario: with alias chains

### Scenario: Alias Chain

        Creates an alias that references another alias.

| # | Example | Status |
|---|---------|--------|
| 1 | supports alias of alias | pass |
| 2 | supports multiple levels of aliasing | pass |

**Example:** supports alias of alias
    Given val user: UserId = 100
    Then  expect user to eq(100)

**Example:** supports multiple levels of aliasing
    Given val value: Top = 42
    Then  expect value to eq(42)

## Feature: Type Alias Usage

## Type Alias in Various Contexts

    Tests using type aliases in structs, classes, and complex expressions.

### Scenario: in struct fields

| # | Example | Status |
|---|---------|--------|
| 1 | uses alias in struct definition | pass |

**Example:** uses alias in struct definition
    Given val e = Event(time: 1234567890, name: "test")
    Then  expect e.time to eq(1234567890)

### Scenario: in class fields

| # | Example | Status |
|---|---------|--------|
| 1 | uses alias in class definition | pass |

**Example:** uses alias in class definition
    Given val c = Counter(value: 10)
    Then  expect c.get() to eq(10)

### Scenario: with return types

| # | Example | Status |
|---|---------|--------|
| 1 | uses alias as return type | pass |

**Example:** uses alias as return type
    Given val r: Result = compute()
    Then  expect r to eq(42)


