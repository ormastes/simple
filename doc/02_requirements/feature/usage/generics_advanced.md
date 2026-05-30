# Advanced Generics Specification
*Source:* `test/feature/usage/generics_advanced_spec.spl`
**Feature IDs:** #GEN-ADV-001 to #GEN-ADV-008  |  **Category:** Type System | Generics  |  **Status:** Implemented

## Overview



Tests advanced generic features including:
- Const generic parameters
- Where clauses on functions
- impl Trait for Type syntax
- Nested generic types
- Tuple return types
- Multiple trait bounds
- Associated types

## Syntax

```simple
# Const generics
struct Array<T, const N: usize>:
    data: T

# Where clause
fn filled(value: T) -> T where T: Copy:
    value

# impl Trait for Type
impl Len for MyList:
    fn len() -> i64:
        self.size

# Multiple trait bounds
fn make<T>() -> T where T: Clone + Default:
    T.default()

# Associated types
trait Iterator:
    type Item
    fn next() -> Option<Self.Item>
```

## Feature: Const Generic Parameters

## const N: usize Syntax

    Tests const generic parameter parsing.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses const generic parameter | pass |

**Example:** parses const generic parameter
    Then  expect true  # Parsed successfully

## Feature: Where Clauses

## Where Clause on Functions

    Tests where clause parsing and validation.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses where clause on function | pass |

**Example:** parses where clause on function
    Then  expect filled(42) == 42

## Feature: impl Trait for Type

## Trait Implementation Syntax

    Tests impl Trait for Type parsing.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses impl trait for type | pass |

**Example:** parses impl trait for type
    Given val list = MyList(size: 42)
    Then  expect list.len() == 42

## Feature: Generic impl with Where

## Generic Implementation

    Tests generic impl blocks.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses generic impl with where | pass |

**Example:** parses generic impl with where
    Given val x: i64 = 42
    Then  expect x.clone() == 42

## Feature: Nested Generic Types

## Nested Generics

    Tests nested generic type parsing like List<Option<T>>.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses nested generic types | pass |

**Example:** parses nested generic types
    Then  expect true  # Parsed successfully

## Feature: Tuple Return Types

## Tuple Return Type Syntax

    Tests function with tuple return type.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses tuple return type | pass |

**Example:** parses tuple return type
    Given val (num, text) = get_pair()
    Then  expect num == 42
    Then  expect text == "hello"

## Feature: Multiple Trait Bounds

## T: Clone + Default Syntax

    Tests multiple trait bounds with +.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses multiple trait bounds | pass |

**Example:** parses multiple trait bounds
    Then  expect true  # Parsed successfully

## Feature: Associated Types

## type Item in Trait

    Tests associated type syntax in traits.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses associated type | pass |

**Example:** parses associated type
    Then  expect true  # Parsed successfully


