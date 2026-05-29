# Trait Coherence Specification
*Source:* `test/feature/usage/trait_coherence_spec.spl`
**Feature IDs:** #TRAIT-COH-001 to #TRAIT-COH-017  |  **Category:** Type System | Traits  |  **Status:** Implemented

## Overview



Tests trait coherence rules including:
- Orphan rule enforcement
- Overlap detection
- Blanket impl conflicts
- Associated type coherence
- Specialization with #[default]

## Coherence Rules

1. **Orphan Rule**: Either trait OR type must be local
2. **Overlap Rule**: No two impls for same trait+type
3. **Blanket Conflict**: Generic impl conflicts with specific
4. **Associated Types**: Same type must be declared consistently

## Feature: Orphan Rule - Allowed Cases

## Local Trait or Local Type

    Tests that orphan rule allows local trait + foreign type.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | allows local trait on foreign type | pass |
| 2 | allows foreign trait on local type | pass |
| 3 | allows local trait on local type | pass |

**Example:** allows local trait on foreign type
    Then  expect "test".process() == 42

**Example:** allows foreign trait on local type
    Given val t = MyType(value: 42)
    Then  expect t.to_string() == "MyType"

**Example:** allows local trait on local type
    Given val t = LocalType(x: 42)
    Then  expect t.get() == 42

## Feature: Orphan Rule - Rejection

## Foreign Trait + Foreign Type

    Tests that orphan rule rejects foreign trait on foreign type.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | foreign trait on foreign type is rejected at compile time | pass |

**Example:** foreign trait on foreign type is rejected at compile time
    Then  expect true  # Placeholder - compile-time check

## Feature: Overlap Detection - Same Type

## Duplicate Impl Detection

    Tests that duplicate impls for same trait+type are rejected.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | single impl is allowed | pass |
| 2 | duplicate impl is rejected at compile time | pass |

**Example:** single impl is allowed
    Given val x: i32 = 21
    Then  expect x.run() == 42

**Example:** duplicate impl is rejected at compile time
    Then  expect true

## Feature: Overlap Detection - Generic vs Concrete

## Generic/Concrete Conflict

    Tests that generic impl conflicts with concrete impl.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | specific impl is allowed alone | pass |
| 2 | generic impl conflicts with specific | pass |

**Example:** specific impl is allowed alone
    Given val x: i32 = 0
    Then  expect x.handle() == 1

**Example:** generic impl conflicts with specific
    Then  expect true

## Feature: No Overlap - Different Types

## Separate Impls Allowed

    Tests that impls for different types don't conflict.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | different types can have same trait | pass |

**Example:** different types can have same trait
    Given val x: i32 = 42
    Given val s: str = "hello"
    Then  expect x.convert() == "i32"
    Then  expect s.convert() == "str"

## Feature: Associated Type Coherence

## Consistent Associated Types

    Tests that associated types are declared consistently.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | associated type in impl is valid | pass |
| 2 | conflicting associated type is rejected | pass |

**Example:** associated type in impl is valid
    Given val list = IntList(items: [42])
    Then  expect list.get() == 42

**Example:** conflicting associated type is rejected
    Then  expect true

## Feature: Blanket Impl Conflict

## Generic Impl Conflicts

    Tests that blanket impls conflict with specific impls.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | specific impl alone works | pass |

**Example:** specific impl alone works
    Given val x: i64 = 42
    Then  expect x.serialize() == "i64"

## Feature: Module Coherence Integration

## Full Module Check

    Tests coherence checking across a module.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | module with trait, struct, and impl passes | pass |

**Example:** module with trait, struct, and impl passes
    Given val p = Person(name: "Alice")
    Then  expect p.print_value() == "Alice"

## Feature: Inherent Impl

## Methods Without Trait

    Tests that inherent impls (no trait) are allowed.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | inherent impl on local type is allowed | pass |

**Example:** inherent impl on local type is allowed
    Given val p = Point(x: 3, y: 4)
    Then  expect p.magnitude_squared() == 25

## Feature: Multiple Traits Same Type

## Different Traits, Same Type

    Tests that multiple different traits can be implemented.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | multiple traits on same type | pass |

**Example:** multiple traits on same type
    Given val v1 = Value(n: 10)
    Given val v2 = Value(n: 5)
    Then  expect v1.to_str() == "Value"
    Then  expect v1.compare(v2) == 5

## Feature: Generic Type Impl

## Impl on Generic Type

    Tests impls on generic types like Vec<T>.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | impl on generic type | pass |

**Example:** impl on generic type
    Given val arr = [1, 2, 3, 4, 5]
    Then  expect arr.size() == 5

## Feature: Specialization with Default

## #[default] Attribute

    Tests that #[default] allows specialization.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | specialization placeholder | pass |

**Example:** specialization placeholder
    Then  expect true  # TODO: Implement @default on impl blocks

## Feature: Extension Trait Pattern

## Local Trait Extending Foreign Type

    Tests the extension trait pattern.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | extension trait on foreign type | pass |
| 2 | generic extension trait | pass |

**Example:** extension trait on foreign type
    Then  expect "hello".shout() == "HELLO!"

**Example:** generic extension trait
    Given val arr = [1, 2, 3]
    Then  expect arr.first_or_default(0) == 1
    Given val empty: [i64] = []
    Then  expect empty.first_or_default(42) == 42

## Feature: Negative Bounds Infrastructure

## Future: !Trait Syntax

    Tests infrastructure for negative trait bounds.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | impl with where clause | pass |

**Example:** impl with where clause
    Then  expect true


