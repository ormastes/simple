# Primitive Types Specification
*Source:* `test/feature/usage/primitive_types_spec.spl`
**Feature IDs:** #PRIM-001  |  **Category:** Language | Types  |  **Status:** Implemented

## Overview



## Overview

Tests for primitive types, type suffixes, union types, type aliases,
and generic types.

## Syntax

```simple
val x = 42i32                             # Type suffix
type Number = i64                         # Type alias
fn process(x: i64 | str) -> i64: ...      # Union type
fn identity<T>(x: T) -> T: x              # Generic function
```

## Feature: Enum Types

## Enum Comparison and Matching

    Tests for enum type operations.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | compares enum variants | pass |

**Example:** compares enum variants
    Given val c = Color.Green
    Given var result = 0
    Then  expect result == 0

## Feature: Union Types

## Union Type Annotations

    Tests for union types in function signatures.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | accepts union type parameter | pass |

**Example:** accepts union type parameter
    Then  expect test(10) == 42

## Feature: Type Aliases

## Type Alias Definitions

    Tests for type alias declarations.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | uses simple type alias | pass |

**Example:** uses simple type alias
    Then  expect double(21) == 42

## Feature: Optional Types

## Optional Type Syntax (T?)

    Tests for optional type annotations.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | accepts optional parameter | pass |

**Example:** accepts optional parameter
    Then  expect maybe_value(10) == 5

## Feature: Generic Functions

## Generic Function Definitions

    Tests for generic functions with type parameters.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | defines identity function | pass |
| 2 | uses two type parameters | pass |

**Example:** defines identity function
    Then  expect identity(42) == 42

**Example:** uses two type parameters
    Given val x = first(10, 20)
    Given val y = second(30, 40)
    Then  expect x + y == 50

## Feature: Generic Structs

## Generic Struct Definitions

    Tests for generic structs with type parameters.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | creates generic struct | pass |

**Example:** creates generic struct
    Given val b = Box { value: 42 }
    Then  expect b.value == 42

## Feature: Option Type Operations

## Option Some/None Operations

    Tests for Option type methods.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | unwraps Some value | pass |
| 2 | unwraps None with default | pass |
| 3 | checks is_some | pass |
| 4 | checks is_none | pass |
| 5 | maps Some value | pass |

**Example:** unwraps Some value
    Given val opt = Some(42)
    Then  expect opt.unwrap() == 42

**Example:** unwraps None with default
    Given val opt = None
    Then  expect opt.unwrap_or(99) == 99

**Example:** checks is_some
    Given val opt = Some(1)
    Given var result = 0
    Then  expect result == 1

**Example:** checks is_none
    Given val opt = None
    Given var result = 0
    Then  expect result == 1

**Example:** maps Some value
    Given val opt = Some(10)
    Given val res = opt.map(\x: x * 2)
    Then  expect res.unwrap() == 20

## Feature: Type Suffixes

## Numeric Type Suffixes

    Tests for numeric literals with type suffixes.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | uses i32 suffix | pass |
| 2 | uses i64 suffix | pass |
| 3 | uses u32 suffix | pass |
| 4 | uses unit suffix km | pass |
| 5 | uses unit suffix in expression | pass |
| 6 | uses f64 suffix | pass |
| 7 | uses f32 suffix | pass |

**Example:** uses i32 suffix
    Given val x = 42i32
    Then  expect x == 42

**Example:** uses i64 suffix
    Given val x = 100i64
    Then  expect x == 100

**Example:** uses u32 suffix
    Given val x = 255u32
    Then  expect x == 255

**Example:** uses unit suffix km
    Given val distance = 100_km
    Then  expect distance == 100

**Example:** uses unit suffix in expression
    Given val a = 50_m
    Given val b = 30_m
    Then  expect a + b == 80

**Example:** uses f64 suffix
    Given val x = 3.15f64
    Then  expect 1 == 1  # parsing test

**Example:** uses f32 suffix
    Given val x = 1.5f32
    Then  expect 1 == 1  # parsing test

## Feature: Strong Enums

## Strong Enum Exhaustive Matching

    Tests for #[strong] enum attribute.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | matches exhaustively without wildcard | pass |
| 2 | allows wildcard in weak enum | pass |

**Example:** matches exhaustively without wildcard
    Given val s = Status.Active
    Given var r = 0
    Then  expect r == 1

**Example:** allows wildcard in weak enum
    Given val s = Status.Active
    Given var result = 0
    Then  expect result == 1


