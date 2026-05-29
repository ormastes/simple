# Structs Specification
*Source:* `test/feature/usage/structs_spec.spl`
**Feature IDs:** #TBD  |  **Category:** Language  |  **Status:** Implemented

## Overview



## Overview

Structs are user-defined data types that group related fields together.
They support named fields with type annotations, default values, and can
have methods defined via impl blocks. Structs are the primary way to
define custom data structures in Simple.

## Syntax

```simple
struct Point:
    x: i64
    y: i64

struct Config:
    host: String = "localhost"
    port: i64 = 8080

val p = Point { x: 3, y: 4 }
val c = Config { port: 9000 }  # host uses default
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Struct | User-defined data type with named fields |
| Field | Named member of a struct with type annotation |
| Default Value | Optional value used when field not provided |
| Construction | Creating struct instance with field values |

## Behavior

- Fields are accessed using dot notation: `point.x`
- Construction requires all fields without defaults
- Fields can have default values
- Structs are value types (copied by default)

## Feature: Structs

## Core Struct Functionality

    Tests for struct definition, construction, field access, and default values.
    Validates struct behavior as value types with named fields.

### Scenario: struct definition and construction

### Scenario: Struct Creation

        Defines and constructs structs with typed fields.

| # | Example | Status |
|---|---------|--------|
| 1 | defines struct with fields | pass |
| 2 | constructs struct with all fields | pass |

**Example:** defines struct with fields
    Given val p = Point { x: 10, y: 20 }
    Then  expect p.x + p.y == 30

**Example:** constructs struct with all fields
    Given val c = Config { host: "localhost", port: 8080 }
    Then  expect c.port == 8080

### Scenario: struct field access

### Scenario: Accessing Struct Fields

        Reads field values using dot notation.

| # | Example | Status |
|---|---------|--------|
| 1 | accesses struct fields | pass |

**Example:** accesses struct fields
    Given val r = Rectangle { width: 10, height: 5 }
    Then  expect r.width * r.height == 50

## Feature: Impl Blocks

## Methods via Impl Blocks

    Tests for adding methods to structs using impl blocks.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | adds method to struct | pass |
| 2 | adds method with arguments | pass |

**Example:** adds method to struct
    Given val p = Point { x: 15, y: 25 }
    Then  expect p.sum() == 40

**Example:** adds method with arguments
    Given val c = Counter { value: 10 }
    Then  expect c.add(5) == 15

## Feature: Classes

## Class Definitions

    Tests for classes with static methods.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | defines class with static method | pass |

**Example:** defines class with static method
    Then  expect Calculator.add(3, 4) == 7

## Feature: Context Blocks

## Context Block Syntax

    Tests for context blocks that provide implicit receiver.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | dispatches methods to context object | pass |
| 2 | accesses self fields in context | pass |

**Example:** dispatches methods to context object
    Given val calc = Calculator {}
    Given var res = 0
    Then  expect res == 42

**Example:** accesses self fields in context
    Given val a = Adder { base: 30 }
    Given var res = 0
    Then  expect res == 42

## Feature: Method Missing

## Dynamic Method Handling

    Tests for method_missing to handle undefined methods.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | calls method_missing for unknown method | pass |
| 2 | passes arguments to method_missing | pass |

**Example:** calls method_missing for unknown method
    Given val d = DSL {}
    Then  expect d.unknown_method() == 42

**Example:** passes arguments to method_missing
    Given val x = args[0]
    Given val m = Multiplier { factor: 7 }
    Then  expect m.any_method(6) == 42


