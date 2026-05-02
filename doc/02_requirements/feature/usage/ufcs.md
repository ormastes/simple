# UFCS (Uniform Function Call Syntax) Specification
*Source:* `test/feature/usage/ufcs_spec.spl`
**Feature IDs:** #3100-3120  |  **Category:** Syntax  |  **Status:** Implemented

## Overview



## Overview

UFCS (Uniform Function Call Syntax) allows calling free functions using method syntax.
When `x.method()` is called, the compiler resolves in priority order:
1. Instance method on x's type (highest priority)
2. Trait method implemented by x's type
3. Free function `method(x)` where first param matches x's type (UFCS)

This enables fluent API chaining without requiring methods to be defined on types.

## Syntax

```simple
# Free function
fn double(x: i64) -> i64:
    x * 2

# Usage via UFCS
val n = 5
val result = n.double()    # Resolves to: double(n)
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| UFCS | Uniform Function Call Syntax - call free functions as methods |
| Resolution Priority | Instance > Trait > FreeFunction |
| Type Matching | First parameter type must be compatible with receiver |

## Implementation Notes

Files involved:
- `simple/compiler/hir.spl` - MethodResolution enum
- `simple/compiler/resolve.spl` - Resolution pass
- `simple/compiler/mir.spl` - Codegen support
- `simple/compiler/driver.spl` - Pipeline integration

## Feature: UFCS Basic Functionality

## Basic UFCS Usage

    Tests basic UFCS functionality where free functions are called
    using method syntax on values.

### Scenario: with integer values

| # | Example | Status |
|---|---------|--------|
| 1 | calls math.abs via dot notation | pass |
| 2 | calls math.sqrt via dot notation | pass |

**Example:** calls math.abs via dot notation
    Given val n = -5
    Given val result = n.abs()
    Then  expect result == 5

**Example:** calls math.sqrt via dot notation
    Given val x = 16.0
    Given val result = x.sqrt()
    Then  expect result == 4.0

### Scenario: with array values

| # | Example | Status |
|---|---------|--------|
| 1 | calls array.len via dot notation | pass |
| 2 | calls array.first via dot notation | pass |
| 3 | calls array.last via dot notation | pass |

**Example:** calls array.len via dot notation
    Given val arr = [1, 2, 3, 4, 5]
    Given val result = arr.len()
    Then  expect result == 5

**Example:** calls array.first via dot notation
    Given val arr = [10, 20, 30]
    Given val result = arr.first()
    Then  expect result == Some(10)

**Example:** calls array.last via dot notation
    Given val arr = [10, 20, 30]
    Given val result = arr.last()
    Then  expect result == Some(30)

## Feature: UFCS Method Chaining

## Chaining UFCS Calls

    Multiple UFCS calls can be chained together for fluent APIs.

### Scenario: chaining multiple UFCS calls

| # | Example | Status |
|---|---------|--------|
| 1 | chains abs and to_string | pass |
| 2 | chains array operations | pass |

**Example:** chains abs and to_string
    Given val n = -42
    Given val result = n.abs().to_string()
    Then  expect result == "42"

**Example:** chains array operations
    Given val arr = [1, 2, 3]
    Given val result = arr.len().to_string()
    Then  expect result == "3"

## Feature: UFCS Priority Ordering

## Resolution Priority

    Method calls resolve in priority order:
    1. Instance method on receiver's type (highest)
    2. Trait method implemented by receiver's type
    3. Free function (UFCS) (lowest)

    This ensures existing methods are not accidentally overridden.

### Scenario: instance method takes priority

| # | Example | Status |
|---|---------|--------|
| 1 | calls string.len method not free function | pass |
| 2 | calls array.push method | pass |

**Example:** calls string.len method not free function
    Given val s = "hello"
    Given val result = s.len()
    Then  expect result == 5

**Example:** calls array.push method
    Given var arr = [1, 2, 3]
    Then  expect arr.len() == 4

## Feature: UFCS Type Matching

## Type Compatibility

    For UFCS, the receiver type must be compatible with the
    first parameter type of the free function.

### Scenario: exact type matching

| # | Example | Status |
|---|---------|--------|
| 1 | matches i64 receiver with i64 parameter | pass |
| 2 | matches f64 receiver with f64 parameter | pass |

**Example:** matches i64 receiver with i64 parameter
    Given val n: i64 = -5
    Given val result = n.abs()
    Then  expect result == 5

**Example:** matches f64 receiver with f64 parameter
    Given val x: f64 = 16.0
    Given val result = x.sqrt()
    Then  expect result == 4.0

## Feature: UFCS Edge Cases

## Edge Cases and Special Scenarios

    Tests for edge cases in UFCS resolution and usage.

### Scenario: with zero and negative values

| # | Example | Status |
|---|---------|--------|
| 1 | works with zero | pass |
| 2 | works with negative float | pass |

**Example:** works with zero
    Given val n = 0
    Given val result = n.abs()
    Then  expect result == 0

**Example:** works with negative float
    Given val x = -3.14
    Given val result = x.abs()
    Then  expect result == 3.14

### Scenario: with empty collections

| # | Example | Status |
|---|---------|--------|
| 1 | len of empty array is zero | pass |
| 2 | first of empty array is None | pass |

**Example:** len of empty array is zero
    Given val arr: [i64] = []
    Given val result = arr.len()
    Then  expect result == 0

**Example:** first of empty array is None
    Given val arr: [i64] = []
    Given val result = arr.first()
    Then  expect result == None

### Scenario: receiver as expression

| # | Example | Status |
|---|---------|--------|
| 1 | works with literal receiver | pass |
| 2 | works with arithmetic expression receiver | pass |

**Example:** works with literal receiver
    Given val result = (-5).abs()
    Then  expect result == 5

**Example:** works with arithmetic expression receiver
    Given val result = (3 - 8).abs()
    Then  expect result == 5


