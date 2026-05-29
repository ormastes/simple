# Option Type Specification
*Source:* `test/feature/usage/option_type_spec.spl`
**Feature IDs:** #OPT-001  |  **Category:** Language  |  **Status:** Implemented

## Overview



## Overview

Tests for the Option type representing values that may or may not be present,
including constructors, pattern matching, and safe unwrapping mechanisms.

## Syntax

```simple
val maybe_value: Option<i32> = Some(42)
val no_value: Option<text> = nil

match maybe_value:
    Some(x) => print "Value is {x}"
    None => print "No value"

val unwrapped = maybe_value.unwrap()           # Raises if None
val safe = maybe_value.unwrap_or(0)            # Default if None
val mapped = maybe_value.map(\x: x * 2)        # Transform if Some
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Some | Option containing a value |
| None | Option representing absence of value |
| Unwrapping | Extracting value from Option |
| Safe Unwrap | Get value or default/error handling |
| Composition | Chaining operations on Options |

## Behavior

- Option<T> is generic over type T
- Some(value) contains a value of type T
- None represents absence (no value)
- Pattern matching provides exhaustive case handling
- map/filter/flat_map for functional composition
- unwrap() raises error, unwrap_or() provides default value
- Existence check with .? operator

## Feature: Option Type Basic Usage

## Option Construction and Access

    Verifies creation of Some/None values, basic unwrapping,
    and pattern matching with Option types.

### Scenario: Some values

| # | Example | Status |
|---|---------|--------|
| 1 | creates Some with value | pass |
| 2 | checks Some is some | pass |

**Example:** creates Some with value
    Given val opt = Some(42)
    Then  expect opt.unwrap() == 42

**Example:** checks Some is some
    Given val opt = Some(1)
    Then  expect opt.is_some()

### Scenario: None values

| # | Example | Status |
|---|---------|--------|
| 1 | creates None | pass |
| 2 | uses unwrap_or for None | pass |

**Example:** creates None
    Given val opt = nil
    Then  expect opt.is_none()

**Example:** uses unwrap_or for None
    Given val opt = nil
    Then  expect opt.unwrap_or(99) == 99

## Feature: Option Type Transformations

## Functional Composition

    Tests map, filter, flat_map, and other functional operations
    on Option values for elegant chaining and composition.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | maps Some value | pass |
| 2 | maps None returns None | pass |

**Example:** maps Some value
    Given val opt = Some(10)
    Given val res = opt.map(\x: x * 2)
    Then  expect res.unwrap() == 20

**Example:** maps None returns None
    Given val opt: Option<i64> = nil
    Given val res = opt.map(\x: x * 2)
    Then  expect res.is_none()

## Feature: Existence Check Operator

## .? Operator for Option

    Tests the existence check operator for concise Option handling.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | returns true for Some | pass |
| 2 | returns false for None | pass |

**Example:** returns true for Some
    Given val opt = Some(42)
    Then  expect opt.?

**Example:** returns false for None
    Given val opt: Option<i64> = nil
    Then  expect not opt.?


