# Result Type Specification
*Source:* `test/feature/usage/result_type_spec.spl`
**Feature IDs:** #RESULT-001  |  **Category:** Language | Types  |  **Status:** Implemented

## Overview



use std.text.{NL}

## Overview

Tests for the Result type representing success or error outcomes,
including constructors, pattern matching, and safe unwrapping mechanisms.

## Syntax

```simple
val success: Result<i32, text> = Ok(42)
val failure: Result<i32, text> = Err("error")

match result:
    Ok(value) => print "Success: {value}"
    Err(msg) => print "Error: {msg}"

val unwrapped = result.unwrap()              # Raises if Err
val safe = result.unwrap_or(0)               # Default if Err
val propagated = fallible_operation()?       # Early return on Err
```

## Feature: Result Type Basic Usage

## Result Construction and Access

    Verifies creation of Ok/Err values, basic unwrapping,
    and pattern matching with Result types.

### Scenario: Ok values

| # | Example | Status |
|---|---------|--------|
| 1 | creates Ok with value | pass |
| 2 | checks Ok is ok | pass |
| 3 | checks Ok is not err | pass |

**Example:** creates Ok with value
    Given val res = Ok(42)
    Then  expect res.unwrap() == 42

**Example:** checks Ok is ok
    Given val res = Ok(10)
    Then  expect res.ok.?

**Example:** checks Ok is not err
    Given val res = Ok(5)
    Then  expect not res.err.?

### Scenario: Err values

| # | Example | Status |
|---|---------|--------|
| 1 | creates Err with error | pass |
| 2 | checks Err is not ok | pass |
| 3 | uses unwrap_or for Err | pass |

**Example:** creates Err with error
    Given val res = Err("error message")
    Then  expect res.err.?

**Example:** checks Err is not ok
    Given val res = Err("oops")
    Then  expect not res.ok.?

**Example:** uses unwrap_or for Err
    Given val res = Err("error")
    Then  expect res.unwrap_or(99) == 99

## Feature: Result from Functions

## Functions Returning Result

    Tests for functions that return Result types for error handling.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | returns Ok from function | pass |
| 2 | returns Err from function | pass |
| 3 | chains Result operations | pass |

**Example:** returns Ok from function
    Given val r = safe_divide(20, 4)
    Then  expect r.unwrap() == 5

**Example:** returns Err from function
    Given val r = safe_divide(10, 0)
    Then  expect r.unwrap_or(-1) == -1

**Example:** chains Result operations
    Given val r1 = step1(5)
    Given val r2 = r1.map(\x: step2(x).unwrap_or(-1))
    Then  expect r2.unwrap() == 30  # (5 + 10) * 2

## Feature: Question Mark Operator

## ? Operator for Error Propagation

    Tests the ? operator that propagates errors by early return.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | propagates Ok value | pass |
| 2 | propagates Err to caller | pass |
| 3 | chains multiple ? operators | pass |

**Example:** propagates Ok value
    Given val result = may_fail(x)?
    Given val res = caller(5)
    Then  expect res.unwrap() == 11  # 5 * 2 + 1

**Example:** propagates Err to caller
    Given val result = may_fail(x)?
    Given val res = caller(-5)
    Then  expect res.unwrap_or(-99) == -99

**Example:** chains multiple ? operators
    Given val a = step1(x)?
    Given val b = step2(a)?
    Given val res = pipeline(5)
    Then  expect res.unwrap() == 30  # (5 + 10) * 2

## Feature: Result Pattern Matching

## Pattern Matching with Result

    Tests pattern matching on Result types with Ok and Err variants.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | matches Ok variant | pass |
| 2 | matches Err variant | pass |
| 3 | uses if let with Ok | pass |
| 4 | uses if let with Err else | pass |

**Example:** matches Ok variant
    Given val res = Ok(100)
    Given var output = 0
    Then  expect output == 100

**Example:** matches Err variant
    Given val res = Err("failure")
    Given var output = 0
    Then  expect output == -1

**Example:** uses if let with Ok
    Given val res = Ok(100)
    Given var output = 0
    Then  expect output == 100

**Example:** uses if let with Err else
    Given val res: Result<i64, text> = Err("error")
    Given var output = 0
    Then  expect output == -1


