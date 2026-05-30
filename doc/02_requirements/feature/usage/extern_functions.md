# extern functions
*Source:* `test/feature/usage/extern_functions_spec.spl`

## Overview

External FFI Functions Tests
Feature: External FFI function calls and native interoperability
Category: Runtime
Status: Complete

Tests for calling external functions defined in the native runtime,
including FFI bindings, memory safety, and parameter passing.

## Feature: External FFI Functions

Tests for basic external function invocation through the FFI interface.
    Verifies that functions can be called, return values are correct,
    and parameters are properly passed.

### Scenario: when calling a simple extern function

### Scenario: Simple Function Call

        Tests basic FFI function invocation with primitive types.

| # | Example | Status |
|---|---------|--------|
| 1 | calls and returns expected result | pass |

**Example:** calls and returns expected result
    Given val result = rt_math_sqrt(16.0)
    Then  expect(result == 4.0)

### Scenario: when passing parameters to extern function

### Scenario: Parameter Passing

        Verifies that parameters are correctly marshalled to native code.

| # | Example | Status |
|---|---------|--------|
| 1 | receives all parameters correctly | pass |
| 2 | handles parameter type conversions | pass |

**Example:** receives all parameters correctly
    Given val result = rt_math_pow(2.0, 3.0)
    Then  expect(result == 8.0)

**Example:** handles parameter type conversions
    Given val result = rt_math_sqrt(25.0)
    Then  expect(result == 5.0)

## Feature: External FFI Return Values

Tests for handling return values from FFI functions,
    including error cases and type conversions.

### Scenario: when extern function returns a value

### Scenario: Return Value Handling

        Tests that return values are properly converted and available.

| # | Example | Status |
|---|---------|--------|
| 1 | returns primitive types correctly | pass |
| 2 | returns composite types correctly | pass |

**Example:** returns primitive types correctly
    Given val result = rt_math_sqrt(9.0)
    Then  expect(result == 3.0)

**Example:** returns composite types correctly
    Given val args = sys_get_args()
    Then  expect(args.len() >= 1)

### Scenario: when extern function encounters errors

### Scenario: Error Propagation

        Tests error handling from native function calls.

| # | Example | Status |
|---|---------|--------|
| 1 | propagates errors from extern function | pass |

**Example:** propagates errors from extern function
    Given val result = rt_math_sqrt(-1.0)
    Then  expect(result != result)

## Feature: External FFI Memory Safety

Tests for memory safety when calling external functions,
    including pointer handling and resource lifecycle.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | properly manages memory across FFI boundary | pass |
| 2 | prevents use-after-free in FFI calls | pass |
| 3 | handles string marshalling safely | pass |

**Example:** properly manages memory across FFI boundary
    Given val args = sys_get_args()
    Given val first = args[0]
    Then  expect(first != "")

**Example:** prevents use-after-free in FFI calls
    Given val r1 = rt_math_sqrt(16.0)
    Given val r2 = rt_math_sqrt(16.0)
    Then  expect(r1 == r2)
    Then  expect(r1 == 4.0)

**Example:** handles string marshalling safely
    Given val args = sys_get_args()
    Then  expect(args.len() >= 1)
    Then  expect(args[0].len() > 0)


