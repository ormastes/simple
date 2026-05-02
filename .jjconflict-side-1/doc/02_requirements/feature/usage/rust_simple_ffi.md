# Rust-to-Simple FFI Specification
*Source:* `test/feature/usage/rust_simple_ffi_spec.spl`
**Feature IDs:** #FFI-001 - #FFI-050  |  **Category:** Runtime  |  **Status:** Implemented

## Overview



use std.text.{NL}

## Overview

The Simple language provides a comprehensive Foreign Function Interface (FFI)
system that enables bidirectional communication between Rust and Simple code.
This specification tests the core FFI functionality.

## Key Concepts

| Concept | Description |
|---------|-------------|
| RuntimeValue | 64-bit tagged value (3-bit tag + 61-bit payload) |
| BridgeValue | C-compatible wrapper for complex types |
| Extern Function | Function implemented in Rust, callable from Simple |
| Symbol Registry | Maps function names to Rust function pointers |

## Behavior

- FFI functions use C calling convention (extern C)
- RuntimeValue passed by value (64 bits, no allocation)
- Complex types allocated on heap, pointer stored in RuntimeValue
- Type marshalling handled automatically for primitive types

## Implementation Notes

FFI functions are organized in phases under src/rust/runtime/src/value/ffi/:
- Phase 1: Core value operations
- Phase 2: Hash and concurrent structures
- Phase 3: Interpreter bridge, contracts
- Phase 4-13: Math, file I/O, networking, GPU, etc.

Total: 562+ FFI functions across 50+ modules.

## Feature: FFI Value Operations

## Core Value Operations

    RuntimeValue is the fundamental type for FFI communication.
    These functions create and extract values from RuntimeValue.

### Scenario: integer values

| # | Example | Status |
|---|---------|--------|
| 1 | creates and extracts positive integers | pass |
| 2 | creates and extracts negative integers | pass |
| 3 | creates and extracts zero | pass |

**Example:** creates and extracts positive integers
    Given val rv = rt_value_int(42)
    Given val result = rt_value_as_int(rv)
    Then  expect(result).to_equal(42)

**Example:** creates and extracts negative integers
    Given val rv = rt_value_int(-100)
    Given val result = rt_value_as_int(rv)
    Then  expect(result).to_equal(-100)

**Example:** creates and extracts zero
    Given val rv = rt_value_int(0)
    Given val result = rt_value_as_int(rv)
    Then  expect(result).to_equal(0)

### Scenario: float values

| # | Example | Status |
|---|---------|--------|
| 1 | creates and extracts floats | pass |

**Example:** creates and extracts floats
    Given val rv = rt_value_float(3.14)
    Given val result = rt_value_as_float(rv)
    Then  expect(result).to_equal(3.14)

### Scenario: boolean values

| # | Example | Status |
|---|---------|--------|
| 1 | creates and extracts true | pass |
| 2 | creates and extracts false | pass |

**Example:** creates and extracts true
    Given val rv = rt_value_bool(true)
    Given val result = rt_value_as_bool(rv)
    Then  expect(result).to_equal(true)

**Example:** creates and extracts false
    Given val rv = rt_value_bool(false)
    Given val result = rt_value_as_bool(rv)
    Then  expect(result).to_equal(false)

### Scenario: nil values

| # | Example | Status |
|---|---------|--------|
| 1 | creates nil value | pass |
| 2 | non-nil values return false | pass |

**Example:** creates nil value
    Given val rv = rt_value_nil()
    Then  expect(rt_value_is_nil(rv)).to_equal(true)

**Example:** non-nil values return false
    Given val rv = rt_value_int(42)
    Then  expect(rt_value_is_nil(rv)).to_equal(false)

## Feature: FFI Array Operations

## Array Operations

    Arrays are heap-allocated collections accessible through FFI.

### Scenario: array creation

| # | Example | Status |
|---|---------|--------|
| 1 | creates empty array with capacity | pass |

**Example:** creates empty array with capacity
    Given val arr = rt_array_new(10)
    Then  expect(rt_array_len(arr)).to_equal(0)

### Scenario: array manipulation

| # | Example | Status |
|---|---------|--------|
| 1 | pushes and retrieves elements | pass |
| 2 | sets elements at index | pass |
| 3 | pops elements | pass |
| 4 | clears array | pass |

**Example:** pushes and retrieves elements
    Given val arr = rt_array_new(10)
    Given val first = rt_array_get(arr, 0)
    Given val second = rt_array_get(arr, 1)
    Then  expect(rt_value_as_int(first)).to_equal(42)
    Then  expect(rt_value_as_int(second)).to_equal(100)

**Example:** sets elements at index
    Given val arr = rt_array_new(10)
    Given val result = rt_array_get(arr, 0)
    Then  expect(rt_value_as_int(result)).to_equal(999)

**Example:** pops elements
    Given val arr = rt_array_new(10)
    Given val popped = rt_array_pop(arr)
    Then  expect(rt_value_as_int(popped)).to_equal(2)
    Then  expect(rt_array_len(arr)).to_equal(1)

**Example:** clears array
    Given val arr = rt_array_new(10)
    Then  expect(rt_array_len(arr)).to_equal(0)

## Feature: FFI Dictionary Operations

## Dictionary Operations

    Dictionaries (hash maps) are heap-allocated key-value stores.

### Scenario: dictionary creation

| # | Example | Status |
|---|---------|--------|
| 1 | creates empty dictionary | pass |

**Example:** creates empty dictionary
    Given val dict = rt_dict_new()
    Then  expect(rt_dict_len(dict)).to_equal(0)

### Scenario: dictionary manipulation

| # | Example | Status |
|---|---------|--------|
| 1 | sets and retrieves values | pass |
| 2 | tracks length correctly | pass |

**Example:** sets and retrieves values
    Given val dict = rt_dict_new()
    Given val key = rt_string_new("name")
    Given val value = rt_string_new("Alice")
    Given val result = rt_dict_get(dict, key)
    Then  expect(rt_string_eq(result, value)).to_equal(true)

**Example:** tracks length correctly
    Given val dict = rt_dict_new()
    Then  expect(rt_dict_len(dict)).to_equal(2)

## Feature: FFI String Operations

## String Operations

    Strings are heap-allocated UTF-8 sequences.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | creates string from literal | pass |
| 2 | concatenates two strings | pass |

**Example:** creates string from literal
    Given val s = rt_string_new("Hello")
    Then  expect(rt_string_len(s)).to_equal(5)

**Example:** concatenates two strings
    Given val a = rt_string_new("Hello, ")
    Given val b = rt_string_new("World!")
    Given val result = rt_string_concat(a, b)
    Then  expect(rt_string_len(result)).to_equal(13)

## Feature: FFI Math Operations

## Math Operations

    Trigonometric, logarithmic, and power functions implemented in Rust.

### Scenario: trigonometric functions

| # | Example | Status |
|---|---------|--------|
| 1 | computes sin(0) equals 0 | pass |
| 2 | computes cos(0) equals 1 | pass |

**Example:** computes sin(0) equals 0
    Given val result = rt_math_sin(0.0)
    Then  expect(result).to_be_greater_than(-0.0001)
    Then  expect(result).to_be_less_than(0.0001)

**Example:** computes cos(0) equals 1
    Given val result = rt_math_cos(0.0)
    Then  expect(result).to_be_greater_than(0.9999)
    Then  expect(result).to_be_less_than(1.0001)

### Scenario: power and logarithm

| # | Example | Status |
|---|---------|--------|
| 1 | computes power | pass |
| 2 | computes square root | pass |

**Example:** computes power
    Given val result = rt_math_pow(2.0, 3.0)
    Then  expect(result).to_be_greater_than(7.9999)
    Then  expect(result).to_be_less_than(8.0001)

**Example:** computes square root
    Given val result = rt_math_sqrt(16.0)
    Then  expect(result).to_be_greater_than(3.9999)
    Then  expect(result).to_be_less_than(4.0001)

## Feature: FFI Environment Operations

## Environment Variable Operations

    Access to system environment variables through FFI.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | gets home directory | pass |
| 2 | gets temp directory | pass |
| 3 | sets and checks environment variable existence | pass |

**Example:** gets home directory
    Given val home = rt_env_home()
    Then  expect(rt_value_is_nil(home)).to_equal(false)

**Example:** gets temp directory
    Given val temp = rt_env_temp()
    Then  expect(rt_value_is_nil(temp)).to_equal(false)

**Example:** sets and checks environment variable existence
    Given val name = "SIMPLE_FFI_TEST_VAR"
    Given val value = "test_value_12345"
    Then  expect(rt_env_exists(name)).to_equal(true)
    Then  expect(rt_env_exists(name)).to_equal(false)

## Feature: FFI Runtime Configuration

## Runtime Configuration

    Global runtime settings accessible through FFI.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | toggles debug mode | pass |
| 2 | toggles macro trace | pass |

**Example:** toggles debug mode
    Given val original = rt_is_debug_mode_enabled()
    Then  expect(rt_is_debug_mode_enabled()).to_equal(true)
    Then  expect(rt_is_debug_mode_enabled()).to_equal(false)

**Example:** toggles macro trace
    Given val original = rt_is_macro_trace_enabled()
    Then  expect(rt_is_macro_trace_enabled()).to_equal(true)
    Then  expect(rt_is_macro_trace_enabled()).to_equal(false)

## Feature: FFI Type Tags

## Type Tag Operations

    RuntimeValue includes a 3-bit type tag for runtime type checking.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | identifies integer type | pass |
| 2 | identifies float type | pass |
| 3 | identifies nil/special type | pass |

**Example:** identifies integer type
    Given val rv = rt_value_int(42)
    Given val tag = rt_value_type_tag(rv)
    Then  expect(tag).to_equal(TAG_INT)

**Example:** identifies float type
    Given val rv = rt_value_float(3.14)
    Given val tag = rt_value_type_tag(rv)
    Then  expect(tag).to_equal(TAG_FLOAT)

**Example:** identifies nil/special type
    Given val rv = rt_value_nil()
    Given val tag = rt_value_type_tag(rv)
    Then  expect(tag).to_equal(TAG_SPECIAL)

## Feature: FFI Error Handling

## Error Handling

    FFI functions report errors through RuntimeValue or panic bridge.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | reports function not found | pass |
| 2 | reports method not found | pass |

**Example:** reports function not found
    Given val error = rt_function_not_found("nonexistent_function")
    Then  expect(rt_is_error(error)).to_equal(true)

**Example:** reports method not found
    Given val error = rt_method_not_found("SomeType", "missing_method")
    Then  expect(rt_is_error(error)).to_equal(true)


