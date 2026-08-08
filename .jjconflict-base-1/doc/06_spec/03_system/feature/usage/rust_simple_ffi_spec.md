# Rust-to-Simple FFI Specification

> The Simple language provides a comprehensive Foreign Function Interface (FFI) system that enables bidirectional communication between Rust and Simple code. This specification tests the core FFI functionality.

<!-- sdn-diagram:id=rust_simple_ffi_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rust_simple_ffi_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rust_simple_ffi_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rust_simple_ffi_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 32 | 32 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rust-to-Simple FFI Specification

The Simple language provides a comprehensive Foreign Function Interface (FFI) system that enables bidirectional communication between Rust and Simple code. This specification tests the core FFI functionality.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #FFI-001 - #FFI-050 |
| Category | Runtime |
| Difficulty | 4/5 |
| Status | Implemented |
| Source | `test/03_system/feature/usage/rust_simple_ffi_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

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

## Scenarios

### FFI Value Operations

#### integer values

#### creates and extracts positive integers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rv = rt_value_int(42)
val result = rt_value_as_int(rv)
expect(result).to_equal(42)
```

</details>

#### creates and extracts negative integers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rv = rt_value_int(-100)
val result = rt_value_as_int(rv)
expect(result).to_equal(-100)
```

</details>

#### creates and extracts zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rv = rt_value_int(0)
val result = rt_value_as_int(rv)
expect(result).to_equal(0)
```

</details>

#### float values

#### creates and extracts floats

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rv = rt_value_float(3.14)
val result = rt_value_as_float(rv)
# RuntimeValue 61-bit payload encoding may lose exact equality
expect(result).to_be_greater_than(3.13)
expect(result).to_be_less_than(3.15)
```

</details>

#### boolean values

#### creates and extracts true

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rv = rt_value_bool(true)
val result = rt_value_as_bool(rv)
expect(result).to_equal(true)
```

</details>

#### creates and extracts false

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rv = rt_value_bool(false)
val result = rt_value_as_bool(rv)
expect(result).to_equal(false)
```

</details>

#### nil values

#### creates nil value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rv = rt_value_nil()
expect(rt_value_is_nil(rv)).to_equal(true)
```

</details>

#### non-nil values return false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rv = rt_value_int(42)
expect(rt_value_is_nil(rv)).to_equal(false)
```

</details>

### FFI Array Operations

#### array creation

#### creates empty array with capacity

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = rt_array_new(10)
expect(rt_array_len(arr)).to_equal(0)
```

</details>

#### array manipulation

#### pushes and retrieves elements

1. rt array push
2. rt array push
   - Expected: rt_value_as_int(first) equals `42`
   - Expected: rt_value_as_int(second) equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = rt_array_new(10)
rt_array_push(arr, rt_value_int(42))
rt_array_push(arr, rt_value_int(100))

val first = rt_array_get(arr, 0)
val second = rt_array_get(arr, 1)

expect(rt_value_as_int(first)).to_equal(42)
expect(rt_value_as_int(second)).to_equal(100)
```

</details>

#### sets elements at index

1. rt array push
2. rt array set
   - Expected: rt_value_as_int(result) equals `999`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = rt_array_new(10)
rt_array_push(arr, rt_value_int(1))
rt_array_set(arr, 0, rt_value_int(999))

val result = rt_array_get(arr, 0)
expect(rt_value_as_int(result)).to_equal(999)
```

</details>

#### pops elements

1. rt array push
2. rt array push
   - Expected: rt_value_as_int(popped) equals `2`
   - Expected: rt_array_len(arr) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = rt_array_new(10)
rt_array_push(arr, rt_value_int(1))
rt_array_push(arr, rt_value_int(2))

val popped = rt_array_pop(arr)
expect(rt_value_as_int(popped)).to_equal(2)
expect(rt_array_len(arr)).to_equal(1)
```

</details>

#### clears array

1. rt array push
2. rt array push
3. rt array clear
   - Expected: rt_array_len(arr) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = rt_array_new(10)
rt_array_push(arr, rt_value_int(1))
rt_array_push(arr, rt_value_int(2))

rt_array_clear(arr)
expect(rt_array_len(arr)).to_equal(0)
```

</details>

### FFI Dictionary Operations

#### dictionary creation

#### creates empty dictionary

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dict = rt_dict_new()
expect(rt_dict_len(dict)).to_equal(0)
```

</details>

#### dictionary manipulation

#### sets and retrieves values

1. rt dict set
   - Expected: rt_string_eq(result, value) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dict = rt_dict_new()
val key = rt_string_new("name")
val value = rt_string_new("Alice")

rt_dict_set(dict, key, value)
val result = rt_dict_get(dict, key)

expect(rt_string_eq(result, value)).to_equal(true)
```

</details>

#### tracks length correctly

1. rt dict set
2. rt dict set
   - Expected: rt_dict_len(dict) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dict = rt_dict_new()
rt_dict_set(dict, rt_string_new("a"), rt_value_int(1))
rt_dict_set(dict, rt_string_new("b"), rt_value_int(2))

expect(rt_dict_len(dict)).to_equal(2)
```

</details>

### FFI String Operations

#### creates string from literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = rt_string_new("Hello")
expect(rt_string_len(s)).to_equal(5)
```

</details>

#### concatenates two strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = rt_string_new("Hello, ")
val b = rt_string_new("World!")
val result = rt_string_concat(a, b)

expect(rt_string_len(result)).to_equal(13)
```

</details>

### FFI Math Operations

#### trigonometric functions

#### computes sin(0) equals 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = rt_math_sin(0.0)
expect(result).to_be_greater_than(-0.0001)
expect(result).to_be_less_than(0.0001)
```

</details>

#### computes cos(0) equals 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = rt_math_cos(0.0)
expect(result).to_be_greater_than(0.9999)
expect(result).to_be_less_than(1.0001)
```

</details>

#### power and logarithm

#### computes power

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = rt_math_pow(2.0, 3.0)
expect(result).to_be_greater_than(7.9999)
expect(result).to_be_less_than(8.0001)
```

</details>

#### computes square root

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = rt_math_sqrt(16.0)
expect(result).to_be_greater_than(3.9999)
expect(result).to_be_less_than(4.0001)
```

</details>

### FFI Environment Operations

#### gets home directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val home = rt_env_home()
expect(rt_value_is_nil(home)).to_equal(false)
```

</details>

#### gets temp directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val temp = rt_env_temp()
expect(rt_value_is_nil(temp)).to_equal(false)
```

</details>

#### sets and checks environment variable existence

1. rt env set
   - Expected: rt_env_exists(name) is true
2. rt env remove
   - Expected: rt_env_exists(name) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "SIMPLE_FFI_TEST_VAR"
val value = "test_value_12345"

rt_env_set(name, value)
expect(rt_env_exists(name)).to_equal(true)

# Cleanup
rt_env_remove(name)
expect(rt_env_exists(name)).to_equal(false)
```

</details>

### FFI Runtime Configuration

#### toggles debug mode

1. rt set debug mode
   - Expected: rt_is_debug_mode_enabled() is true
2. rt set debug mode
   - Expected: rt_is_debug_mode_enabled() is false
3. rt set debug mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = rt_is_debug_mode_enabled()

rt_set_debug_mode(true)
expect(rt_is_debug_mode_enabled()).to_equal(true)

rt_set_debug_mode(false)
expect(rt_is_debug_mode_enabled()).to_equal(false)

# Restore original
rt_set_debug_mode(original)
```

</details>

#### toggles macro trace

1. rt set macro trace
   - Expected: rt_is_macro_trace_enabled() is true
2. rt set macro trace
   - Expected: rt_is_macro_trace_enabled() is false
3. rt set macro trace


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = rt_is_macro_trace_enabled()

rt_set_macro_trace(true)
expect(rt_is_macro_trace_enabled()).to_equal(true)

rt_set_macro_trace(false)
expect(rt_is_macro_trace_enabled()).to_equal(false)

# Restore original
rt_set_macro_trace(original)
```

</details>

### FFI Type Tags

#### identifies integer type

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rv = rt_value_int(42)
val tag = rt_value_type_tag(rv)
expect(tag).to_equal(TAG_INT)
```

</details>

#### identifies float type

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rv = rt_value_float(3.14)
val tag = rt_value_type_tag(rv)
expect(tag).to_equal(TAG_FLOAT)
```

</details>

#### identifies nil/special type

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rv = rt_value_nil()
val tag = rt_value_type_tag(rv)
expect(tag).to_equal(TAG_SPECIAL)
```

</details>

### FFI Error Handling

#### reports function not found

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val error = rt_function_not_found("nonexistent_function")
expect(rt_is_error(error)).to_equal(true)
```

</details>

#### reports method not found

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val error = rt_method_not_found("SomeType", "missing_method")
expect(rt_is_error(error)).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 32 |
| Active scenarios | 32 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
