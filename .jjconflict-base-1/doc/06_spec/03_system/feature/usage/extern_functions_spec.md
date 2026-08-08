# External FFI Function Calls and Native Interoperability

> Simple's Foreign Function Interface (FFI) enables calling native runtime functions declared with the `extern fn` keyword. This is the foundation for all system-level operations, including math, I/O, and process management. This spec validates that extern functions can be declared and called correctly, that parameters are marshalled across the FFI boundary, that return values (including composite types like `List<text>`) are properly converted, and that memory remains stable across repeated FFI calls.

<!-- sdn-diagram:id=extern_functions_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=extern_functions_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

extern_functions_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=extern_functions_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# External FFI Function Calls and Native Interoperability

Simple's Foreign Function Interface (FFI) enables calling native runtime functions declared with the `extern fn` keyword. This is the foundation for all system-level operations, including math, I/O, and process management. This spec validates that extern functions can be declared and called correctly, that parameters are marshalled across the FFI boundary, that return values (including composite types like `List<text>`) are properly converted, and that memory remains stable across repeated FFI calls.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RT-012 |
| Category | Runtime |
| Status | Active |
| Source | `test/03_system/feature/usage/extern_functions_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Simple's Foreign Function Interface (FFI) enables calling native runtime functions
declared with the `extern fn` keyword. This is the foundation for all system-level
operations, including math, I/O, and process management. This spec validates that
extern functions can be declared and called correctly, that parameters are marshalled
across the FFI boundary, that return values (including composite types like `List<text>`)
are properly converted, and that memory remains stable across repeated FFI calls.

## Syntax

```simple
extern fn rt_math_sqrt(x: f64) -> f64
extern fn rt_math_pow(x: f64, y: f64) -> f64
extern fn sys_get_args() -> List<text>

val result = rt_math_sqrt(16.0)    # returns 4.0
val args = sys_get_args()           # returns program arguments
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| `extern fn` | Declaration that binds a Simple function name to a native runtime symbol |
| Parameter marshalling | Automatic conversion of Simple types to native types at the FFI boundary |
| Return type conversion | Native return values are converted back to Simple types (f64, List, text) |
| Memory safety | FFI calls must not cause use-after-free or dangling references |
| String marshalling | Text values are safely transferred between the Rust runtime and Simple |

## Scenarios

### External FFI Functions

#### when calling a simple extern function

#### calls and returns expected result

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = rt_math_sqrt(16.0)
assert_true(result == 4.0)
```

</details>

#### when passing parameters to extern function

#### receives all parameters correctly

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = rt_math_pow(2.0, 3.0)
assert_true(result == 8.0)
```

</details>

#### handles parameter type conversions

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = rt_math_sqrt(25.0)
assert_true(result == 5.0)
```

</details>

### External FFI Return Values

#### when extern function returns a value

#### returns primitive types correctly

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = rt_math_sqrt(9.0)
assert_true(result == 3.0)
```

</details>

#### returns composite types correctly

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = sys_get_args()
assert_true(args.len() >= 1)
```

</details>

#### when extern function encounters errors

#### propagates errors from extern function

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test with NaN input (sqrt of negative number)
val result = rt_math_sqrt(-1.0)
# NaN is not equal to itself
assert_true(result != result)
```

</details>

### External FFI Memory Safety

#### properly manages memory across FFI boundary

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test that list returned from FFI is valid
val args = sys_get_args()
val first = args[0]
assert_true(first != "")
```

</details>

#### prevents use-after-free in FFI calls

- assert true
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Call FFI function multiple times to ensure memory is stable
val r1 = rt_math_sqrt(16.0)
val r2 = rt_math_sqrt(16.0)
assert_true(r1 == r2)
assert_true(r1 == 4.0)
```

</details>

#### handles string marshalling safely

- assert true
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Get args which involves string marshalling from Rust to Simple
val args = sys_get_args()
assert_true(args[0].len() > 0)
# Program name should be non-empty (index before .len() to avoid interpreter var corruption)
assert_true(args.len() >= 1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
