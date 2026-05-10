# External FFI Function Calls and Native Interoperability

**Feature ID:** #RT-012 | **Category:** Runtime | **Status:** Active

_Source: `test/feature/usage/extern_functions_spec.spl`_

---

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

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 9 |

## Test Structure

### External FFI Functions

#### when calling a simple extern function

- ✅ calls and returns expected result
#### when passing parameters to extern function

- ✅ receives all parameters correctly
- ✅ handles parameter type conversions
### External FFI Return Values

#### when extern function returns a value

- ✅ returns primitive types correctly
- ✅ returns composite types correctly
#### when extern function encounters errors

- ✅ propagates errors from extern function
### External FFI Memory Safety

- ✅ properly manages memory across FFI boundary
- ✅ prevents use-after-free in FFI calls
- ✅ handles string marshalling safely

