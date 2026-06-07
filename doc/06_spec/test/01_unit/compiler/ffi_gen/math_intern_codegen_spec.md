# Math intern codegen specification

> 1. [InternParamSpec

<!-- sdn-diagram:id=math_intern_codegen_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=math_intern_codegen_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

math_intern_codegen_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=math_intern_codegen_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Math intern codegen specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/ffi_gen/math_intern_codegen_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

#

## Scenarios

### math intern codegen

#### generates inline abs wrapper

1. [InternParamSpec
2. "i64", "Absolute value of an integer", "n abs
   - Expected: code contains `n.abs()`
   - Expected: code does not contain `ffi_abs`
   - Expected: code contains `as_int()`
   - Expected: code contains `Value::Int`
   - Expected: code contains `Absolute value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spec = make_inline_spec(
    "abs",
    [InternParamSpec(name: "n", value_type: "i64")],
    "i64", "Absolute value of an integer", "n.abs()"
)
val code = generate_fn_wrapper(spec)
# Should contain the inline expression, NOT ffi_abs()
expect(code.contains("n.abs()")).to_equal(true)
expect(code.contains("ffi_abs")).to_equal(false)
# Should extract the parameter as i64
expect(code.contains("as_int()")).to_equal(true)
# Should wrap result in Value::Int
expect(code.contains("Value::Int")).to_equal(true)
# Should have the doc comment
expect(code.contains("Absolute value")).to_equal(true)
```

</details>

#### generates inline min wrapper with two params

1. [InternParamSpec
2. "i64", "Minimum of two integers", "a min
   - Expected: code contains `a.min(b)`
   - Expected: code does not contain `ffi_min`
   - Expected: code contains `.get(0)`
   - Expected: code contains `.get(1)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spec = make_inline_spec(
    "min",
    [InternParamSpec(name: "a", value_type: "i64"), InternParamSpec(name: "b", value_type: "i64")],
    "i64", "Minimum of two integers", "a.min(b)"
)
val code = generate_fn_wrapper(spec)
expect(code.contains("a.min(b)")).to_equal(true)
expect(code.contains("ffi_min")).to_equal(false)
# Two params: should use .get(0) and .get(1)
expect(code.contains(".get(0)")).to_equal(true)
expect(code.contains(".get(1)")).to_equal(true)
```

</details>

#### generates inline pow wrapper with cast

1. [InternParamSpec
2. "i64", "Power function", "base pow
   - Expected: code contains `base.pow(exp as u32)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spec = make_inline_spec(
    "pow",
    [InternParamSpec(name: "base", value_type: "i64"), InternParamSpec(name: "exp", value_type: "i64")],
    "i64", "Power function", "base.pow(exp as u32)"
)
val code = generate_fn_wrapper(spec)
expect(code.contains("base.pow(exp as u32)")).to_equal(true)
```

</details>

#### generates inline identity for floor

1. [InternParamSpec
2. "i64", "Floor
   - Expected: code contains `Ok(Value::Int(n))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spec = make_inline_spec(
    "floor",
    [InternParamSpec(name: "n", value_type: "i64")],
    "i64", "Floor (identity for integers)", "n"
)
val code = generate_fn_wrapper(spec)
expect(code.contains("Ok(Value::Int(n))")).to_equal(true)
```

</details>

#### generates FFI-delegated rt_math_sin wrapper

1. [InternParamSpec
2. "f64", "Sine
   - Expected: code contains `ffi_rt_math_sin(x)`
   - Expected: code contains `Value::Float`
   - Expected: code contains `as_float()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spec = make_ffi_spec(
    "rt_math_sin",
    [InternParamSpec(name: "x", value_type: "f64")],
    "f64", "Sine (radians)", "rt_math_sin"
)
val code = generate_fn_wrapper(spec)
expect(code.contains("ffi_rt_math_sin(x)")).to_equal(true)
expect(code.contains("Value::Float")).to_equal(true)
expect(code.contains("as_float()")).to_equal(true)
```

</details>

#### generates FFI-delegated rt_math_atan2 wrapper

1. [InternParamSpec
   - Expected: code contains `ffi_rt_math_atan2(y, x)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spec = make_ffi_spec(
    "rt_math_atan2",
    [InternParamSpec(name: "y", value_type: "f64"), InternParamSpec(name: "x", value_type: "f64")],
    "f64", "Two-argument arc tangent", "rt_math_atan2"
)
val code = generate_fn_wrapper(spec)
expect(code.contains("ffi_rt_math_atan2(y, x)")).to_equal(true)
```

</details>

#### generates FFI-delegated rt_math_nan zero-arg wrapper

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spec = make_ffi_spec(
    "rt_math_nan", [], "f64", "Returns IEEE 754 NaN", "rt_math_nan"
)
val code = generate_fn_wrapper(spec)
expect(code.contains("ffi_rt_math_nan()")).to_equal(true)
```

</details>

#### generates FFI-delegated bool return for rt_math_is_nan

1. [InternParamSpec
   - Expected: code contains `Value::Bool`
   - Expected: code contains `ffi_rt_math_is_nan(x)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spec = make_ffi_spec(
    "rt_math_is_nan",
    [InternParamSpec(name: "x", value_type: "f64")],
    "bool", "Check if value is NaN", "rt_math_is_nan"
)
val code = generate_fn_wrapper(spec)
expect(code.contains("Value::Bool")).to_equal(true)
expect(code.contains("ffi_rt_math_is_nan(x)")).to_equal(true)
```

</details>

#### generates module with mixed inline and FFI functions

1. [InternParamSpec
2. "i64", "Absolute value", "n abs
3. [InternParamSpec
   - Expected: module_code contains `Auto-generated interpreter extern wrappers for math`
   - Expected: module_code contains `rt_math_sin as ffi_rt_math_sin`
   - Expected: module_code does not contain `abs as ffi_abs`
   - Expected: module_code contains `pub fn abs(`
   - Expected: module_code contains `pub fn rt_math_sin_fn(`
   - Expected: module_code contains `n.abs()`
   - Expected: module_code contains `ffi_rt_math_sin(x)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var specs: [InternFnSpec] = []
specs.push(make_inline_spec(
    "abs",
    [InternParamSpec(name: "n", value_type: "i64")],
    "i64", "Absolute value", "n.abs()"
))
specs.push(make_ffi_spec(
    "rt_math_sin",
    [InternParamSpec(name: "x", value_type: "f64")],
    "f64", "Sine", "rt_math_sin"
))

val module_code = generate_module("math", specs)
# Module header
expect(module_code.contains("Auto-generated interpreter extern wrappers for math")).to_equal(true)
# Imports: should have rt_math_sin but NOT abs
expect(module_code.contains("rt_math_sin as ffi_rt_math_sin")).to_equal(true)
expect(module_code.contains("abs as ffi_abs")).to_equal(false)
# Both functions should be present
expect(module_code.contains("pub fn abs(")).to_equal(true)
expect(module_code.contains("pub fn rt_math_sin_fn(")).to_equal(true)
# Inline expr in abs
expect(module_code.contains("n.abs()")).to_equal(true)
# FFI call in rt_math_sin
expect(module_code.contains("ffi_rt_math_sin(x)")).to_equal(true)
```

</details>

#### skips FFI import block when all specs are inline

1. [InternParamSpec
2. "i64", "Absolute value", "n abs
3. [InternParamSpec
4. "i64", "Minimum", "a min
   - Expected: module_code does not contain `use simple_runtime`
   - Expected: module_code contains `use crate::error`
   - Expected: module_code contains `use crate::value::Value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var specs: [InternFnSpec] = []
specs.push(make_inline_spec(
    "abs",
    [InternParamSpec(name: "n", value_type: "i64")],
    "i64", "Absolute value", "n.abs()"
))
specs.push(make_inline_spec(
    "min",
    [InternParamSpec(name: "a", value_type: "i64"), InternParamSpec(name: "b", value_type: "i64")],
    "i64", "Minimum", "a.min(b)"
))

val module_code = generate_module("math", specs)
# Should NOT have the runtime import block
expect(module_code.contains("use simple_runtime")).to_equal(false)
# But should still have error imports
expect(module_code.contains("use crate::error")).to_equal(true)
expect(module_code.contains("use crate::value::Value")).to_equal(true)
```

</details>

#### generates correct dispatch entries

1. [InternParamSpec
2. "i64", "Absolute value", "n abs
3. [InternParamSpec
   - Expected: dispatch contains `"abs" => math::abs(&evaluated)`
   - Expected: dispatch contains `"rt_math_sin" => math::rt_math_sin_fn(&evaluated)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var specs: [InternFnSpec] = []
specs.push(make_inline_spec(
    "abs",
    [InternParamSpec(name: "n", value_type: "i64")],
    "i64", "Absolute value", "n.abs()"
))
specs.push(make_ffi_spec(
    "rt_math_sin",
    [InternParamSpec(name: "x", value_type: "f64")],
    "f64", "Sine", "rt_math_sin"
))

val dispatch = generate_dispatch_entries(specs)
expect(dispatch.contains("\"abs\" => math::abs(&evaluated)")).to_equal(true)
expect(dispatch.contains("\"rt_math_sin\" => math::rt_math_sin_fn(&evaluated)")).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
