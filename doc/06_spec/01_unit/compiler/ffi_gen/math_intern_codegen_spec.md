# Math intern codegen specification

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

#

## Scenarios

### math intern codegen

#### generates inline abs wrapper

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- generates inline abs wrapper
   - Expected: code contains `n.abs()`
   - Expected: code does not contain `ffi_abs`
   - Expected: code contains `as_int()`
   - Expected: code contains `Value::Int`
   - Expected: code contains `Absolute value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates inline abs wrapper")
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

- generates inline min wrapper with two params
   - Expected: code contains `a.min(b)`
   - Expected: code does not contain `ffi_min`
   - Expected: code contains `.get(0)`
   - Expected: code contains `.get(1)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates inline min wrapper with two params")
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

- generates inline pow wrapper with cast
   - Expected: code contains `base.pow(exp as u32)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates inline pow wrapper with cast")
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

- generates inline identity for floor
   - Expected: code contains `Ok(Value::Int(n))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates inline identity for floor")
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

- generates FFI-delegated rt_math_sin wrapper
   - Expected: code contains `ffi_rt_math_sin(x)`
   - Expected: code contains `Value::Float`
   - Expected: code contains `as_float()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates FFI-delegated rt_math_sin wrapper")
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

- generates FFI-delegated rt_math_atan2 wrapper
   - Expected: code contains `ffi_rt_math_atan2(y, x)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates FFI-delegated rt_math_atan2 wrapper")
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

- generates FFI-delegated rt_math_nan zero-arg wrapper
   - Expected: code contains `ffi_rt_math_nan()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates FFI-delegated rt_math_nan zero-arg wrapper")
val spec = make_ffi_spec(
    "rt_math_nan", [], "f64", "Returns IEEE 754 NaN", "rt_math_nan"
)
val code = generate_fn_wrapper(spec)
expect(code.contains("ffi_rt_math_nan()")).to_equal(true)
```

</details>

#### generates FFI-delegated bool return for rt_math_is_nan

- generates FFI-delegated bool return for rt_math_is_nan
   - Expected: code contains `Value::Bool`
   - Expected: code contains `ffi_rt_math_is_nan(x)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates FFI-delegated bool return for rt_math_is_nan")
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

- generates module with mixed inline and FFI functions
   - Expected: module_code contains `Auto-generated interpreter extern wrappers for math`
   - Expected: module_code contains `rt_math_sin as ffi_rt_math_sin`
   - Expected: module_code does not contain `abs as ffi_abs`
   - Expected: module_code contains `pub fn abs(`
   - Expected: module_code contains `pub fn rt_math_sin_fn(`
   - Expected: module_code contains `n.abs()`
   - Expected: module_code contains `ffi_rt_math_sin(x)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates module with mixed inline and FFI functions")
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

- skips FFI import block when all specs are inline
   - Expected: module_code does not contain `use simple_runtime`
   - Expected: module_code contains `use crate::error`
   - Expected: module_code contains `use crate::value::Value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips FFI import block when all specs are inline")
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

- generates correct dispatch entries
   - Expected: dispatch contains `"abs" => math::abs(&evaluated)`
   - Expected: dispatch contains `"rt_math_sin" => math::rt_math_sin_fn(&evaluated)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates correct dispatch entries")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `37175fe359b5ae2125b14af9f30dade23e78a078429d851937e8fb3810b9f47c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `37175fe359b5ae2125b14af9f30dade23e78a078429d851937e8fb3810b9f47c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `37175fe359b5ae2125b14af9f30dade23e78a078429d851937e8fb3810b9f47c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/ffi_gen/math_intern_codegen_spec.spl
mirror: doc/06_spec/01_unit/compiler/ffi_gen/math_intern_codegen_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/ffi_gen/math_intern_codegen_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/ffi_gen/math_intern_codegen_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/ffi_gen/math_intern_codegen_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generates inline abs wrapper' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/ffi_gen/math_intern_codegen_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generates inline min wrapper with two params' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/ffi_gen/math_intern_codegen_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generates inline pow wrapper with cast' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
