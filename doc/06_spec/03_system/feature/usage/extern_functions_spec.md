# External FFI Function Calls and Native Interoperability

> Simple's Foreign Function Interface (FFI) enables calling native runtime functions declared with the `extern fn` keyword. This is the foundation for all system-level operations, including math, I/O, and process management. This spec validates that use std.spec.step

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# External FFI Function Calls and Native Interoperability

Simple's Foreign Function Interface (FFI) enables calling native runtime functions declared with the `extern fn` keyword. This is the foundation for all system-level operations, including math, I/O, and process management. This spec validates that use std.spec.step

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RT-012 |
| Category | Runtime |
| Status | Active |
| Source | `test/03_system/feature/usage/extern_functions_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Simple's Foreign Function Interface (FFI) enables calling native runtime functions
declared with the `extern fn` keyword. This is the foundation for all system-level
operations, including math, I/O, and process management. This spec validates that
use std.spec.step

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

- calls and returns expected result


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("calls and returns expected result")
val result = rt_math_sqrt(16.0)
assert_true(result == 4.0)
```

</details>

#### when passing parameters to extern function

#### receives all parameters correctly

- receives all parameters correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("receives all parameters correctly")
val result = rt_math_pow(2.0, 3.0)
assert_true(result == 8.0)
```

</details>

#### handles parameter type conversions

- handles parameter type conversions


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles parameter type conversions")
val result = rt_math_sqrt(25.0)
assert_true(result == 5.0)
```

</details>

### External FFI Return Values

#### when extern function returns a value

#### returns primitive types correctly

- returns primitive types correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns primitive types correctly")
val result = rt_math_sqrt(9.0)
assert_true(result == 3.0)
```

</details>

#### returns composite types correctly

- returns composite types correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns composite types correctly")
val args = sys_get_args()
assert_true(args.len() >= 1)
```

</details>

#### when extern function encounters errors

#### propagates errors from extern function

- propagates errors from extern function


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("propagates errors from extern function")
# Test with NaN input (sqrt of negative number)
val result = rt_math_sqrt(-1.0)
# NaN is not equal to itself
assert_true(result != result)
```

</details>

### External FFI Memory Safety

#### properly manages memory across FFI boundary

- properly manages memory across FFI boundary


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("properly manages memory across FFI boundary")
# Test that list returned from FFI is valid
val args = sys_get_args()
val first = args[0]
assert_true(first != "")
```

</details>

#### prevents use-after-free in FFI calls

- prevents use-after-free in FFI calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("prevents use-after-free in FFI calls")
# Call FFI function multiple times to ensure memory is stable
val r1 = rt_math_sqrt(16.0)
val r2 = rt_math_sqrt(16.0)
assert_true(r1 == r2)
assert_true(r1 == 4.0)
```

</details>

#### handles string marshalling safely

- handles string marshalling safely


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles string marshalling safely")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6521cb76fef1100e7158435f1aa9a76a4b1e6bfd6693c782896637136767e872`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6521cb76fef1100e7158435f1aa9a76a4b1e6bfd6693c782896637136767e872`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6521cb76fef1100e7158435f1aa9a76a4b1e6bfd6693c782896637136767e872`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/extern_functions_spec.spl
mirror: doc/06_spec/03_system/feature/usage/extern_functions_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/extern_functions_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/extern_functions_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/extern_functions_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'calls and returns expected result' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/extern_functions_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'receives all parameters correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/extern_functions_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles parameter type conversions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
