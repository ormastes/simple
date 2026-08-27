# Result Type Specification

> Tests for the Result type representing success or error outcomes, including constructors, pattern matching, and safe unwrapping mechanisms.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Result Type Specification

Tests for the Result type representing success or error outcomes, including constructors, pattern matching, and safe unwrapping mechanisms.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RESULT-001 |
| Category | Language \| Types |
| Status | Implemented |
| Source | `test/03_system/feature/usage/result_type_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for the Result type representing success or error outcomes,
including constructors, pattern matching, and safe unwrapping mechanisms.

## Syntax

```simple
use std.spec.step

val success: Result<i32, text> = Ok(42)
val failure: Result<i32, text> = Err("error")

match result:
Ok(value) => print "Success: {value}"
Err(msg) => print "Error: {msg}"

val unwrapped = result.unwrap()              # Raises if Err
val safe = result.unwrap_or(0)               # Default if Err
val propagated = fallible_operation()?       # Early return on Err
```

## Scenarios

### Result Type Basic Usage

#### Ok values

#### creates Ok with value

- creates Ok with value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates Ok with value")
val res = Ok(42)
expect res.unwrap() == 42
```

</details>

#### checks Ok is ok

- checks Ok is ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("checks Ok is ok")
val res = Ok(10)
expect res.ok.?
```

</details>

#### checks Ok is not err

- checks Ok is not err


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("checks Ok is not err")
val res = Ok(5)
expect not res.err.?
```

</details>

#### Err values

#### creates Err with error

- creates Err with error


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates Err with error")
val res = Err("error message")
expect res.err.?
```

</details>

#### checks Err is not ok

- checks Err is not ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("checks Err is not ok")
val res = Err("oops")
expect not res.ok.?
```

</details>

#### uses unwrap_or for Err

- uses unwrap_or for Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses unwrap_or for Err")
val res = Err("error")
expect res.unwrap_or(99) == 99
```

</details>

### Result from Functions

#### returns Ok from function

- returns Ok from function


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns Ok from function")
fn safe_divide(a, b):
    if b == 0:
        return Err("division by zero")
    return Ok(a / b)

val r = safe_divide(20, 4)
expect r.unwrap() == 5
```

</details>

#### returns Err from function

- returns Err from function


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns Err from function")
fn safe_divide(a, b):
    if b == 0:
        return Err("division by zero")
    return Ok(a / b)

val r = safe_divide(10, 0)
expect r.unwrap_or(-1) == -1
```

</details>

#### chains Result operations

- chains Result operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("chains Result operations")
fn step1(x):
    if x < 0:
        return Err("negative")
    return Ok(x + 10)

fn step2(x):
    if x > 100:
        return Err("too large")
    return Ok(x * 2)

val r1 = step1(5)
val r2 = r1.map(step2(_1).unwrap_or(-1))
expect r2.unwrap() == 30  # (5 + 10) * 2
```

</details>

### Question Mark Operator

#### propagates Ok value

- propagates Ok value


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("propagates Ok value")
fn may_fail(x) -> Result<i64, text>:
    if x < 0:
        return Err("negative")
    return Ok(x * 2)

fn caller(x):
    val result = may_fail(x)?
    return Ok(result + 1)

val res = caller(5)
expect res.unwrap() == 11  # 5 * 2 + 1
```

</details>

#### propagates Err to caller

- propagates Err to caller


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("propagates Err to caller")
fn may_fail(x) -> Result<i64, text>:
    if x < 0:
        return Err("negative")
    return Ok(x * 2)

fn caller(x):
    val result = may_fail(x)?
    return Ok(result + 1)

val res = caller(-5)
expect res.unwrap_or(-99) == -99
```

</details>

#### chains multiple ? operators

- chains multiple ? operators


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("chains multiple ? operators")
fn step1(x):
    if x < 0:
        return Err("step1 failed")
    return Ok(x + 10)

fn step2(x):
    if x > 100:
        return Err("step2 failed")
    return Ok(x * 2)

fn pipeline(x):
    val a = step1(x)?
    val b = step2(a)?
    return Ok(b)

val res = pipeline(5)
expect res.unwrap() == 30  # (5 + 10) * 2
```

</details>

### Result Pattern Matching

#### matches Ok variant

- matches Ok variant


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches Ok variant")
val res = Ok(100)
var output = 0
match res:
    case Ok(value):
        output = value
    case Err(_):
        output = -1
expect output == 100
```

</details>

#### matches Err variant

- matches Err variant


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches Err variant")
val res = Err("failure")
var output = 0
match res:
    case Ok(value):
        output = value
    case Err(_):
        output = -1
expect output == -1
```

</details>

#### uses if let with Ok

- uses if let with Ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses if let with Ok")
val res = Ok(100)
var output = 0
if let Ok(value) = res:
    output = value
expect output == 100
```

</details>

#### uses if let with Err else

- uses if let with Err else


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses if let with Err else")
val res: Result<i64, text> = Err("error")
var output = 0
if let Ok(value) = res:
    output = value
else:
    output = -1
expect output == -1
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
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

- Canonical SPipe generation for source `e4e463b16aa7fdd92206fd7bdbb77b13adb462d8cab2b8718be9293fea9fa19e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e4e463b16aa7fdd92206fd7bdbb77b13adb462d8cab2b8718be9293fea9fa19e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e4e463b16aa7fdd92206fd7bdbb77b13adb462d8cab2b8718be9293fea9fa19e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/result_type_spec.spl
mirror: doc/06_spec/03_system/feature/usage/result_type_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/result_type_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/result_type_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/result_type_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates Ok with value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/result_type_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'checks Ok is ok' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/result_type_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'checks Ok is not err' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
