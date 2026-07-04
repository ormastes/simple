# Result Type Specification

> Tests for the Result type representing success or error outcomes, including constructors, pattern matching, and safe unwrapping mechanisms.

<!-- sdn-diagram:id=result_type_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=result_type_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

result_type_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=result_type_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

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

## Scenarios

### Result Type Basic Usage

#### Ok values

#### creates Ok with value

1. expect res unwrap


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = Ok(42)
expect res.unwrap() == 42
```

</details>

#### checks Ok is ok

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = Ok(10)
expect res.ok.?
```

</details>

#### checks Ok is not err

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = Ok(5)
expect not res.err.?
```

</details>

#### Err values

#### creates Err with error

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = Err("error message")
expect res.err.?
```

</details>

#### checks Err is not ok

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = Err("oops")
expect not res.ok.?
```

</details>

#### uses unwrap_or for Err

1. expect res unwrap or


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = Err("error")
expect res.unwrap_or(99) == 99
```

</details>

### Result from Functions

#### returns Ok from function

1. fn safe divide
2. expect r unwrap


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn safe_divide(a, b):
    if b == 0:
        return Err("division by zero")
    return Ok(a / b)

val r = safe_divide(20, 4)
expect r.unwrap() == 5
```

</details>

#### returns Err from function

1. fn safe divide
2. expect r unwrap or


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn safe_divide(a, b):
    if b == 0:
        return Err("division by zero")
    return Ok(a / b)

val r = safe_divide(10, 0)
expect r.unwrap_or(-1) == -1
```

</details>

#### chains Result operations

1. fn step1
2. fn step2
3. expect r2 unwrap


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn may fail
2. fn caller
3. expect res unwrap


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn may fail
2. fn caller
3. expect res unwrap or


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn step1
2. fn step2
3. fn pipeline
4. expect res unwrap


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = Ok(100)
var output = 0
if let Ok(value) = res:
    output = value
expect output == 100
```

</details>

#### uses if let with Err else

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
