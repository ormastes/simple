# Try Operator Specification

> 1. expect result is ok

<!-- sdn-diagram:id=try_operator_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=try_operator_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

try_operator_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=try_operator_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Try Operator Specification

## Scenarios

### Try operator (?)

#### with Result type

#### unwraps Ok values

1. expect result is ok
2. expect result unwrap


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = divide(a=10, b=2)
expect result.is_ok() == true
expect result.unwrap() == 5
```

</details>

#### propagates Err on failure

1. expect result is err


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = compute_ratio(a=100, b=0, c=5)
expect result.is_err() == true
```

</details>

#### chains multiple ? operations

1. expect result is ok
2. expect result unwrap


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = compute_ratio(a=100, b=5, c=2)
# 100 / 5 = 20, 20 / 2 = 10
expect result.is_ok() == true
expect result.unwrap() == 10
```

</details>

#### stops at first error in chain

1. expect result is err


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = safe_sqrt_ratio(a=10, b=0)
# First division fails
expect result.is_err() == true
```

</details>

#### handles negative sqrt error

1. expect result is err


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = safe_sqrt_ratio(a=-100, b=10)
# -100 / 10 = -10, sqrt(-10) fails
expect result.is_err() == true
```

</details>

#### completes successfully when all succeed

1. expect result is ok
2. expect result unwrap


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = safe_sqrt_ratio(a=100, b=4)
# 100 / 4 = 25, sqrt(25) = 5
expect result.is_ok() == true
expect result.unwrap() == 5
```

</details>

#### with Option type

#### unwraps Some values

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [10, 20, 30]
val result = find_value(arr, 20)
val is_some = result.is_some()
expect(is_some).to_equal(true)
val unwrapped = result.unwrap()
expect(unwrapped).to_equal(1)
```

</details>

#### propagates None on not found

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [10, 20, 30]
val result = get_element(arr, 99)
val is_none = result.is_none()
expect(is_none).to_equal(true)
```

</details>

#### returns value when found

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [10, 20, 30]
val result = get_element(arr, 20)
val is_some = result.is_some()
expect(is_some).to_equal(true)
val unwrapped = result.unwrap()
expect(unwrapped).to_equal(20)
```

</details>

#### early return behavior

#### returns immediately on Err

1. fn test early return
2. expect result is err


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This tests that code after ? doesn't execute on error
fn test_early_return(x: i64) -> Result<i64, text>:
    val result_val = divide(a=10, b=x)?
    # This line should not execute if x == 0
    return Ok(result_val * 1000)

val result = test_early_return(0)
expect result.is_err() == true
```

</details>

#### continues execution on Ok

1. fn test continue
2. expect result is ok
3. expect result unwrap


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn test_continue(x: i64) -> Result<i64, text>:
    val result_val = divide(a=10, b=x)?
    return Ok(result_val * 1000)

val result = test_continue(2)
expect result.is_ok() == true
expect result.unwrap() == 5000
```

</details>

#### nested function calls

#### propagates through call stack

1. fn inner
2. fn middle
3. fn outer
4. expect result is ok
5. expect result unwrap
   - Expected: is_err2 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn inner(x: i64) -> Result<i64, text>:
    return divide(a=100, b=x)

fn middle(x: i64) -> Result<i64, text>:
    val inner_val = inner(x)?
    return Ok(inner_val + 1)

fn outer(x: i64) -> Result<i64, text>:
    val mid_val = middle(x)?
    return Ok(mid_val * 2)

# Success case: 100/5=20, 20+1=21, 21*2=42
val result = outer(5)
expect result.is_ok() == true
expect result.unwrap() == 42

# Failure case: division by zero propagates up
val result_fail = outer(0)
val is_err2 = result_fail.is_err()
expect(is_err2).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/shared/types/try_operator_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Try operator (?)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
