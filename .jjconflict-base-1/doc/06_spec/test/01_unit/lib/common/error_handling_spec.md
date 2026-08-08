# Error Handling Specification

> <details>

<!-- sdn-diagram:id=error_handling_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=error_handling_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

error_handling_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=error_handling_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Error Handling Specification

## Scenarios

### Result type

#### creates Ok result

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result: Result<i64, text> = Ok(42)
match result:
    case Ok(value):
        expect value == 42
    case Err(_):
        expect false
```

</details>

#### creates Err result

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result: Result<i64, text> = Err("failed")
match result:
    case Err(msg):
        expect msg == "failed"
    case Ok(_):
        expect false
```

</details>

#### uses is_ok and is_err

- expect ok result is ok
- expect not ok result is err
- expect err result is err
- expect not err result is ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok_result: Result<i64, text> = Ok(42)
val err_result: Result<i64, text> = Err("failed")

expect ok_result.is_ok()
expect not ok_result.is_err()
expect err_result.is_err()
expect not err_result.is_ok()
```

</details>

#### unwraps Ok values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result: Result<i64, text> = Ok(42)
val value = result.unwrap()
expect value == 42
```

</details>

#### provides default on error

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result: Result<i64, text> = Err("failed")
val value = result.unwrap_or(0)
expect value == 0
```

</details>

#### maps Ok values

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result: Result<i64, text> = Ok(10)
val doubled = result.map(_1 * 2)
match doubled:
    case Ok(value):
        expect value == 20
    case Err(_):
        expect false
```

</details>

#### maps Err values

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result: Result<i64, text> = Err("error")
val mapped = result.map_err(&:upper)
match mapped:
    case Err(msg):
        expect msg == "ERROR"
    case Ok(_):
        expect false
```

</details>

### Option type

#### creates Some option

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt: Option<i64> = Some(42)
match opt:
    case Some(value):
        expect value == 42
    case None:
        expect false
```

</details>

#### creates None option

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt: Option<i64> = None
match opt:
    case None:
        expect true
    case Some(_):
        expect false
```

</details>

#### uses is_some and is_none

- expect some val is some
- expect not some val is none
- expect none val is none
- expect not none val is some


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val some_val: Option<i64> = Some(42)
val none_val: Option<i64> = None

expect some_val.is_some()
expect not some_val.is_none()
expect none_val.is_none()
expect not none_val.is_some()
```

</details>

#### unwraps Some values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt: Option<i64> = Some(42)
val value = opt.unwrap()
expect value == 42
```

</details>

#### provides default on None

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt: Option<i64> = None
val value = opt.unwrap_or(0)
expect value == 0
```

</details>

#### maps Some values

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt: Option<i64> = Some(10)
val doubled = opt.map(_1 * 2)
match doubled:
    case Some(value):
        expect value == 20
    case None:
        expect false
```

</details>

#### filters Some values

- expect filtered is some
- expect rejected is none


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt: Option<i64> = Some(10)
val filtered = opt.filter(_1 > 5)
expect filtered.is_some()

val rejected = opt.filter(_1 < 5)
expect rejected.is_none()
```

</details>

### Try operator

#### propagates errors with ?

- fn divide
- Err
- Ok
- fn complex calc
- Ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn divide(a: i64, b: i64) -> Result<i64, text>:
    if b == 0:
        Err("Division by zero")
    else:
        Ok(a / b)

fn complex_calc(x: i64) -> Result<i64, text>:
    val step1 = divide(x, 2)?
    val step2 = divide(step1, 3)?
    Ok(step2)

val result = complex_calc(18)
match result:
    case Ok(value):
        expect value == 3  # 18/2/3 = 3
    case Err(_):
        expect false
```

</details>

#### short-circuits on first error

- fn may fail early
- Ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn may_fail_early() -> Result<i64, text>:
    val x = Err("Early error")?
    Ok(x)

val result = may_fail_early()
match result:
    case Err(msg):
        expect msg == "Early error"
    case Ok(_):
        expect false
```

</details>

### Optional chaining

#### chains with ?. operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Address:
    city: text

struct Person:
    address: Option<Address>

val person = Person(address: Some(Address(city: "NYC")))
val city = person.address?.city
match city:
    case Some(c):
        expect c == "NYC"
    case None:
        expect false
```

</details>

#### returns None on any None in chain

- expect city is none


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Address:
    city: text

struct Person:
    address: Option<Address>

val person = Person(address: None)
val city = person.address?.city
expect city.is_none()
```

</details>

### Null coalescing

#### uses ?? for default values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val maybe_value: Option<i64> = None
val value = maybe_value ?? 42
expect value == 42
```

</details>

#### returns value when Some

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val maybe_value: Option<i64> = Some(10)
val value = maybe_value ?? 42
expect value == 10
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/error_handling_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Result type
- Option type
- Try operator
- Optional chaining
- Null coalescing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
