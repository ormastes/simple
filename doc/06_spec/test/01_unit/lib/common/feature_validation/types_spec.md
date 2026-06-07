# Types Feature Validation

> Validates Option and Result types including Some/nil, the .? operator, ?? null coalescing, and the Result pattern for error handling.

<!-- sdn-diagram:id=types_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=types_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

types_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=types_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 32 | 32 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Types Feature Validation

Validates Option and Result types including Some/nil, the .? operator, ?? null coalescing, and the Result pattern for error handling.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #27 Option and Result |
| Category | Types |
| Status | Complete |
| Source | `test/01_unit/lib/common/feature_validation/types_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates Option and Result types including Some/nil, the .? operator,
?? null coalescing, and the Result pattern for error handling.

## Scenarios

### Feature #27 - Option Type

#### Some values

#### creates Some with integer

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = Some(42)
expect(opt).to_equal(Some(42))
```

</details>

#### creates Some with string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = Some("hello")
expect(opt).to_equal(Some("hello"))
```

</details>

#### creates Some with boolean

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = Some(true)
expect(opt).to_equal(Some(true))
```

</details>

#### creates Some with array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = Some([1, 2, 3])
expect(opt).to_equal(Some([1, 2, 3]))
```

</details>

#### nil values

#### represents absence with nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = nil
expect(opt).to_be_nil()
```

</details>

#### nil equals nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(nil).to_equal(nil)
```

</details>

#### null coalescing (??)

#### returns value when present

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = Some(42)
val result = opt ?? 0
expect(result).to_equal(42)
```

</details>

#### returns default when nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = nil
val result = opt ?? 99
expect(result).to_equal(99)
```

</details>

#### returns default string when nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = nil
val display = name ?? "Anonymous"
expect(display).to_equal("Anonymous")
```

</details>

#### returns value string when present

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = Some("Alice")
val display = name ?? "Anonymous"
expect(display).to_equal("Alice")
```

</details>

#### unwrap operations

#### unwrap extracts Some value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = Some(42)
expect(opt.unwrap()).to_equal(42)
```

</details>

#### unwrap_or returns value for Some

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = Some(10)
expect(opt.unwrap_or(0)).to_equal(10)
```

</details>

#### unwrap_or returns default for nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = nil
expect(opt.unwrap_or(99)).to_equal(99)
```

</details>

#### conditional checks

#### Some is not nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = Some(1)
val check = opt != nil
expect(check).to_equal(true)
```

</details>

#### nil is nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = nil
val check = opt == nil
expect(check).to_equal(true)
```

</details>

#### Option in collections

#### uses Option with array elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = [1, 2, 3]
val first = if items.len() > 0: Some(items[0]) else: nil
expect(first).to_equal(Some(1))
```

</details>

#### uses nil for empty collection

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = []
val first = if items.len() > 0: Some(items[0]) else: nil
expect(first).to_be_nil()
```

</details>

### Feature #27 - Result Pattern

#### Ok values

#### creates Ok with integer

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = Ok(42)
expect(result.is_ok()).to_equal(true)
```

</details>

#### creates Ok with string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = Ok("success")
expect(result.is_ok()).to_equal(true)
```

</details>

#### extracts Ok value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = Ok(100)
expect(result.unwrap()).to_equal(100)
```

</details>

#### Err values

#### creates Err with string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = Err("something went wrong")
expect(result.is_err()).to_equal(true)
```

</details>

#### extracts Err value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = Err("failure")
expect(result.unwrap_err()).to_equal("failure")
```

</details>

#### Result checks

#### is_ok returns true for Ok

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = Ok(1)
expect(result.is_ok()).to_equal(true)
```

</details>

#### is_ok returns false for Err

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = Err("error")
expect(result.is_ok()).to_equal(false)
```

</details>

#### is_err returns true for Err

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = Err("error")
expect(result.is_err()).to_equal(true)
```

</details>

#### is_err returns false for Ok

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = Ok(1)
expect(result.is_err()).to_equal(false)
```

</details>

#### Result unwrap_or

#### returns value for Ok

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = Ok(42)
expect(result.unwrap_or(0)).to_equal(42)
```

</details>

#### returns default for Err

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = Err("error")
expect(result.unwrap_or(0)).to_equal(0)
```

</details>

#### Result conversion to Option

#### ok() converts Ok to Some

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = Ok(42)
val opt = result.ok()
expect(opt).to_equal(Some(42))
```

</details>

#### ok() converts Err to none

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = Err("error")
val opt = result.ok()
# In interpreter, Err.ok() returns Option::None which differs from nil.
# Verify it is not a Some value.
val is_none = opt.unwrap_or(-1)
expect(is_none).to_equal(-1)
```

</details>

#### error handling patterns

#### uses Result for fallible computation

1. fn safe divide
2. Ok
   - Expected: result1.unwrap() equals `5`
   - Expected: result2.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn safe_divide(a, b):
    if b == 0:
        return Err("division by zero")
    Ok(a / b)

val result1 = safe_divide(10, 2)
expect(result1.unwrap()).to_equal(5)

val result2 = safe_divide(10, 0)
expect(result2.is_err()).to_equal(true)
```

</details>

#### chains Result with unwrap_or

1. fn parse number
2. Err
   - Expected: value equals `42`
   - Expected: fallback equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn parse_number(s):
    if s == "42":
        return Ok(42)
    Err("not a number")

val value = parse_number("42").unwrap_or(-1)
expect(value).to_equal(42)

val fallback = parse_number("abc").unwrap_or(-1)
expect(fallback).to_equal(-1)
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
