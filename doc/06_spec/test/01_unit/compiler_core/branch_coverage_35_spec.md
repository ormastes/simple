# Branch Coverage Test Suite - Optional Functions & Type System

> Tests functions returning Optional types and type inference paths to cover expr_is_option (line 504) and option_base_stype (lines 208-213).

<!-- sdn-diagram:id=branch_coverage_35_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=branch_coverage_35_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

branch_coverage_35_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=branch_coverage_35_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Branch Coverage Test Suite - Optional Functions & Type System

Tests functions returning Optional types and type inference paths to cover expr_is_option (line 504) and option_base_stype (lines 208-213).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #BRANCH #OPTIONAL_FUNCTIONS #TYPE_INFERENCE |
| Category | Testing |
| Status | Implemented |
| Source | `test/01_unit/compiler_core/branch_coverage_35_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests functions returning Optional types and type inference paths
to cover expr_is_option (line 504) and option_base_stype (lines 208-213).

## Scenarios

### Functions Returning Optional

#### function with optional return

1. fn maybe value
2. Some
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn maybe_value() -> i64?:
    Some(42)

val result = maybe_value()
check(result.?)
```

</details>

#### function returning nil

1. fn get none
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn get_none() -> i64?:
    nil

val result = get_none()
check(not result.?)
```

</details>

#### conditional optional return

1. fn conditional
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn conditional(flag: bool) -> i64?:
    if flag:
        return Some(100)
    nil

check(conditional(true).?)
check(not conditional(false).?)
```

</details>

### Optional in Expressions

#### optional function in if

1. fn maybe positive
2. Some
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn maybe_positive() -> i64?:
    Some(5)

if maybe_positive().?:
    check(true)
else:
    check(false)
```

</details>

#### optional with default

1. fn might fail
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn might_fail() -> i64?:
    nil

val value = might_fail() ?? 99
check(value == 99)
```

</details>

#### optional coalesce with value

1. fn get optional
2. Some
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn get_optional() -> i64?:
    Some(10)

val result = get_optional() ?? 0
check(result == 10)
```

</details>

### Type Inference for Optionals

#### infer from Some

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = Some(42)
check(x.?)
```

</details>

#### infer from nil

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n: i64? = nil
check(not n.?)
```

</details>

#### infer from function

1. fn returns opt
2. Some
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn returns_opt() -> text?:
    Some("hello")

val s = returns_opt()
check(s.?)
```

</details>

### Long Type Names

#### struct with long name

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct VeryLongStructNameForTestingBufferLimits:
    value: i64

val item = VeryLongStructNameForTestingBufferLimits(value: 42)
check(item.value == 42)
```

</details>

#### optional of long struct

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct AnotherVeryLongNameToTestOptionalHandling:
    id: i64

val opt: AnotherVeryLongNameToTestOptionalHandling? = nil
check(not opt.?)
```

</details>

### Nested Optional Types

#### optional of optional

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val o1 = Some(Some(42))
check(o1.?)
```

</details>

#### optional of optional - nil inner

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val o2 = Some(nil)
check(o2.?)
```

</details>

#### function returning nested optional

1. fn nested opt
2. Some
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn nested_opt() -> i64?:
    Some(100)

val result = nested_opt()
check(result.?)
```

</details>

### Optional Struct Fields

#### struct with optional field

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Record:
    id: i64
    optional_value: i64?

val r1 = Record(id: 1, optional_value: Some(10))
val r2 = Record(id: 2, optional_value: nil)

check(r1.optional_value.?)
check(not r2.optional_value.?)
```

</details>

### Optional in Collections

#### array of optionals

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [Some(1), nil, Some(3)]
check(arr[0].?)
check(not arr[1].?)
```

</details>

#### optional array

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt_arr = Some([1, 2, 3])
check(opt_arr.?)
```

</details>

### Type Base Extraction

#### non-optional type

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val y: i64 = 42
check(y == 42)
```

</details>

#### text type

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s: text = "hello"
check(s == "hello")
```

</details>

#### bool type

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: bool = true
check(b)
```

</details>

#### optional extract via coalesce

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x: i64? = Some(42)
val unwrapped = x ?? 0
check(unwrapped == 42)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
