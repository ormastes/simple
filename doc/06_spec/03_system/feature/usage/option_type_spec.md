# Option Type Specification

> Tests for the Option type representing values that may or may not be present, including constructors, pattern matching, and safe unwrapping mechanisms.

<!-- sdn-diagram:id=option_type_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=option_type_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

option_type_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=option_type_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Option Type Specification

Tests for the Option type representing values that may or may not be present, including constructors, pattern matching, and safe unwrapping mechanisms.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #OPT-001 |
| Category | Language |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/03_system/feature/usage/option_type_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for the Option type representing values that may or may not be present,
including constructors, pattern matching, and safe unwrapping mechanisms.

## Syntax

```simple
val maybe_value: Option<i32> = Some(42)
val no_value: Option<text> = nil

match maybe_value:
Some(x) => print "Value is {x}"
None => print "No value"

val unwrapped = maybe_value.unwrap()           # Raises if None
val safe = maybe_value.unwrap_or(0)            # Default if None
val mapped = maybe_value.map(_1 * 2)           # Transform if Some
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Some | Option containing a value |
| None | Option representing absence of value |
| Unwrapping | Extracting value from Option |
| Safe Unwrap | Get value or default/error handling |
| Composition | Chaining operations on Options |

## Behavior

- Option<T> is generic over type T
- Some(value) contains a value of type T
- None represents absence (no value)
- Pattern matching provides exhaustive case handling
- map/filter/flat_map for functional composition
- unwrap() raises error, unwrap_or() provides default value
- Existence check with .? operator

## Scenarios

### Option Type Basic Usage

#### Some values

#### creates Some with value

1. expect opt unwrap


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = Some(42)
expect opt.unwrap() == 42
```

</details>

#### checks Some is some

1. expect opt is some


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = Some(1)
expect opt.is_some()
```

</details>

#### None values

#### creates None

1. expect opt is none


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = nil
expect opt.is_none()
```

</details>

#### uses unwrap_or for None

1. expect opt unwrap or


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = nil
expect opt.unwrap_or(99) == 99
```

</details>

### Option Type Transformations

#### maps Some value

1. expect res unwrap


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = Some(10)
val res = opt.map(_1 * 2)
expect res.unwrap() == 20
```

</details>

#### maps None returns None

1. expect res is none


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt: Option<i64> = nil
val res = opt.map(_1 * 2)
expect res.is_none()
```

</details>

### Existence Check Operator

#### returns true for Some

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = Some(42)
expect opt.?
```

</details>

#### returns false for None

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt: Option<i64> = nil
expect not opt.?
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
