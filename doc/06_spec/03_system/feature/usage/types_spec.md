# Simple Language Type System - Test Specification

> Executable tests for Simple's type system basics: primitives, mutability, generics, and type inference.

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
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Language Type System - Test Specification

Executable tests for Simple's type system basics: primitives, mutability, generics, and type inference.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #20-29 |
| Category | Language Features |
| Status | Stable (Basic Features) |
| Source | `test/03_system/feature/usage/types_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Executable tests for Simple's type system basics: primitives, mutability, generics, and type inference.

Note: Advanced features (unit types, capability effects, suspension operators) are not yet implemented.

## Scenarios

### Types Spec

#### basic type literals

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# String, integer, boolean, float literals
val s = "hello"
val i = 42
val b = true
val f = 3.14
expect(s).to_equal("hello")
expect(i).to_equal(42)
expect(b).to_equal(true)
```

</details>

#### mutability rules - val and const

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val y = 20
const MAX = 100
expect(y).to_equal(20)
expect(MAX).to_equal(100)
```

</details>

#### mutable variables

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var count = 0
count = count + 1
count = count + 1
expect(count).to_equal(2)
```

</details>

#### generic container - array

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Array is a generic type [T]
val numbers = [1, 2, 3, 4, 5]
val strings = ["a", "b", "c"]
expect(numbers[0]).to_equal(1)
expect(strings[1]).to_equal("b")
```

</details>

#### option type basic usage

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Option is a built-in generic type
val some_val = 42
val none_val = nil

# Basic Option behavior
if some_val != nil:
    expect(some_val).to_equal(42)

if none_val == nil:
    check(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
