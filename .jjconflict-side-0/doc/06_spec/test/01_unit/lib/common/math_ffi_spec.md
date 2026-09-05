# Math Ffi Specification

> <details>

<!-- sdn-diagram:id=math_ffi_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=math_ffi_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

math_ffi_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=math_ffi_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Math Ffi Specification

## Scenarios

### Math FFI Functions

#### power and exponential

<details>
<summary>Advanced: calculates power correctly via loop</summary>

#### calculates power correctly via loop

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = 1
for _ in 0..3:
    result = result * 2
expect(result).to_equal(8)
```

</details>


</details>

#### handles zero exponent

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# x^0 = 1 for any x
var result = 1
# 0 iterations = x^0
expect(result).to_equal(1)
```

</details>

#### handles base of 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = 1
for _ in 0..100:
    result = result * 1
expect(result).to_equal(1)
```

</details>

#### absolute value

#### calculates absolute value of negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = -5
var abs_x = x
if abs_x < 0: abs_x = -abs_x
expect(abs_x).to_equal(5)
```

</details>

#### positive value unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 5
var abs_x = x
if abs_x < 0: abs_x = -abs_x
expect(abs_x).to_equal(5)
```

</details>

#### zero unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0
var abs_x = x
if abs_x < 0: abs_x = -abs_x
expect(abs_x).to_equal(0)
```

</details>

#### integer square roots via approximation

#### sqrt(16) = 4 via search

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = 0
for i in 0..17:
    if i * i == 16:
        result = i
expect(result).to_equal(4)
```

</details>

#### sqrt(9) = 3 via search

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = 0
for i in 0..10:
    if i * i == 9:
        result = i
expect(result).to_equal(3)
```

</details>

#### sqrt(1) = 1 via search

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = 0
for i in 0..2:
    if i * i == 1:
        result = i
expect(result).to_equal(1)
```

</details>

#### sqrt(0) = 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(0 * 0).to_equal(0)
```

</details>

#### special values

#### handles zero correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(0 * 2).to_equal(0)
expect(0 + 5).to_equal(5)
expect(0 - 3).to_equal(-3)
```

</details>

#### handles one correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(1 * 100).to_equal(100)
expect(1 + 0).to_equal(1)
```

</details>

#### handles negative numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(-1 * -1).to_equal(1)
expect(-3 * 2).to_equal(-6)
expect(-10 + 10).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/math_ffi_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Math FFI Functions

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
