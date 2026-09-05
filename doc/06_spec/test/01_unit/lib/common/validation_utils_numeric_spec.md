# Validation Utils Numeric Specification

> <details>

<!-- sdn-diagram:id=validation_utils_numeric_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=validation_utils_numeric_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

validation_utils_numeric_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=validation_utils_numeric_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Validation Utils Numeric Specification

## Scenarios

### std.validation_utils

### is_positive

#### returns true for positive numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_positive(1)).to_equal(true)
expect(is_positive(42)).to_equal(true)
```

</details>

#### returns false for zero and negatives

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_positive(0)).to_equal(false)
expect(is_positive(-1)).to_equal(false)
```

</details>

### is_negative

#### returns true for negative numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_negative(-1)).to_equal(true)
expect(is_negative(-42)).to_equal(true)
```

</details>

#### returns false for zero and positives

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_negative(0)).to_equal(false)
expect(is_negative(1)).to_equal(false)
```

</details>

### is_non_negative

#### returns true for zero and positives

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_non_negative(0)).to_equal(true)
expect(is_non_negative(42)).to_equal(true)
```

</details>

#### returns false for negatives

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_non_negative(-1)).to_equal(false)
```

</details>

### is_zero

#### returns true for zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_zero(0)).to_equal(true)
```

</details>

#### returns false for non-zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_zero(1)).to_equal(false)
expect(is_zero(-1)).to_equal(false)
```

</details>

### is_in_range

#### returns true when in range

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_in_range(5, 1, 10)).to_equal(true)
expect(is_in_range(1, 1, 10)).to_equal(true)
expect(is_in_range(10, 1, 10)).to_equal(true)
```

</details>

#### returns false when out of range

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_in_range(0, 1, 10)).to_equal(false)
expect(is_in_range(11, 1, 10)).to_equal(false)
```

</details>

### is_outside_range

#### returns true when outside range

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_outside_range(0, 1, 10)).to_equal(true)
expect(is_outside_range(11, 1, 10)).to_equal(true)
```

</details>

#### returns false when in range

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_outside_range(5, 1, 10)).to_equal(false)
```

</details>

### is_not_empty

#### returns true for non-empty strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_not_empty("hello")).to_equal(true)
```

</details>

#### returns false for empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_not_empty("")).to_equal(false)
```

</details>

### is_empty

#### returns true for empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_empty("")).to_equal(true)
```

</details>

#### returns false for non-empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_empty("hello")).to_equal(false)
```

</details>

### is_divisible

#### checks divisibility

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_divisible(10, 5)).to_equal(true)
expect(is_divisible(10, 3)).to_equal(false)
```

</details>

#### handles zero divisor

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_divisible(10, 0)).to_equal(false)
```

</details>

### is_multiple_of

#### checks if multiple

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_multiple_of(15, 5)).to_equal(true)
expect(is_multiple_of(15, 4)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/validation_utils_numeric_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- std.validation_utils
- is_positive
- is_negative
- is_non_negative
- is_zero
- is_in_range
- is_outside_range
- is_not_empty
- is_empty
- is_divisible
- is_multiple_of

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
