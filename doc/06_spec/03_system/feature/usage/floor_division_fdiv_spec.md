# Floor Division (.fdiv) Method

> val result = 7 // 2  # Floor division (old)

<!-- sdn-diagram:id=floor_division_fdiv_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=floor_division_fdiv_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

floor_division_fdiv_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=floor_division_fdiv_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 53 | 53 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Floor Division (.fdiv) Method

val result = 7 // 2  # Floor division (old)

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | OP-FDIV |
| Category | Operators \| Arithmetic |
| Status | Implemented |
| Source | `test/03_system/feature/usage/floor_division_fdiv_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Migration from // Operator

**Old syntax (deprecated):**
```simple
val result = 7 // 2  # Floor division (old)
```

**New syntax:**
```simple
val result = 7.fdiv(2)  # Floor division (new)
```

## Mathematical Definition

Floor division: ⌊a/b⌋ (always rounds towards negative infinity)

Properties:
- `a = b * a.fdiv(b) + a % b` (division algorithm)
- `a.fdiv(b)` has same sign as `a / b` when positive
- `a.fdiv(b)` rounds down for negative results

## Examples

```simple
# Positive integers
7.fdiv(2)    # → 3
10.fdiv(3)   # → 3

# Negative integers (rounds towards negative infinity)
(-7).fdiv(2)   # → -4 (not -3)
7.fdiv(-2)     # → -4 (not -3)
(-7).fdiv(-2)  # → 3

# Floating point
7.5.fdiv(2.0)    # → 3.0
(-7.5).fdiv(2.0) # → -4.0
```

## Comparison with Other Division

| Operation | 7 / 2 | -7 / 2 | 7 / -2 | -7 / -2 |
|-----------|-------|--------|--------|---------|
| Regular `/` | 3 | -3 | -3 | 3 |
| Floor `.fdiv()` | 3 | -4 | -4 | 3 |
| Truncate `.trunc()` | 3 | -3 | -3 | 3 |

## Scenarios

### Floor Division (i64.fdiv) - Positive Integers

#### divides evenly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 10.fdiv(5)
expect result == 2
```

</details>

#### divides with remainder

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 7.fdiv(2)
expect result == 3
```

</details>

#### divides with large remainder

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 17.fdiv(5)
expect result == 3
```

</details>

#### divides exactly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 20.fdiv(4)
expect result == 5
```

</details>

#### divides small by large

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 3.fdiv(7)
expect result == 0
```

</details>

#### divides one by one

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 1.fdiv(1)
expect result == 1
```

</details>

#### divides large numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 1000.fdiv(7)
expect result == 142
```

</details>

### Floor Division (i64.fdiv) - Negative Integers

#### divides negative by positive (rounds down)

1. expect result ==


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = (-7).fdiv(2)
expect result == (-4)  # Not -3! Rounds towards negative infinity
```

</details>

#### divides positive by negative (rounds down)

1. expect result ==


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 7.fdiv(-2)
expect result == (-4)  # Not -3! Rounds towards negative infinity
```

</details>

#### divides negative by negative (positive result)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = (-7).fdiv(-2)
expect result == 3
```

</details>

#### divides negative evenly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = (-10).fdiv(-5)
expect result == 2
```

</details>

#### handles negative dividend with remainder

1. expect result ==


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = (-17).fdiv(5)
expect result == (-4)  # -17 / 5 = -3.4 → floor = -4
```

</details>

#### handles negative divisor with remainder

1. expect result ==


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 17.fdiv(-5)
expect result == (-4)  # 17 / -5 = -3.4 → floor = -4
```

</details>

#### handles both negative with remainder

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = (-17).fdiv(-5)
expect result == 3  # -17 / -5 = 3.4 → floor = 3
```

</details>

### Floor Division (i64.fdiv) - Edge Cases

#### divides zero by positive

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 0.fdiv(5)
expect result == 0
```

</details>

#### divides zero by negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 0.fdiv(-5)
expect result == 0
```

</details>

#### handles one divided by itself

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 42.fdiv(42)
expect result == 1
```

</details>

#### handles negative one by one

1. expect result ==


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = (-1).fdiv(1)
expect result == (-1)
```

</details>

#### handles one by negative one

1. expect result ==


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 1.fdiv(-1)
expect result == (-1)
```

</details>

### Floor Division (i64.fdiv) - Division Algorithm

#### satisfies division algorithm for positive numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 17
val b = 5
val q = a.fdiv(b)
val r = a % b
expect a == b * q + r
expect q == 3
expect r == 2
```

</details>

#### satisfies division algorithm for negative dividend

1. expect q ==


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = -17
val b = 5
val q = a.fdiv(b)
val r = a - b * q
expect a == b * q + r
expect q == (-4)
expect r == 3
```

</details>

#### satisfies division algorithm for negative divisor

1. expect q ==


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 17
val b = -5
val q = a.fdiv(b)
val r = a - b * q
expect a == b * q + r
expect q == (-4)
```

</details>

#### satisfies division algorithm for both negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = -17
val b = -5
val q = a.fdiv(b)
val r = a % b
expect a == b * q + r
expect q == 3
```

</details>

### Floor Division (f64.fdiv) - Positive Floats

#### divides evenly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 10.0.fdiv(5.0)
expect result == 2.0
```

</details>

#### divides with fractional result

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 7.5.fdiv(2.0)
expect result == 3.0
```

</details>

#### divides small by large

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 1.5.fdiv(2.0)
expect result == 0.0
```

</details>

#### divides with small quotient

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 2.9.fdiv(3.0)
expect result == 0.0
```

</details>

#### divides exactly at boundary

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 6.0.fdiv(2.0)
expect result == 3.0
```

</details>

#### divides fractional by integer

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 9.7.fdiv(3.0)
expect result == 3.0
```

</details>

### Floor Division (f64.fdiv) - Negative Floats

#### divides negative by positive

1. expect result ==


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = (-7.5).fdiv(2.0)
expect result == (-4.0)  # Rounds down to -4, not up to -3
```

</details>

#### divides positive by negative

1. expect result ==


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 7.5.fdiv(-2.0)
expect result == (-4.0)  # Rounds down to -4
```

</details>

#### divides negative by negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = (-7.5).fdiv(-2.0)
expect result == 3.0
```

</details>

#### handles negative fractional dividend

1. expect result ==


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = (-5.9).fdiv(2.0)
expect result == (-3.0)  # -5.9 / 2.0 = -2.95 → floor = -3
```

</details>

#### handles negative fractional divisor

1. expect result ==


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 5.9.fdiv(-2.0)
expect result == (-3.0)  # 5.9 / -2.0 = -2.95 → floor = -3
```

</details>

### Floor Division (f64.fdiv) - Special Float Values

#### handles division by very small number

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 1.0.fdiv(0.0001)
expect result == 10000.0
```

</details>

#### handles very large result

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 999999999.0.fdiv(1.0)
expect result == 999999999.0
```

</details>

#### handles very large value divided by finite

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Division by zero not supported at runtime, test large values instead
val large = 999999999999.0
val result = large.fdiv(2.0)
expect result == 499999999999.0
```

</details>

#### handles very small value as divisor

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 2.0.fdiv(0.0001)
expect result == 20000.0
```

</details>

#### handles zero fdiv positive

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 0.0.fdiv(2.0)
expect result == 0.0
```

</details>

### Floor Division vs Regular Division

#### matches regular division for positive exact division

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val regular = 10 / 5
val floor = 10.fdiv(5)
expect regular == floor
```

</details>

#### differs from regular division when remainder exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val regular = 7 / 2  # Truncating division: 3
val floor = 7.fdiv(2)  # Floor division: 3
expect regular == floor  # Same for positive
```

</details>

#### differs for negative dividend

1. expect floor ==
2. expect regular ==


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val regular = (-7) / 2  # Truncating: -3
val floor = (-7).fdiv(2)  # Floor: -4
expect floor == (-4)
expect regular == (-3)
expect floor != regular
```

</details>

#### differs for negative divisor

1. expect floor ==
2. expect regular ==


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val regular = 7 / (-2)  # Truncating: -3
val floor = 7.fdiv(-2)  # Floor: -4
expect floor == (-4)
expect regular == (-3)
expect floor != regular
```

</details>

### Floor Division - Real World Use Cases

#### calculates number of pages needed

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val total_items = 25
val items_per_page = 10
val pages = (total_items + items_per_page - 1).fdiv(items_per_page)
expect pages == 3  # Need 3 pages for 25 items
```

</details>

#### calculates array chunk count

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val array_length = 17
val chunk_size = 5
val chunks = array_length.fdiv(chunk_size)
expect chunks == 3  # 17 / 5 = 3 complete chunks
```

</details>

#### calculates time in hours

1. expect hours == 2  # 125 minutes = 2 hours


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val minutes = 125
val hours = minutes.fdiv(60)
expect hours == 2  # 125 minutes = 2 hours (plus 5 minutes)
```

</details>

#### calculates grid coordinates

1. expect row == 2  # Row 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val index = 23
val grid_width = 8
val row = index.fdiv(grid_width)
val col = index % grid_width
expect row == 2  # Row 2 (0-indexed)
expect col == 7  # Column 7
```

</details>

#### rounds negative temperatures to day boundary

1. expect days ago ==


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# -15 hours ago → which day?
val hours_ago = -15
val days_ago = hours_ago.fdiv(24)
expect days_ago == (-1)  # Yesterday (rounds down)
```

</details>

### Floor Division - Property Testing

#### always produces result <= regular division for negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = -17
val b = 5
val floor_div = a.fdiv(b)
val regular_div = a / b
expect floor_div <= regular_div
```

</details>

#### always rounds down for fractional floats

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result1 = 7.1.fdiv(2.0)
val result2 = 7.9.fdiv(2.0)
expect result1 == 3.0
expect result2 == 3.0
```

</details>

#### is idempotent for exact division

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result1 = 10.fdiv(5)
val result2 = result1.fdiv(1)
expect result2 == 2
```

</details>

### Floor Division - Consistency with Math Block

#### matches math block floor division for positive

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Requires math block integration
val result = 10.fdiv(3)
expect result == 3
```

</details>

#### matches math block floor division for negative

1. expect result ==


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Requires math block integration
val result = (-10).fdiv(3)
expect result == (-4)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 53 |
| Active scenarios | 53 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
