# resource_exhaustion_spec

> Resource Exhaustion Resilience Specification

<!-- sdn-diagram:id=resource_exhaustion_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=resource_exhaustion_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

resource_exhaustion_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=resource_exhaustion_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# resource_exhaustion_spec

Resource Exhaustion Resilience Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/core/resilience/resource_exhaustion_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Resource Exhaustion Resilience Specification

Tests for operations under high load: large arrays, deep string
concatenation, many small allocations, and bulk computations.

Feature: Resource Exhaustion Resilience
Category: Resilience Testing
Status: Active

## Scenarios

### resilience: large arrays

#### creates and verifies a 1000-element array length

1. arr push
   - Expected: arr_len equals `1000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr: [i64] = []
for i in 0..1000:
    arr.push(i)
val arr_len = arr.len()
expect(arr_len).to_equal(1000)
```

</details>

#### array first and last element access

1. arr2 push
   - Expected: first equals `0`
   - Expected: last equals `999`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr2: [i64] = []
for i in 0..1000:
    arr2.push(i)
val first = arr2[0]
expect(first).to_equal(0)
val last = arr2[999]
expect(last).to_equal(999)
```

</details>

#### sums 1000 elements correctly

1. arr push
   - Expected: total equals `499500`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = []
for i in 0..1000:
    arr.push(i)
var total = 0
for item in arr:
    total = total + item
# Sum of 0..999 = 999 * 1000 / 2 = 499500
expect(total).to_equal(499500)
```

</details>

#### creates and searches a 500-element array

1. arr push
   - Expected: found is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = []
for i in 0..500:
    arr.push(i * 3)
# Search for known value
var found = false
for item in arr:
    if item == 300:
        found = true
expect(found).to_equal(true)
```

</details>

#### handles array of random values with correct length

1. lcg seed
2. arr push
   - Expected: arr.len() equals `1000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lcg_seed(40001)
var arr = []
for i in 0..1000:
    val item = lcg_range(0, 10000)
    arr.push(item)
expect(arr.len()).to_equal(1000)
```

</details>

#### overwrites all elements in a large array

1. arr push
   - Expected: arr[0] equals `0`
   - Expected: arr[249] equals `498`
   - Expected: arr[499] equals `998`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = []
for i in 0..500:
    arr.push(0)
for i in 0..500:
    arr[i] = i * 2
expect(arr[0]).to_equal(0)
expect(arr[249]).to_equal(498)
expect(arr[499]).to_equal(998)
```

</details>

### resilience: deep string concatenation

#### builds a 200-character string incrementally

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = ""
for i in 0..200:
    s = s + "x"
expect(s.len()).to_equal(200)
```

</details>

#### builds a 100-segment string

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = ""
for i in 0..100:
    s = s + "ab"
expect(s.len()).to_equal(200)
```

</details>

#### builds a string with varied content

1. lcg seed
   - Expected: s_len equals `150`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lcg_seed(40002)
var s = ""
for i in 0..150:
    val idx = lcg_range(0, 10)
    s = s + "x"
val s_len = s.len()
expect(s_len).to_equal(150)
```

</details>

#### concatenation preserves content order

1. parts push
   - Expected: starts_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parts: [text] = []
for i in 0..50:
    parts.push("{i}")
var combined = ""
for part in parts:
    combined = combined + part + ","
# Should start with "0,"
val starts_ok = combined.starts_with("0,")
expect(starts_ok).to_equal(true)
```

</details>

#### concatenation contains last element

1. parts2 push
   - Expected: contains_last is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var parts2: [text] = []
for i in 0..50:
    parts2.push("{i}")
var combined2 = ""
for part in parts2:
    combined2 = combined2 + part + ","
val contains_last = combined2.contains("49,")
expect(contains_last).to_equal(true)
```

</details>

### resilience: many small allocations

#### creates 500 small arrays

1. total len = total len + small len
   - Expected: total_len equals `1500`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var total_len = 0
for i in 0..500:
    val small = [i, i + 1, i + 2]
    total_len = total_len + small.len()
expect(total_len).to_equal(1500)
```

</details>

#### creates 200 small strings

1. total len = total len + s len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var total_len = 0
for i in 0..200:
    val s = "item_{i}"
    total_len = total_len + s.len()
# Each "item_X" has length 5-8 depending on i
expect(total_len).to_be_greater_than(0)
```

</details>

<details>
<summary>Advanced: nested loops with allocation do not crash</summary>

#### nested loops with allocation do not crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var total = 0
for i in 0..50:
    for j in 0..20:
        val pair = [i, j]
        total = total + pair[0] + pair[1]
# Sum of i over 50*20 iterations + sum of j over 50*20 iterations
# i: each i repeated 20 times = 20 * (0+1+...+49) = 20 * 1225 = 24500
# j: each j repeated 50 times = 50 * (0+1+...+19) = 50 * 190 = 9500
expect(total).to_equal(34000)
```

</details>


</details>

### resilience: bulk computation

#### performs 5000 arithmetic operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = 0
for i in 0..5000:
    result = result + 1
expect(result).to_equal(5000)
```

</details>

#### performs 1000 comparisons without error

1. lcg seed
   - Expected: total equals `1000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lcg_seed(40003)
var less_count = 0
var equal_count = 0
var greater_count = 0
for i in 0..1000:
    val a = lcg_range(-100, 100)
    val b = lcg_range(-100, 100)
    if a < b: less_count = less_count + 1
    if a == b: equal_count = equal_count + 1
    if a > b: greater_count = greater_count + 1
val total = less_count + equal_count + greater_count
expect(total).to_equal(1000)
```

</details>

#### performs 500 modulo operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var failures = 0
for i in 0..500:
    val n = i + 1
    val remainder = n % 7
    if remainder < 0 or remainder >= 7:
        failures = failures + 1
expect(failures).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
