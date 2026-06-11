# Random Specification

> 1. rng seed

<!-- sdn-diagram:id=random_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=random_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

random_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=random_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Random Specification

## Scenarios

### Random number generation

#### Seeding

#### same seed produces same sequence

1. rng seed
2. rng seed
   - Expected: a1 equals `b1`
   - Expected: a2 equals `b2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rng_seed(42)
val a1 = rng_next()
val a2 = rng_next()
rng_seed(42)
val b1 = rng_next()
val b2 = rng_next()
expect(a1).to_equal(b1)
expect(a2).to_equal(b2)
```

</details>

#### different seeds produce different sequences

1. rng seed
2. rng seed
   - Expected: different is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rng_seed(42)
val a1 = rng_next()
rng_seed(99)
val b1 = rng_next()
# Very unlikely to be equal
val different = a1 != b1
expect(different).to_equal(true)
```

</details>

#### Range generation

#### generates value in range

1. rng seed
   - Expected: in_range is true
   - Expected: in_upper is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rng_seed(42)
val result = rng_int(1, 10)
val in_range = result >= 1
expect(in_range).to_equal(true)
val in_upper = result <= 10
expect(in_upper).to_equal(true)
```

</details>

#### generates multiple values in range

1. rng seed
   - Expected: all_in_range is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rng_seed(123)
var all_in_range = true
for _ in 0..20:
    val v = rng_int(0, 100)
    if v < 0 or v > 100:
        all_in_range = false
expect(all_in_range).to_equal(true)
```

</details>

#### generates different values

1. rng seed
   - Expected: some_different is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rng_seed(42)
val v1 = rng_next()
val v2 = rng_next()
val v3 = rng_next()
# At least two should differ
val some_different = v1 != v2 or v2 != v3
expect(some_different).to_equal(true)
```

</details>

#### Distribution properties

#### generates non-negative values

1. rng seed
   - Expected: all_positive is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rng_seed(42)
var all_positive = true
for _ in 0..50:
    val v = rng_next()
    if v < 0:
        all_positive = false
expect(all_positive).to_equal(true)
```

</details>

#### generates values spread across range

1. rng seed


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rng_seed(42)
var low_count = 0
var high_count = 0
for _ in 0..100:
    val v = rng_int(0, 99)
    if v < 50: low_count = low_count + 1
    if v >= 50: high_count = high_count + 1
# Both halves should have some values
expect(low_count).to_be_greater_than(10)
expect(high_count).to_be_greater_than(10)
```

</details>

#### Sequence operations

#### shuffles array by swapping

1. rng seed
   - Expected: arr.len() equals `5`
   - Expected: sum equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rng_seed(42)
var arr = [1, 2, 3, 4, 5]
# Fisher-Yates shuffle
for i in 0..4:
    val j = rng_int(i, 4)
    val tmp = arr[i]
    arr[i] = arr[j]
    arr[j] = tmp
# Should still have same length
expect(arr.len()).to_equal(5)
# Sum should be preserved
var sum = 0
for v in arr:
    sum = sum + v
expect(sum).to_equal(15)
```

</details>

#### picks random element from array

1. rng seed
   - Expected: valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rng_seed(42)
val items = [10, 20, 30, 40, 50]
val idx = rng_int(0, 4)
val picked = items[idx]
val valid = picked == 10 or picked == 20 or picked == 30 or picked == 40 or picked == 50
expect(valid).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/random_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Random number generation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
