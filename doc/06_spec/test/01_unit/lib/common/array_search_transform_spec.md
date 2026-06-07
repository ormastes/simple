# Array Search Transform Specification

> <details>

<!-- sdn-diagram:id=array_search_transform_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=array_search_transform_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

array_search_transform_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=array_search_transform_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 35 | 35 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Array Search Transform Specification

## Scenarios

### std.array

### array_position

#### finds index of matching element

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val idx = array_position([10, 20, 30], fn(x): x == 20)
expect(idx).to_equal(1)
```

</details>

#### returns -1 when not found

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val idx = array_position([10, 20, 30], fn(x): x == 99)
expect(idx).to_equal(-1)
```

</details>

### array_find

#### finds first matching element

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val found = array_find([10, 20, 30], fn(x): x > 15)
expect(found).to_equal(20)
```

</details>

#### returns nil when not found

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val found = array_find([10, 20, 30], fn(x): x > 100)
expect(found).to_be_nil()
```

</details>

### array_find_or

#### finds element or returns default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val found = array_find_or([10, 20, 30], fn(x): x > 100, -1)
expect(found).to_equal(-1)
```

</details>

#### finds element when present

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val found = array_find_or([10, 20, 30], fn(x): x > 15, -1)
expect(found).to_equal(20)
```

</details>

### array_enumerate

#### returns index-value pairs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pairs = array_enumerate(["a", "b", "c"])
expect(pairs.len()).to_equal(3)
```

</details>

### array_zip

#### zips two arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val zipped = array_zip([1, 2, 3], ["a", "b", "c"])
expect(zipped.len()).to_equal(3)
```

</details>

#### truncates to shorter length

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val zipped = array_zip([1, 2], ["a", "b", "c"])
expect(zipped.len()).to_equal(2)
```

</details>

### array_chunk

#### splits into chunks

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val chunks = array_chunk([1, 2, 3, 4, 5], 2)
expect(chunks.len()).to_equal(3)
```

</details>

### array_flat_map

#### maps and flattens

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_flat_map([1, 2, 3], fn(x): [x, x * 10])
expect(result.len()).to_equal(6)
expect(result[0]).to_equal(1)
expect(result[1]).to_equal(10)
```

</details>

### array_take_while

#### takes elements while predicate is true

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_take_while([1, 2, 3, 4, 5], fn(x): x < 4)
expect(result.len()).to_equal(3)
expect(result[0]).to_equal(1)
expect(result[2]).to_equal(3)
```

</details>

### array_drop_while

#### drops elements while predicate is true

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_drop_while([1, 2, 3, 4, 5], fn(x): x < 4)
expect(result.len()).to_equal(2)
expect(result[0]).to_equal(4)
```

</details>

### array_count

#### counts matching elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n = array_count([1, 2, 3, 4, 5], fn(x): x > 3)
expect(n).to_equal(2)
```

</details>

### array_any

#### returns true if any match

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_any([1, 2, 3], fn(x): x > 2)).to_equal(true)
```

</details>

#### returns false if none match

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_any([1, 2, 3], fn(x): x > 10)).to_equal(false)
```

</details>

### array_all

#### returns true if all match

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_all([2, 4, 6], fn(x): x > 0)).to_equal(true)
```

</details>

#### returns false if any fails

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_all([2, 4, 6], fn(x): x > 3)).to_equal(false)
```

</details>

### array_sum

#### sums numeric array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_sum([1, 2, 3, 4, 5])).to_equal(15)
```

</details>

#### returns 0 for empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_sum([])).to_equal(0)
```

</details>

### array_max

#### finds maximum element

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = array_max([3, 1, 4, 1, 5])
expect(m).to_equal(5)
```

</details>

#### returns nil for empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = array_max([])
expect(m).to_be_nil()
```

</details>

### array_min

#### finds minimum element

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = array_min([3, 1, 4, 1, 5])
expect(m).to_equal(1)
```

</details>

#### returns nil for empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = array_min([])
expect(m).to_be_nil()
```

</details>

### array_range

#### creates range array

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = array_range(0, 5)
expect(r.len()).to_equal(5)
expect(r[0]).to_equal(0)
expect(r[4]).to_equal(4)
```

</details>

#### handles empty range

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = array_range(5, 5)
expect(r.len()).to_equal(0)
```

</details>

### array_repeat

#### creates array of repeated values

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = array_repeat("x", 3)
expect(r.len()).to_equal(3)
expect(r[0]).to_equal("x")
expect(r[2]).to_equal("x")
```

</details>

### array_append_all

#### concatenates two arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_append_all([1, 2], [3, 4])
expect(result.len()).to_equal(4)
expect(result[2]).to_equal(3)
```

</details>

### array_partition

#### splits by predicate

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parts = array_partition([1, 2, 3, 4, 5], fn(x): x > 3)
expect(parts.len()).to_equal(2)
```

</details>

### array_concat

#### concatenates multiple arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_concat([[1, 2], [3, 4], [5]])
expect(result.len()).to_equal(5)
```

</details>

### array_flatten

#### flattens nested arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_flatten([[1, 2], [3, 4]])
expect(result.len()).to_equal(4)
```

</details>

### array_uniq

#### removes duplicates

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_uniq([1, 2, 2, 3, 3, 3])
expect(result.len()).to_equal(3)
```

</details>

### array_compact

#### removes nil values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_compact([1, nil, 2, nil, 3])
expect(result.len()).to_equal(3)
```

</details>

### array_reverse

#### reverses array

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_reverse([1, 2, 3])
expect(result[0]).to_equal(3)
expect(result[2]).to_equal(1)
```

</details>

#### handles empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_reverse([])
expect(result.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/array_search_transform_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- std.array
- array_position
- array_find
- array_find_or
- array_enumerate
- array_zip
- array_chunk
- array_flat_map
- array_take_while
- array_drop_while
- array_count
- array_any
- array_all
- array_sum
- array_max
- array_min
- array_range
- array_repeat
- array_append_all
- array_partition
- array_concat
- array_flatten
- array_uniq
- array_compact
- array_reverse

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 35 |
| Active scenarios | 35 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
