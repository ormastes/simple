# List Utils Specification

> 1. expect array equals

<!-- sdn-diagram:id=list_utils_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=list_utils_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

list_utils_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=list_utils_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# List Utils Specification

## Scenarios

### List Utilities

### Reverse

#### reverses list

1. expect array equals


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect array_equals(array_reverse([1, 2, 3, 4]), [4, 3, 2, 1])
```

</details>

#### handles single element

1. expect array equals


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect array_equals(array_reverse([1]), [1])
```

</details>

#### handles empty list

1. expect array reverse


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [i64] = []
expect array_reverse(empty).len() == 0
```

</details>

### Chunk

#### chunks list into parts

1. expect chunks list len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val chunks_list = array_chunk([1, 2, 3, 4, 5], 2)
expect chunks_list.len() == 3
```

</details>

#### handles exact fit

1. expect chunks list len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val chunks_list = array_chunk([1, 2, 3, 4], 2)
expect chunks_list.len() == 2
```

</details>

#### handles size larger than list

1. expect chunks list len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val chunks_list = array_chunk([1, 2], 5)
expect chunks_list.len() == 1
```

</details>

### Interleave

#### interleaves equal length lists

1. expect array equals


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_interleave([1, 2, 3], [4, 5, 6])
expect array_equals(result, [1, 4, 2, 5, 3, 6])
```

</details>

#### handles different lengths

1. expect result len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_interleave([1, 2], [3, 4, 5, 6])
expect result.len() == 6
```

</details>

### Rotation

#### rotates left

1. expect array equals


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect array_equals(array_rotate_left([1, 2, 3, 4, 5], 2), [3, 4, 5, 1, 2])
```

</details>

#### rotates left by zero

1. expect array equals


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect array_equals(array_rotate_left([1, 2, 3], 0), [1, 2, 3])
```

</details>

#### rotates right

1. expect array equals


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect array_equals(array_rotate_right([1, 2, 3, 4, 5], 2), [4, 5, 1, 2, 3])
```

</details>

### Deduplication

#### removes consecutive duplicates

1. expect array equals


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect array_equals(array_dedup([1, 1, 2, 2, 3, 3]), [1, 2, 3])
```

</details>

#### keeps non-consecutive duplicates

1. expect array equals


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect array_equals(array_dedup([1, 2, 1, 2]), [1, 2, 1, 2])
```

</details>

#### dedup_all removes all duplicates

1. expect array equals


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect array_equals(array_dedup_all([1, 2, 1, 3, 2]), [1, 2, 3])
```

</details>

### Flatten

#### flattens nested lists

1. expect array equals


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nested = [[1, 2], [3, 4], [5]]
expect array_equals(array_flatten(nested), [1, 2, 3, 4, 5])
```

</details>

#### handles empty nested list

1. expect array flatten


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [[i64]] = []
expect array_flatten(empty).len() == 0
```

</details>

### Windows

#### creates sliding windows

1. expect wins len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wins = array_windows([1, 2, 3, 4], 2)
expect wins.len() == 3
```

</details>

#### handles size too large

1. expect wins len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wins = array_windows([1, 2], 5)
expect wins.len() == 0
```

</details>

### Intersperse

#### inserts separator between elements

1. expect array equals


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect array_equals(array_intersperse([1, 2, 3], 0), [1, 0, 2, 0, 3])
```

</details>

#### handles single element

1. expect array equals


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect array_equals(array_intersperse([1], 0), [1])
```

</details>

### Slicing

#### take gets first n elements

1. expect array equals


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect array_equals(array_take([1, 2, 3, 4, 5], 3), [1, 2, 3])
```

</details>

#### take handles oversized n

1. expect array equals


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect array_equals(array_take([1, 2], 5), [1, 2])
```

</details>

#### drop removes first n elements

1. expect array equals


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect array_equals(array_drop([1, 2, 3, 4, 5], 2), [3, 4, 5])
```

</details>

#### drop handles oversized n

1. expect dropped len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dropped = array_drop([1, 2], 5)
expect dropped.len() == 0
```

</details>

### Comparison

#### list_equals returns true for equal

1. expect array equals


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect array_equals([1, 2, 3], [1, 2, 3])
```

</details>

#### list_equals returns false for different

1. expect not array equals
2. expect not array equals


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect not array_equals([1, 2], [1, 2, 3])
expect not array_equals([1, 2, 3], [1, 3, 2])
```

</details>

### Sorting Check

#### is_sorted detects sorted

1. expect array is sorted


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect array_is_sorted([1, 2, 3, 4])
```

</details>

#### is_sorted detects unsorted

1. expect not array is sorted


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect not array_is_sorted([1, 3, 2, 4])
```

</details>

#### is_sorted handles empty

1. expect array is sorted


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [i64] = []
expect array_is_sorted(empty)
```

</details>

#### is_sorted handles single element

1. expect array is sorted


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect array_is_sorted([1])
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/tooling/list_utils_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- List Utilities
- Reverse
- Chunk
- Interleave
- Rotation
- Deduplication
- Flatten
- Windows
- Intersperse
- Slicing
- Comparison
- Sorting Check

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
