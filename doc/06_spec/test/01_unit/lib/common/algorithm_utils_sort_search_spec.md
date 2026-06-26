# Algorithm Utils Sort Search Specification

> <details>

<!-- sdn-diagram:id=algorithm_utils_sort_search_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=algorithm_utils_sort_search_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

algorithm_utils_sort_search_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=algorithm_utils_sort_search_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 39 | 39 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Algorithm Utils Sort Search Specification

## Scenarios

### std.algorithm_utils

### is_sorted

#### returns true for sorted list

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_sorted([1, 2, 3, 4, 5])).to_equal(true)
```

</details>

#### returns false for unsorted list

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_sorted([3, 1, 2])).to_equal(false)
```

</details>

#### handles empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_sorted([])).to_equal(true)
```

</details>

#### handles single element

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_sorted([42])).to_equal(true)
```

</details>

### lists_equal

#### returns true for equal lists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lists_equal([1, 2, 3], [1, 2, 3])).to_equal(true)
```

</details>

#### returns false for different lists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lists_equal([1, 2], [1, 3])).to_equal(false)
```

</details>

#### returns false for different lengths

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lists_equal([1, 2], [1, 2, 3])).to_equal(false)
```

</details>

### swap

#### swaps two elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = swap([10, 20, 30], 0, 2)
expect(result[0]).to_equal(30)
expect(result[2]).to_equal(10)
```

</details>

### sorting algorithms

#### bubble_sort sorts correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = bubble_sort([5, 3, 1, 4, 2])
expect(is_sorted(result)).to_equal(true)
```

</details>

#### selection_sort sorts correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = selection_sort([5, 3, 1, 4, 2])
expect(is_sorted(result)).to_equal(true)
```

</details>

#### insertion_sort sorts correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = insertion_sort([5, 3, 1, 4, 2])
expect(is_sorted(result)).to_equal(true)
```

</details>

#### quick_sort sorts correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = quick_sort([5, 3, 1, 4, 2])
expect(is_sorted(result)).to_equal(true)
```

</details>

#### merge_sort sorts correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = merge_sort([5, 3, 1, 4, 2])
expect(is_sorted(result)).to_equal(true)
```

</details>

#### handles empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bubble_sort([])).to_equal([])
```

</details>

#### handles single element

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(quick_sort([42])).to_equal([42])
```

</details>

### linear_search

#### finds element

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val idx = linear_search([10, 20, 30], 20)
expect(idx.?).to_equal(true)
```

</details>

#### returns nil for missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val idx = linear_search([10, 20, 30], 99)
expect(idx.?).to_equal(false)
```

</details>

### binary_search

#### finds element in sorted list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val idx = binary_search([1, 2, 3, 4, 5], 3)
expect(idx.?).to_equal(true)
```

</details>

#### returns nil for missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val idx = binary_search([1, 2, 3, 4, 5], 99)
expect(idx.?).to_equal(false)
```

</details>

### find_min

#### finds minimum

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = find_min([3, 1, 4, 1, 5])
expect(m.?).to_equal(true)
```

</details>

#### returns nil for empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = find_min([])
expect(m.?).to_equal(false)
```

</details>

### find_max

#### finds maximum

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = find_max([3, 1, 4, 1, 5])
expect(m.?).to_equal(true)
```

</details>

#### returns nil for empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = find_max([])
expect(m.?).to_equal(false)
```

</details>

### find_min_index

#### finds index of minimum

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val idx = find_min_index([3, 1, 4])
expect(idx.?).to_equal(true)
```

</details>

### find_max_index

#### finds index of maximum

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val idx = find_max_index([3, 1, 4])
expect(idx.?).to_equal(true)
```

</details>

### reverse_list

#### reverses a list

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(reverse_list([1, 2, 3])).to_equal([3, 2, 1])
```

</details>

#### handles empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(reverse_list([])).to_equal([])
```

</details>

### take

#### takes first n elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(take([1, 2, 3, 4, 5], 3)).to_equal([1, 2, 3])
```

</details>

#### takes all if n > length

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(take([1, 2], 5)).to_equal([1, 2])
```

</details>

### drop

#### drops first n elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(drop([1, 2, 3, 4, 5], 2)).to_equal([3, 4, 5])
```

</details>

### sum

#### sums elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sum([1, 2, 3, 4, 5])).to_equal(15)
```

</details>

#### returns 0 for empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sum([])).to_equal(0)
```

</details>

### count_occurrences

#### counts target occurrences

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(count_occurrences([1, 2, 2, 3, 2], 2)).to_equal(3)
expect(count_occurrences([1, 2, 3], 99)).to_equal(0)
```

</details>

### find_all_indices

#### finds all indices of target

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val indices = find_all_indices([1, 2, 3, 2, 1], 2)
expect(indices.len()).to_equal(2)
```

</details>

### remove_duplicates

#### removes duplicate elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = remove_duplicates([1, 2, 2, 3, 3, 3])
expect(result.len()).to_equal(3)
```

</details>

### is_prefix

#### checks if list is prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_prefix([1, 2], [1, 2, 3])).to_equal(true)
expect(is_prefix([1, 3], [1, 2, 3])).to_equal(false)
```

</details>

### is_suffix

#### checks if list is suffix

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_suffix([2, 3], [1, 2, 3])).to_equal(true)
expect(is_suffix([1, 3], [1, 2, 3])).to_equal(false)
```

</details>

### find_sublist

#### finds sublist in haystack

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val idx = find_sublist([1, 2, 3, 4, 5], [3, 4])
expect(idx.?).to_equal(true)
```

</details>

#### returns nil for missing sublist

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val idx = find_sublist([1, 2, 3], [4, 5])
expect(idx.?).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/algorithm_utils_sort_search_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- std.algorithm_utils
- is_sorted
- lists_equal
- swap
- sorting algorithms
- linear_search
- binary_search
- find_min
- find_max
- find_min_index
- find_max_index
- reverse_list
- take
- drop
- sum
- count_occurrences
- find_all_indices
- remove_duplicates
- is_prefix
- is_suffix
- find_sublist

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 39 |
| Active scenarios | 39 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
