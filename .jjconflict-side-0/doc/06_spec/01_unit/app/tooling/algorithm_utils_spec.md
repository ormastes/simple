# Algorithm Utils Specification

> 1. expect is sorted

<!-- sdn-diagram:id=algorithm_utils_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=algorithm_utils_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

algorithm_utils_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=algorithm_utils_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 33 | 33 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Algorithm Utils Specification

## Scenarios

### Algorithm Utilities

### Sorting

#### bubble sort works

1. expect is sorted


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val unsorted = [3, 1, 4, 1, 5, 9, 2, 6]
val sorted = bubble_sort(unsorted)
expect is_sorted(sorted)
expect sorted[0] == 1
```

</details>

#### selection sort works

1. expect is sorted


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val unsorted = [64, 25, 12, 22, 11]
val sorted = selection_sort(unsorted)
expect is_sorted(sorted)
expect sorted[0] == 11
```

</details>

#### insertion sort works

1. expect is sorted


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val unsorted = [12, 11, 13, 5, 6]
val sorted = insertion_sort(unsorted)
expect is_sorted(sorted)
expect sorted[0] == 5
```

</details>

#### quick sort works

1. expect is sorted


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val unsorted = [10, 7, 8, 9, 1, 5]
val sorted = quick_sort(unsorted)
expect is_sorted(sorted)
expect sorted[0] == 1
```

</details>

#### merge sort works

1. expect is sorted


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val unsorted = [38, 27, 43, 3, 9, 82, 10]
val sorted = merge_sort(unsorted)
expect is_sorted(sorted)
expect sorted[0] == 3
```

</details>

#### merge sorted lists

1. expect lists equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val left = [1, 3, 5]
val right = [2, 4, 6]
val merged = merge_sorted(left=left, right=right)
expect lists_equal(merged, [1, 2, 3, 4, 5, 6])
```

</details>

#### is_sorted detects sorted list

1. expect is sorted


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect is_sorted([1, 2, 3, 4, 5])
```

</details>

#### is_sorted detects unsorted list

1. expect not is sorted


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect not is_sorted([1, 3, 2, 4, 5])
```

</details>

#### is_sorted handles empty list

1. expect is sorted


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [i64] = []
expect is_sorted(empty)
```

</details>

### Searching

#### linear search finds element

1. nil: fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val list = [10, 20, 30, 40, 50]
val result = linear_search(list, 30)
match result:
    Some(idx): expect(idx).to_equal(2)
    nil: fail("linear_search did not find existing element 30")
```

</details>

#### linear search returns nil for missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val list = [10, 20, 30, 40, 50]
val result = linear_search(list, 25)
expect(result).to_be_nil()
```

</details>

#### binary search finds element

1. nil: fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val list = [1, 3, 5, 7, 9, 11, 13]
val result = binary_search(list, 7)
match result:
    Some(idx): expect(idx).to_equal(3)
    nil: fail("binary_search did not find existing element 7")
```

</details>

#### binary search returns nil for missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val list = [1, 3, 5, 7, 9, 11, 13]
val result = binary_search(list, 6)
expect(result).to_be_nil()
```

</details>

#### find_min returns minimum

1. nil: fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val list = [5, 2, 8, 1, 9]
val result = find_min(list)
match result:
    Some(v): expect(v).to_equal(1)
    nil: fail("find_min returned nil for a non-empty list")
```

</details>

#### find_max returns maximum

1. nil: fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val list = [5, 2, 8, 1, 9]
val result = find_max(list)
match result:
    Some(v): expect(v).to_equal(9)
    nil: fail("find_max returned nil for a non-empty list")
```

</details>

#### find_min_index returns correct index

1. nil: fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val list = [5, 2, 8, 1, 9]
val result = find_min_index(list)
match result:
    Some(i): expect(i).to_equal(3)
    nil: fail("find_min_index returned nil for a non-empty list")
```

</details>

#### find_max_index returns correct index

1. nil: fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val list = [5, 2, 8, 1, 9]
val result = find_max_index(list)
match result:
    Some(i): expect(i).to_equal(4)
    nil: fail("find_max_index returned nil for a non-empty list")
```

</details>

### List Manipulation

#### reverse_list works

1. expect lists equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val list = [1, 2, 3, 4, 5]
val reversed = reverse_list(list)
expect lists_equal(reversed, [5, 4, 3, 2, 1])
```

</details>

#### take gets first n elements

1. expect lists equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val list = [1, 2, 3, 4, 5]
val taken = take(list, 3)
expect lists_equal(taken, [1, 2, 3])
```

</details>

#### drop removes first n elements

1. expect lists equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val list = [1, 2, 3, 4, 5]
val dropped = drop(list, 2)
expect lists_equal(dropped, [3, 4, 5])
```

</details>

#### remove_duplicates works

1. expect lists equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val list = [1, 2, 2, 3, 3, 3, 4]
val unique = remove_duplicates(list)
expect lists_equal(unique, [1, 2, 3, 4])
```

</details>

### Statistics

#### sum calculates total

1. expect sum


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val list = [1, 2, 3, 4, 5]
expect sum(list) == 15
```

</details>

#### sum of empty list is 0

1. expect sum


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val list: [i64] = []
expect sum(list) == 0
```

</details>

### Comparisons

#### lists_equal returns true for equal lists

1. expect lists equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect lists_equal(a=[1, 2, 3], b=[1, 2, 3])
```

</details>

#### lists_equal returns false for different lists

1. expect not lists equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect not lists_equal(a=[1, 2, 3], b=[1, 2, 4])
```

</details>

#### is_prefix works

1. expect is prefix


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect is_prefix(prefix=[1, 2], list=[1, 2, 3, 4])
```

</details>

#### is_suffix works

1. expect is suffix


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect is_suffix(suffix=[3, 4], list=[1, 2, 3, 4])
```

</details>

#### count_occurrences works

1. expect count occurrences


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val list = [1, 2, 2, 3, 2, 4]
expect count_occurrences(list, 2) == 3
```

</details>

#### find_all_indices works

1. expect lists equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val list = [1, 2, 2, 3, 2, 4]
val indices = find_all_indices(list, 2)
expect lists_equal(a=indices, b=[1, 2, 4])
```

</details>

### Edge Cases

#### sort empty list

1. expect sorted len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [i64] = []
val sorted = quick_sort(empty)
expect sorted.len() == 0
```

</details>

#### sort single element

1. expect lists equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val single = [42]
val sorted = merge_sort(single)
expect lists_equal(a=sorted, b=[42])
```

</details>

#### take more than length

1. expect lists equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val list = [1, 2, 3]
val taken = take(list, 10)
expect lists_equal(a=taken, b=[1, 2, 3])
```

</details>

#### drop more than length

1. expect dropped len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val list = [1, 2, 3]
val dropped = drop(list, 10)
expect dropped.len() == 0
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/tooling/algorithm_utils_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Algorithm Utilities
- Sorting
- Searching
- List Manipulation
- Statistics
- Comparisons
- Edge Cases

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 33 |
| Active scenarios | 33 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
