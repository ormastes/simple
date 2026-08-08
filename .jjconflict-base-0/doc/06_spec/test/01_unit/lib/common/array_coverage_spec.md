# Array Coverage Specification

> Comprehensive branch coverage tests for the array and array_advanced modules. Tests every exported function with inputs that exercise all if/elif/else branches, empty arrays, single elements, boundary conditions, and typical usage.

<!-- sdn-diagram:id=array_coverage_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=array_coverage_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

array_coverage_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=array_coverage_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 228 | 228 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Array Coverage Specification

Comprehensive branch coverage tests for the array and array_advanced modules. Tests every exported function with inputs that exercise all if/elif/else branches, empty arrays, single elements, boundary conditions, and typical usage.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LIB-ARRAY-COV |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/lib/common/array_coverage_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Comprehensive branch coverage tests for the array and array_advanced modules.
Tests every exported function with inputs that exercise all if/elif/else branches,
empty arrays, single elements, boundary conditions, and typical usage.

## Scenarios

### array coverage

### array_position
_Branch coverage for array_position: predicate match vs no match, empty array._

#### returns index when predicate matches first element

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_position([5, 10, 15], fn(x): x == 5)).to_equal(0)
```

</details>

#### returns index when predicate matches middle element

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_position([5, 10, 15], fn(x): x == 10)).to_equal(1)
```

</details>

#### returns index when predicate matches last element

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_position([5, 10, 15], fn(x): x == 15)).to_equal(2)
```

</details>

#### returns -1 when no element matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_position([5, 10, 15], fn(x): x == 99)).to_equal(-1)
```

</details>

#### returns -1 for empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_position([], fn(x): x == 1)).to_equal(-1)
```

</details>

### array_find
_Branch coverage for array_find: match found vs nil return._

#### finds first element matching predicate

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_find([10, 20, 30], fn(x): x > 15)).to_equal(20)
```

</details>

#### returns nil when no element matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_find([10, 20, 30], fn(x): x > 100)).to_be_nil()
```

</details>

#### returns nil for empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_find([], fn(x): x == 1)).to_be_nil()
```

</details>

#### finds first match not subsequent ones

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_find([1, 2, 3, 4], fn(x): x > 1)).to_equal(2)
```

</details>

### array_find_or
_Branch coverage: element found vs default returned._

#### returns element when found

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_find_or([10, 20, 30], fn(x): x > 15, -1)).to_equal(20)
```

</details>

#### returns default when not found

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_find_or([10, 20, 30], fn(x): x > 100, -1)).to_equal(-1)
```

</details>

#### returns default for empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_find_or([], fn(x): x == 1, 42)).to_equal(42)
```

</details>

### array_enumerate
_Covers loop body and empty array._

#### returns index-value pairs

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pairs = array_enumerate(["a", "b", "c"])
expect(pairs.len()).to_equal(3)
val p0 = pairs[0]
expect(p0[0]).to_equal(0)
expect(p0[1]).to_equal("a")
val p2 = pairs[2]
expect(p2[0]).to_equal(2)
expect(p2[1]).to_equal("c")
```

</details>

#### returns empty for empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_enumerate([]).len()).to_equal(0)
```

</details>

### array_zip
_Branch coverage: arr2.len() < arr1.len() and arr2.len() >= arr1.len()._

#### zips equal length arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val zipped = array_zip([1, 2], ["a", "b"])
expect(zipped.len()).to_equal(2)
val z0 = zipped[0]
expect(z0[0]).to_equal(1)
expect(z0[1]).to_equal("a")
```

</details>

#### truncates to shorter when arr2 is shorter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val zipped = array_zip([1, 2, 3], ["a", "b"])
expect(zipped.len()).to_equal(2)
```

</details>

#### truncates to shorter when arr1 is shorter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val zipped = array_zip([1], ["a", "b", "c"])
expect(zipped.len()).to_equal(1)
```

</details>

#### returns empty when either array is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_zip([], [1, 2]).len()).to_equal(0)
expect(array_zip([1, 2], []).len()).to_equal(0)
```

</details>

### array_chunk
_Branch coverage: end_idx > arr.len() and end_idx <= arr.len()._

#### splits evenly

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val chunks = array_chunk([1, 2, 3, 4], 2)
expect(chunks.len()).to_equal(2)
expect(chunks[0]).to_equal([1, 2])
expect(chunks[1]).to_equal([3, 4])
```

</details>

#### last chunk smaller when uneven

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val chunks = array_chunk([1, 2, 3, 4, 5], 2)
expect(chunks.len()).to_equal(3)
expect(chunks[2]).to_equal([5])
```

</details>

#### single element chunks

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val chunks = array_chunk([1, 2, 3], 1)
expect(chunks.len()).to_equal(3)
```

</details>

#### chunk size larger than array

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val chunks = array_chunk([1, 2], 5)
expect(chunks.len()).to_equal(1)
expect(chunks[0]).to_equal([1, 2])
```

</details>

#### returns empty for empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_chunk([], 3).len()).to_equal(0)
```

</details>

### array_flat_map
_Covers mapper producing multi-element arrays and empty arrays._

#### maps and flattens

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_flat_map([1, 2, 3], fn(x): [x, x * 10])
expect(result).to_equal([1, 10, 2, 20, 3, 30])
```

</details>

#### handles mapper returning empty arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_flat_map([1, 2, 3], fn(x): [])
expect(result.len()).to_equal(0)
```

</details>

#### handles empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_flat_map([], fn(x): [x])
expect(result.len()).to_equal(0)
```

</details>

### array_take_while
_Branch coverage: predicate false immediately, mid-way, and never false._

#### takes elements while predicate is true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_take_while([1, 2, 3, 4, 5], fn(x): x < 4)
expect(result).to_equal([1, 2, 3])
```

</details>

#### returns empty when first element fails predicate

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_take_while([10, 20, 30], fn(x): x < 5)
expect(result.len()).to_equal(0)
```

</details>

#### returns all when predicate always true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_take_while([1, 2, 3], fn(x): x < 100)
expect(result).to_equal([1, 2, 3])
```

</details>

#### returns empty for empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_take_while([], fn(x): x < 100)
expect(result.len()).to_equal(0)
```

</details>

### array_drop_while
_Branch coverage: predicate false immediately, mid-way, and always true._

#### drops elements while predicate is true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_drop_while([1, 2, 3, 4, 5], fn(x): x < 3)
expect(result).to_equal([3, 4, 5])
```

</details>

#### drops nothing when first element fails predicate

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_drop_while([10, 20, 30], fn(x): x < 5)
expect(result).to_equal([10, 20, 30])
```

</details>

#### drops all when predicate always true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_drop_while([1, 2, 3], fn(x): x < 100)
expect(result).to_equal([])
```

</details>

#### returns empty for empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_drop_while([], fn(x): x < 100)
expect(result).to_equal([])
```

</details>

### array_sort_by

#### returns empty array as-is

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_sort_by([], fn(a, b): a - b)
expect(result).to_equal([])
```

</details>

#### returns single element array as-is

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_sort_by([42], fn(a, b): a - b)
expect(result).to_equal([42])
```

</details>

#### sorts small array (insertion sort path, len<10)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_sort_by([3, 1, 4, 1, 5], fn(a, b): a - b)
expect(result).to_equal([1, 1, 3, 4, 5])
```

</details>

#### sorts small array descending

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_sort_by([3, 1, 4, 1, 5], fn(a, b): b - a)
expect(result).to_equal([5, 4, 3, 1, 1])
```

</details>

#### sorts already sorted small array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_sort_by([1, 2, 3, 4], fn(a, b): a - b)
expect(result).to_equal([1, 2, 3, 4])
```

</details>

#### sorts reverse-sorted small array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_sort_by([5, 4, 3, 2, 1], fn(a, b): a - b)
expect(result).to_equal([1, 2, 3, 4, 5])
```

</details>

#### sorts large array (quicksort path, len>=10)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = [9, 3, 7, 1, 8, 2, 6, 4, 10, 5]
val result = array_sort_by(input, fn(a, b): a - b)
expect(result).to_equal([1, 2, 3, 4, 5, 6, 7, 8, 9, 10])
```

</details>

#### sorts large array with duplicates (equal branch)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = [5, 3, 5, 1, 3, 5, 1, 3, 5, 1]
val result = array_sort_by(input, fn(a, b): a - b)
expect(result).to_equal([1, 1, 1, 3, 3, 3, 5, 5, 5, 5])
```

</details>

#### sorts large array descending

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
val result = array_sort_by(input, fn(a, b): b - a)
expect(result).to_equal([10, 9, 8, 7, 6, 5, 4, 3, 2, 1])
```

</details>

#### handles two element array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_sort_by([5, 2], fn(a, b): a - b)
expect(result).to_equal([2, 5])
```

</details>

### array_group_by
_Branch coverage: contains_key true vs false._

#### groups elements by key function

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val groups = array_group_by([1, 2, 3, 4, 5, 6], fn(x): x % 2)
expect(groups[0]).to_contain(2)
expect(groups[1]).to_contain(1)
```

</details>

#### handles single group

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val groups = array_group_by([2, 4, 6], fn(x): "even")
expect(groups["even"].len()).to_equal(3)
```

</details>

#### handles empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val groups = array_group_by([], fn(x): x)
expect(groups.len()).to_equal(0)
```

</details>

### array_count
_Branch coverage: predicate true vs false._

#### counts matching elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_count([1, 2, 3, 4, 5], fn(x): x > 3)).to_equal(2)
```

</details>

#### returns 0 when nothing matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_count([1, 2, 3], fn(x): x > 10)).to_equal(0)
```

</details>

#### counts all when all match

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_count([1, 2, 3], fn(x): x > 0)).to_equal(3)
```

</details>

#### returns 0 for empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_count([], fn(x): x > 0)).to_equal(0)
```

</details>

### array_any
_Branch coverage: early return true vs fall-through false._

#### returns true when match exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_any([1, 2, 3], fn(x): x == 2)).to_equal(true)
```

</details>

#### returns true when last element matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_any([1, 2, 3], fn(x): x == 3)).to_equal(true)
```

</details>

#### returns false when no match

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_any([1, 2, 3], fn(x): x > 10)).to_equal(false)
```

</details>

#### returns false for empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_any([], fn(x): x == 1)).to_equal(false)
```

</details>

### array_all
_Branch coverage: early return false vs fall-through true._

#### returns true when all match

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_all([2, 4, 6], fn(x): x > 0)).to_equal(true)
```

</details>

#### returns false when one fails

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_all([2, 4, 6], fn(x): x > 3)).to_equal(false)
```

</details>

#### returns false when first fails

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_all([0, 4, 6], fn(x): x > 1)).to_equal(false)
```

</details>

#### returns true for empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_all([], fn(x): x > 0)).to_equal(true)
```

</details>

### array_sum
_Delegates to sum_i64._

#### sums elements

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

#### handles single element

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_sum([42])).to_equal(42)
```

</details>

#### handles negative numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_sum([-1, -2, 3])).to_equal(0)
```

</details>

### array_max
_Branch coverage: empty array (nil), single element, max at start/middle/end._

#### returns nil for empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_max([])).to_be_nil()
```

</details>

#### returns single element

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_max([7])).to_equal(7)
```

</details>

#### finds max at end

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_max([1, 2, 3])).to_equal(3)
```

</details>

#### finds max at start

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_max([5, 2, 3])).to_equal(5)
```

</details>

#### finds max in middle

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_max([1, 9, 3])).to_equal(9)
```

</details>

#### handles all equal elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_max([4, 4, 4])).to_equal(4)
```

</details>

### array_min
_Branch coverage: empty array (nil), single element, min at various positions._

#### returns nil for empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_min([])).to_be_nil()
```

</details>

#### returns single element

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_min([7])).to_equal(7)
```

</details>

#### finds min at start

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_min([1, 2, 3])).to_equal(1)
```

</details>

#### finds min at end

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_min([5, 2, 1])).to_equal(1)
```

</details>

#### finds min in middle

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_min([9, 1, 3])).to_equal(1)
```

</details>

#### handles all equal elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_min([4, 4, 4])).to_equal(4)
```

</details>

### array_range
_Covers normal range, empty range (start == end), start > end._

#### creates range 0 to 5

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = array_range(0, 5)
expect(r).to_equal([0, 1, 2, 3, 4])
```

</details>

#### handles empty range when start equals end

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_range(5, 5)).to_equal([])
```

</details>

#### handles empty range when start > end

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_range(10, 5)).to_equal([])
```

</details>

#### creates single element range

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_range(3, 4)).to_equal([3])
```

</details>

### array_repeat
_Covers zero count, single count, multiple count._

#### repeats item n times

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_repeat("x", 3)).to_equal(["x", "x", "x"])
```

</details>

#### returns empty for count 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_repeat("x", 0)).to_equal([])
```

</details>

#### handles single repetition

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_repeat(42, 1)).to_equal([42])
```

</details>

### array_append_all

#### concatenates two arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_append_all([1, 2], [3, 4])).to_equal([1, 2, 3, 4])
```

</details>

#### handles first array empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_append_all([], [1, 2])).to_equal([1, 2])
```

</details>

#### handles second array empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_append_all([1, 2], [])).to_equal([1, 2])
```

</details>

#### handles both empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_append_all([], [])).to_equal([])
```

</details>

### array_partition
_Branch coverage: predicate true vs false for each element._

#### partitions by predicate

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parts = array_partition([1, 2, 3, 4, 5], fn(x): x > 3)
expect(parts[0]).to_equal([4, 5])
expect(parts[1]).to_equal([1, 2, 3])
```

</details>

#### all match

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parts = array_partition([1, 2, 3], fn(x): x > 0)
expect(parts[0]).to_equal([1, 2, 3])
expect(parts[1]).to_equal([])
```

</details>

#### none match

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parts = array_partition([1, 2, 3], fn(x): x > 10)
expect(parts[0]).to_equal([])
expect(parts[1]).to_equal([1, 2, 3])
```

</details>

#### empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parts = array_partition([], fn(x): x > 0)
expect(parts[0]).to_equal([])
expect(parts[1]).to_equal([])
```

</details>

### array_concat

#### concatenates multiple arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_concat([[1, 2], [3], [4, 5]])).to_equal([1, 2, 3, 4, 5])
```

</details>

#### handles empty sub-arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_concat([[1], [], [2]])).to_equal([1, 2])
```

</details>

#### handles empty outer array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_concat([])).to_equal([])
```

</details>

### array_flatten

#### flattens nested arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_flatten([[1, 2], [3, 4]])).to_equal([1, 2, 3, 4])
```

</details>

#### handles empty sub-arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_flatten([[], [1], []])).to_equal([1])
```

</details>

#### handles empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_flatten([])).to_equal([])
```

</details>

### array_uniq
_Branch coverage: seen.contains_key true vs false._

#### removes duplicates

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_uniq([1, 2, 2, 3, 3, 3]).len()).to_equal(3)
```

</details>

#### keeps order of first occurrences

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_uniq([3, 1, 2, 1, 3])
expect(result[0]).to_equal(3)
expect(result[1]).to_equal(1)
expect(result[2]).to_equal(2)
expect(result.len()).to_equal(3)
```

</details>

#### handles already unique array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_uniq([1, 2, 3])).to_equal([1, 2, 3])
```

</details>

#### handles empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_uniq([])).to_equal([])
```

</details>

#### handles single element

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_uniq([5])).to_equal([5])
```

</details>

### array_compact
_Branch coverage: item != nil true vs false._

#### removes nil values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_compact([1, nil, 2, nil, 3])
expect(result).to_equal([1, 2, 3])
```

</details>

#### returns same when no nils

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_compact([1, 2, 3])).to_equal([1, 2, 3])
```

</details>

#### returns empty when all nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_compact([nil, nil, nil])).to_equal([])
```

</details>

#### handles empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_compact([])).to_equal([])
```

</details>

### array_reverse

#### reverses array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_reverse([1, 2, 3])).to_equal([3, 2, 1])
```

</details>

#### handles empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_reverse([])).to_equal([])
```

</details>

#### handles single element

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_reverse([1])).to_equal([1])
```

</details>

### array_take
_Branch coverage: n < arr.len() vs n >= arr.len()._

#### takes first n elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_take([1, 2, 3, 4, 5], 3)).to_equal([1, 2, 3])
```

</details>

#### returns all when n > length

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_take([1, 2], 5)).to_equal([1, 2])
```

</details>

#### returns empty when n is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_take([1, 2, 3], 0)).to_equal([])
```

</details>

#### handles empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_take([], 3)).to_equal([])
```

</details>

### array_drop
_Branch coverage: n >= arr.len() vs n < arr.len()._

#### drops first n elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_drop([1, 2, 3, 4, 5], 2)).to_equal([3, 4, 5])
```

</details>

#### returns empty when n >= length

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_drop([1, 2, 3], 5)).to_equal([])
```

</details>

#### returns empty when n equals length

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_drop([1, 2, 3], 3)).to_equal([])
```

</details>

#### returns all when n is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_drop([1, 2, 3], 0)).to_equal([1, 2, 3])
```

</details>

#### handles empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_drop([], 0)).to_equal([])
```

</details>

### array_windows
_Branch coverage: size > arr.len(), size <= 0, normal sliding._

#### creates sliding windows

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wins = array_windows([1, 2, 3, 4], 2)
expect(wins.len()).to_equal(3)
expect(wins[0]).to_equal([1, 2])
expect(wins[1]).to_equal([2, 3])
expect(wins[2]).to_equal([3, 4])
```

</details>

#### returns empty when size > length

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_windows([1, 2], 5)).to_equal([])
```

</details>

#### returns empty when size is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_windows([1, 2, 3], 0)).to_equal([])
```

</details>

#### window size equals array length

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wins = array_windows([1, 2, 3], 3)
expect(wins.len()).to_equal(1)
expect(wins[0]).to_equal([1, 2, 3])
```

</details>

#### handles empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_windows([], 2)).to_equal([])
```

</details>

### array_interleave
_Branch coverage: i < arr1.len() and i < arr2.len() at different lengths._

#### interleaves equal length arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_interleave([1, 3, 5], [2, 4, 6])).to_equal([1, 2, 3, 4, 5, 6])
```

</details>

#### interleaves when arr1 longer

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_interleave([1, 3, 5], [2, 4])
expect(result).to_equal([1, 2, 3, 4, 5])
```

</details>

#### interleaves when arr2 longer

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_interleave([1, 3], [2, 4, 6])
expect(result).to_equal([1, 2, 3, 4, 6])
```

</details>

#### handles empty arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_interleave([], [])).to_equal([])
```

</details>

#### handles one empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_interleave([1, 2], [])).to_equal([1, 2])
expect(array_interleave([], [1, 2])).to_equal([1, 2])
```

</details>

### array_intersperse
_Branch coverage: arr.len() <= 1 vs arr.len() > 1._

#### inserts separator between elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_intersperse([1, 2, 3], 0)).to_equal([1, 0, 2, 0, 3])
```

</details>

#### returns same for single element

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_intersperse([1], 0)).to_equal([1])
```

</details>

#### returns empty for empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_intersperse([], 0)).to_equal([])
```

</details>

#### handles two elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_intersperse([1, 2], 0)).to_equal([1, 0, 2])
```

</details>

### array_rotate_left
_Branch coverage: empty array, normal rotation, full rotation._

#### rotates left by n positions

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_rotate_left([1, 2, 3, 4, 5], 2)).to_equal([3, 4, 5, 1, 2])
```

</details>

#### rotates left by 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_rotate_left([1, 2, 3, 4], 1)).to_equal([2, 3, 4, 1])
```

</details>

#### returns empty for empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_rotate_left([], 3)).to_equal([])
```

</details>

#### full rotation returns same

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_rotate_left([1, 2, 3], 3)).to_equal([1, 2, 3])
```

</details>

#### rotation larger than length wraps

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_rotate_left([1, 2, 3], 4)).to_equal([2, 3, 1])
```

</details>

### array_rotate_right
_Branch coverage: empty array, normal rotation._

#### rotates right by n positions

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_rotate_right([1, 2, 3, 4, 5], 2)).to_equal([4, 5, 1, 2, 3])
```

</details>

#### rotates right by 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_rotate_right([1, 2, 3, 4], 1)).to_equal([4, 1, 2, 3])
```

</details>

#### returns empty for empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_rotate_right([], 3)).to_equal([])
```

</details>

#### full rotation returns same

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_rotate_right([1, 2, 3], 3)).to_equal([1, 2, 3])
```

</details>

### array_dedup
_Branch coverage: empty, consecutive matches vs non-matches._

#### removes consecutive duplicates

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_dedup([1, 1, 2, 2, 3, 3])).to_equal([1, 2, 3])
```

</details>

#### preserves non-consecutive duplicates

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_dedup([1, 2, 1, 2])).to_equal([1, 2, 1, 2])
```

</details>

#### returns empty for empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_dedup([])).to_equal([])
```

</details>

#### handles single element

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_dedup([5])).to_equal([5])
```

</details>

#### handles all same elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_dedup([3, 3, 3, 3])).to_equal([3])
```

</details>

### array_dedup_all
_Branch coverage: found duplicate vs not found._

#### removes all duplicates keeping first

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_dedup_all([1, 2, 1, 3, 2])
expect(result).to_equal([1, 2, 3])
```

</details>

#### handles already unique

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_dedup_all([1, 2, 3])).to_equal([1, 2, 3])
```

</details>

#### handles empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_dedup_all([])).to_equal([])
```

</details>

#### handles single element

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_dedup_all([5])).to_equal([5])
```

</details>

#### handles all same

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_dedup_all([3, 3, 3])).to_equal([3])
```

</details>

### array_is_sorted
_Branch coverage: len<=1, sorted, not sorted (arr[i] > arr[i+1])._

#### returns true for sorted array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_is_sorted([1, 2, 3, 4])).to_equal(true)
```

</details>

#### returns false for unsorted array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_is_sorted([1, 3, 2])).to_equal(false)
```

</details>

#### returns true for empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_is_sorted([])).to_equal(true)
```

</details>

#### returns true for single element

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_is_sorted([1])).to_equal(true)
```

</details>

#### returns true for equal elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_is_sorted([2, 2, 2])).to_equal(true)
```

</details>

#### detects unsorted at end

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_is_sorted([1, 2, 3, 1])).to_equal(false)
```

</details>

### array_equals
_Branch coverage: different lengths, element mismatch, full match._

#### returns true for equal arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_equals([1, 2, 3], [1, 2, 3])).to_equal(true)
```

</details>

#### returns false for different lengths

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_equals([1, 2], [1, 2, 3])).to_equal(false)
```

</details>

#### returns false for element mismatch

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_equals([1, 2, 3], [1, 9, 3])).to_equal(false)
```

</details>

#### returns true for empty arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_equals([], [])).to_equal(true)
```

</details>

#### returns false when first is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_equals([], [1])).to_equal(false)
```

</details>

### array_group_consecutive
_Branch coverage: empty, arr[i]==arr[i-1] vs not equal._

#### groups consecutive equal elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_group_consecutive([1, 1, 2, 2, 2, 3, 1])
expect(result.len()).to_equal(4)
expect(result[0]).to_equal([1, 1])
expect(result[1]).to_equal([2, 2, 2])
expect(result[2]).to_equal([3])
expect(result[3]).to_equal([1])
```

</details>

#### returns empty for empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_group_consecutive([])).to_equal([])
```

</details>

#### handles single element

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_group_consecutive([5])
expect(result.len()).to_equal(1)
expect(result[0]).to_equal([5])
```

</details>

#### handles all same elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_group_consecutive([2, 2, 2])
expect(result.len()).to_equal(1)
expect(result[0]).to_equal([2, 2, 2])
```

</details>

#### handles all different elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_group_consecutive([1, 2, 3])
expect(result.len()).to_equal(3)
```

</details>

### array_transpose
_Branch coverage: empty matrix vs non-empty._

<details>
<summary>Advanced: transposes 2x3 matrix</summary>

#### transposes 2x3 matrix

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_transpose([[1, 2, 3], [4, 5, 6]])
expect(result.len()).to_equal(3)
expect(result[0]).to_equal([1, 4])
expect(result[1]).to_equal([2, 5])
expect(result[2]).to_equal([3, 6])
```

</details>


</details>

<details>
<summary>Advanced: transposes 1x1 matrix</summary>

#### transposes 1x1 matrix

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_transpose([[42]])
expect(result.len()).to_equal(1)
expect(result[0]).to_equal([42])
```

</details>


</details>

<details>
<summary>Advanced: returns empty for empty matrix</summary>

#### returns empty for empty matrix

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_transpose([])).to_equal([])
```

</details>


</details>

<details>
<summary>Advanced: returns empty for ragged matrix</summary>

#### returns empty for ragged matrix

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_transpose([[1, 2], [3]])).to_equal([])
```

</details>


</details>

<details>
<summary>Advanced: transposes square matrix</summary>

#### transposes square matrix

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_transpose([[1, 2], [3, 4]])
expect(result[0]).to_equal([1, 3])
expect(result[1]).to_equal([2, 4])
```

</details>


</details>

### array_cartesian_product
_Covers nested loop iteration and empty inputs._

#### produces all pairs

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_cartesian_product([1, 2], [3, 4])
expect(result.len()).to_equal(4)
val r0 = result[0]
expect(r0[0]).to_equal(1)
expect(r0[1]).to_equal(3)
val r3 = result[3]
expect(r3[0]).to_equal(2)
expect(r3[1]).to_equal(4)
```

</details>

#### returns empty when first array is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_cartesian_product([], [1, 2])).to_equal([])
```

</details>

#### returns empty when second array is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_cartesian_product([1, 2], [])).to_equal([])
```

</details>

#### handles single element arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_cartesian_product([1], [2])
expect(result.len()).to_equal(1)
```

</details>

### array_frequencies
_Branch coverage: found existing element vs new element._

#### counts element frequencies

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_frequencies([1, 2, 2, 3, 3, 3])
expect(result.len()).to_equal(3)
val f0 = result[0]
expect(f0[0]).to_equal(1)
expect(f0[1]).to_equal(1)
val f1 = result[1]
expect(f1[0]).to_equal(2)
expect(f1[1]).to_equal(2)
val f2 = result[2]
expect(f2[0]).to_equal(3)
expect(f2[1]).to_equal(3)
```

</details>

#### handles all unique elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_frequencies([1, 2, 3])
expect(result.len()).to_equal(3)
```

</details>

#### handles all same elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_frequencies([5, 5, 5])
expect(result.len()).to_equal(1)
val f0 = result[0]
expect(f0[0]).to_equal(5)
expect(f0[1]).to_equal(3)
```

</details>

#### handles empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_frequencies([]).len()).to_equal(0)
```

</details>

### array_mode
_Branch coverage: empty (nil), single mode, tie (first encountered)._

#### returns most frequent element

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_mode([1, 2, 2, 3, 3, 3])).to_equal(3)
```

</details>

#### returns nil for empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_mode([])).to_be_nil()
```

</details>

#### returns first encountered on tie

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_mode([1, 2, 1, 2])).to_equal(1)
```

</details>

#### handles single element

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_mode([42])).to_equal(42)
```

</details>

### array_median
_Delegates to median_i64 from math.spl._

#### finds median of odd-length sorted array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_median([1, 2, 3, 4, 5])
expect(result).to_equal(3)
```

</details>

#### finds median of even-length sorted array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_median([1, 2, 3, 4])
expect(result).to_equal(2)
```

</details>

#### handles single element

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_median([7])).to_equal(7)
```

</details>

### array_intersect
_Branch coverage: in_arr2 true/false, already_added true/false._

#### finds common elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_intersect([1, 2, 3], [2, 3, 4])
expect(result).to_equal([2, 3])
```

</details>

#### returns empty when no common elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_intersect([1, 2], [3, 4])).to_equal([])
```

</details>

#### handles duplicates in first array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_intersect([1, 1, 2, 2], [1, 2])
expect(result).to_equal([1, 2])
```

</details>

#### handles empty first array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_intersect([], [1, 2])).to_equal([])
```

</details>

#### handles empty second array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_intersect([1, 2], [])).to_equal([])
```

</details>

### array_difference
_Branch coverage: in_arr2 true/false, already_added true/false._

#### finds elements in first but not second

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_difference([1, 2, 3, 4], [2, 4])).to_equal([1, 3])
```

</details>

#### returns all when no overlap

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_difference([1, 2], [3, 4])).to_equal([1, 2])
```

</details>

#### returns empty when all overlap

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_difference([1, 2], [1, 2, 3])).to_equal([])
```

</details>

#### handles duplicates in first array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_difference([1, 1, 2, 2], [2])
expect(result).to_equal([1])
```

</details>

#### handles empty arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_difference([], [1])).to_equal([])
expect(array_difference([1, 2], [])).to_equal([1, 2])
```

</details>

### array_union
_Branch coverage: already_added true/false in both loops._

#### combines unique elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_union([1, 2, 3], [3, 4, 5])).to_equal([1, 2, 3, 4, 5])
```

</details>

#### handles no overlap

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_union([1, 2], [3, 4])).to_equal([1, 2, 3, 4])
```

</details>

#### handles full overlap

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_union([1, 2], [1, 2])).to_equal([1, 2])
```

</details>

#### handles duplicates within arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_union([1, 1, 2], [2, 3, 3])
expect(result).to_equal([1, 2, 3])
```

</details>

#### handles empty arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_union([], [1, 2])).to_equal([1, 2])
expect(array_union([1, 2], [])).to_equal([1, 2])
expect(array_union([], [])).to_equal([])
```

</details>

### array_is_subset
_Branch coverage: found true/false, early return false._

#### returns true when subset

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_is_subset([1, 2], [1, 2, 3, 4])).to_equal(true)
```

</details>

#### returns false when not subset

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_is_subset([1, 5], [1, 2, 3])).to_equal(false)
```

</details>

#### returns true for empty first array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_is_subset([], [1, 2])).to_equal(true)
```

</details>

#### returns true when arrays are equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_is_subset([1, 2, 3], [1, 2, 3])).to_equal(true)
```

</details>

#### returns true for empty subset of empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_is_subset([], [])).to_equal(true)
```

</details>

### array_starts_with
_Branch coverage: prefix longer than arr, element mismatch, full match._

#### returns true when starts with prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_starts_with([1, 2, 3, 4], [1, 2])).to_equal(true)
```

</details>

#### returns false when does not start with prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_starts_with([1, 2, 3, 4], [2, 3])).to_equal(false)
```

</details>

#### returns false when prefix longer than array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_starts_with([1, 2], [1, 2, 3])).to_equal(false)
```

</details>

#### returns true for empty prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_starts_with([1, 2, 3], [])).to_equal(true)
```

</details>

#### returns true when arrays are equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_starts_with([1, 2, 3], [1, 2, 3])).to_equal(true)
```

</details>

### array_ends_with
_Branch coverage: suffix longer than arr, element mismatch, full match._

#### returns true when ends with suffix

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_ends_with([1, 2, 3, 4], [3, 4])).to_equal(true)
```

</details>

#### returns false when does not end with suffix

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_ends_with([1, 2, 3, 4], [2, 3])).to_equal(false)
```

</details>

#### returns false when suffix longer than array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_ends_with([1, 2], [1, 2, 3])).to_equal(false)
```

</details>

#### returns true for empty suffix

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_ends_with([1, 2, 3], [])).to_equal(true)
```

</details>

#### returns true when arrays are equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_ends_with([1, 2, 3], [1, 2, 3])).to_equal(true)
```

</details>

### array_index_of_subarray
_Branch coverage: empty subarray, subarray > arr, match, no match, mismatch mid-compare._

#### finds subarray at beginning

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_index_of_subarray([1, 2, 3, 4], [1, 2])).to_equal(0)
```

</details>

#### finds subarray in middle

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_index_of_subarray([1, 2, 3, 4], [2, 3])).to_equal(1)
```

</details>

#### finds subarray at end

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_index_of_subarray([1, 2, 3, 4], [3, 4])).to_equal(2)
```

</details>

#### returns -1 when not found

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_index_of_subarray([1, 2, 3, 4], [5, 6])).to_equal(-1)
```

</details>

#### returns -1 for empty subarray

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_index_of_subarray([1, 2, 3], [])).to_equal(-1)
```

</details>

#### returns -1 when subarray longer than array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_index_of_subarray([1, 2], [1, 2, 3])).to_equal(-1)
```

</details>

#### finds first occurrence

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_index_of_subarray([1, 2, 3, 2, 3], [2, 3])).to_equal(1)
```

</details>

#### handles partial match then fail

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_index_of_subarray([1, 2, 4, 2, 3], [2, 3])).to_equal(3)
```

</details>

### array_contains_subarray
_Delegates to array_index_of_subarray >= 0._

#### returns true when subarray present

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_contains_subarray([1, 2, 3, 4], [2, 3])).to_equal(true)
```

</details>

#### returns false when subarray absent

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_contains_subarray([1, 2, 3, 4], [5, 6])).to_equal(false)
```

</details>

#### returns false for empty subarray

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_contains_subarray([1, 2, 3], [])).to_equal(false)
```

</details>

#### returns true when arrays are equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(array_contains_subarray([1, 2, 3], [1, 2, 3])).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 228 |
| Active scenarios | 228 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
