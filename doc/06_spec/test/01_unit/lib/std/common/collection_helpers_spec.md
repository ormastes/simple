# Collection Helpers Specification

> Tests for Phase 1 collection helper functions: sort_by_key, min_by_key, max_by_key, flat_map, compact_map, insert_at, remove_at, arr_pop, arr_shift, reject, none, one, find_last, find_last_index, at, arr_clone, each_slice, chunk, pairwise, sum_by, product, tally, compress, reduce_right, values_at, fill, replace_range, zip_longest, slice_when, chunk_while, top_n, bottom_n, each_cons, arr_compare, dedup_by.

<!-- sdn-diagram:id=collection_helpers_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=collection_helpers_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

collection_helpers_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=collection_helpers_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 70 | 70 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Collection Helpers Specification

Tests for Phase 1 collection helper functions: sort_by_key, min_by_key, max_by_key, flat_map, compact_map, insert_at, remove_at, arr_pop, arr_shift, reject, none, one, find_last, find_last_index, at, arr_clone, each_slice, chunk, pairwise, sum_by, product, tally, compress, reduce_right, values_at, fill, replace_range, zip_longest, slice_when, chunk_while, top_n, bottom_n, each_cons, arr_compare, dedup_by.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #COLL-P1 |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Implemented |
| Requirements | doc/02_requirements/feature/stdlib_helpers.md |
| Source | `test/01_unit/lib/std/common/collection_helpers_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for Phase 1 collection helper functions: sort_by_key, min_by_key,
max_by_key, flat_map, compact_map, insert_at, remove_at, arr_pop,
arr_shift, reject, none, one, find_last, find_last_index, at, arr_clone,
each_slice, chunk, pairwise, sum_by, product, tally, compress,
reduce_right, values_at, fill, replace_range, zip_longest, slice_when,
chunk_while, top_n, bottom_n, each_cons, arr_compare, dedup_by.

## Scenarios

### sort_by_key

#### sorts strings by length

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sort_by_key(["banana", "apple", "fig"], &:len)
expect(result[0]).to_equal("fig")
expect(result[1]).to_equal("apple")
expect(result[2]).to_equal("banana")
```

</details>

#### returns empty for empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sort_by_key([], &:len)
expect(result.len()).to_equal(0)
```

</details>

#### returns single-element array unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sort_by_key(["only"], &:len)
expect(result[0]).to_equal("only")
```

</details>

### min_by_key

#### finds shortest string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = min_by_key(["banana", "apple", "fig"], &:len)
expect(result).to_equal("fig")
```

</details>

#### returns nil for empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = min_by_key([], &:len)
expect(result).to_be_nil()
```

</details>

### max_by_key

#### finds longest string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = max_by_key(["banana", "apple", "fig"], &:len)
expect(result).to_equal("banana")
```

</details>

#### returns nil for empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = max_by_key([], &:len)
expect(result).to_be_nil()
```

</details>

### flat_map

#### maps and flattens one level

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = flat_map([1, 2, 3], [_1, _1 * 10])
expect(result.len()).to_equal(6)
expect(result[0]).to_equal(1)
expect(result[1]).to_equal(10)
expect(result[2]).to_equal(2)
expect(result[3]).to_equal(20)
```

</details>

#### handles empty arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = flat_map([], [_1])
expect(result.len()).to_equal(0)
```

</details>

### compact_map

#### maps and removes nils

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = compact_map([1, 2, 3, 4], if _1 % 2 == 0: _1 * 10 else: nil)
expect(result.len()).to_equal(2)
expect(result[0]).to_equal(20)
expect(result[1]).to_equal(40)
```

</details>

#### returns empty when all nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = compact_map([1, 3, 5], if _1 % 2 == 0: _1 else: nil)
expect(result.len()).to_equal(0)
```

</details>

### insert_at

#### inserts at middle

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = insert_at([1, 2, 3], 1, 99)
expect(result.len()).to_equal(4)
expect(result[0]).to_equal(1)
expect(result[1]).to_equal(99)
expect(result[2]).to_equal(2)
```

</details>

#### inserts at beginning

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = insert_at([1, 2], 0, 99)
expect(result[0]).to_equal(99)
expect(result.len()).to_equal(3)
```

</details>

#### inserts at end

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = insert_at([1, 2], 2, 99)
expect(result[2]).to_equal(99)
expect(result.len()).to_equal(3)
```

</details>

### remove_at

#### removes at middle

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = remove_at([10, 20, 30], 1)
expect(result.len()).to_equal(2)
expect(result[0]).to_equal(10)
expect(result[1]).to_equal(30)
```

</details>

#### returns original for out of bounds

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = remove_at([1, 2, 3], 5)
expect(result.len()).to_equal(3)
```

</details>

### arr_pop

#### removes and returns last element

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (rest, last) = arr_pop([1, 2, 3])
expect(last).to_equal(3)
expect(rest.len()).to_equal(2)
expect(rest[0]).to_equal(1)
expect(rest[1]).to_equal(2)
```

</details>

#### returns nil for empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (rest, last) = arr_pop([])
expect(last).to_be_nil()
expect(rest.len()).to_equal(0)
```

</details>

### arr_shift

#### removes and returns first element

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (rest, first) = arr_shift([1, 2, 3])
expect(first).to_equal(1)
expect(rest.len()).to_equal(2)
expect(rest[0]).to_equal(2)
```

</details>

#### returns nil for empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (rest, first) = arr_shift([])
expect(first).to_be_nil()
```

</details>

### reject

#### keeps elements not matching predicate

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = reject([1, 2, 3, 4, 5], _1 % 2 == 0)
expect(result.len()).to_equal(3)
expect(result[0]).to_equal(1)
expect(result[1]).to_equal(3)
expect(result[2]).to_equal(5)
```

</details>

#### keeps all when nothing matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = reject([1, 3, 5], _1 % 2 == 0)
expect(result.len()).to_equal(3)
```

</details>

### none

#### returns true when no match

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(none([1, 3, 5], _1 % 2 == 0)).to_equal(true)
```

</details>

#### returns false when any match

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(none([1, 2, 3], _1 % 2 == 0)).to_equal(false)
```

</details>

#### returns true for empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(none([], \_: true)).to_equal(true)
```

</details>

### one

#### returns true for exactly one match

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(one([1, 2, 3], _1 == 2)).to_equal(true)
```

</details>

#### returns false for multiple matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(one([1, 2, 2], _1 == 2)).to_equal(false)
```

</details>

#### returns false for no matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(one([1, 3, 5], _1 == 2)).to_equal(false)
```

</details>

### find_last

#### finds last matching element

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(find_last([1, 2, 3, 4], _1 % 2 == 0)).to_equal(4)
```

</details>

#### returns nil when none match

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(find_last([1, 3, 5], _1 % 2 == 0)).to_be_nil()
```

</details>

### find_last_index

#### finds index of last match

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(find_last_index([1, 2, 3, 2], _1 == 2)).to_equal(3)
```

</details>

#### returns nil when none match

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(find_last_index([1, 3, 5], _1 == 2)).to_be_nil()
```

</details>

### at

#### gets element by positive index

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(at([10, 20, 30], 0)).to_equal(10)
expect(at([10, 20, 30], 2)).to_equal(30)
```

</details>

#### supports negative index

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(at([10, 20, 30], -1)).to_equal(30)
expect(at([10, 20, 30], -2)).to_equal(20)
expect(at([10, 20, 30], -3)).to_equal(10)
```

</details>

#### returns nil for out of bounds

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(at([10, 20, 30], 5)).to_be_nil()
expect(at([10, 20, 30], -4)).to_be_nil()
```

</details>

### arr_clone

#### creates shallow copy

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = [1, 2, 3]
val copy = arr_clone(original)
expect(copy.len()).to_equal(3)
expect(copy[0]).to_equal(1)
expect(copy[1]).to_equal(2)
expect(copy[2]).to_equal(3)
```

</details>

#### returns empty for empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val copy = arr_clone([])
expect(copy.len()).to_equal(0)
```

</details>

### chunk

#### splits into chunks

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = chunk([1, 2, 3, 4, 5], 2)
expect(result.len()).to_equal(3)
expect(result[0].len()).to_equal(2)
expect(result[0][0]).to_equal(1)
expect(result[0][1]).to_equal(2)
expect(result[2].len()).to_equal(1)
expect(result[2][0]).to_equal(5)
```

</details>

#### returns empty for empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = chunk([], 2)
expect(result.len()).to_equal(0)
```

</details>

#### returns empty for zero chunk size

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = chunk([1, 2, 3], 0)
expect(result.len()).to_equal(0)
```

</details>

### pairwise

#### returns consecutive pairs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pairwise([1, 2, 3, 4])
expect(result.len()).to_equal(3)
```

</details>

#### returns empty for single element

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pairwise([1])
expect(result.len()).to_equal(0)
```

</details>

#### returns empty for empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = pairwise([])
expect(result.len()).to_equal(0)
```

</details>

### sum_by

#### sums extracted values

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sum_by(["hi", "hello", "hey"], &:len)).to_equal(10)
```

</details>

#### returns 0 for empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sum_by([], &:len)).to_equal(0)
```

</details>

### product

#### multiplies all elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(product([1, 2, 3, 4])).to_equal(24)
```

</details>

#### returns 1 for empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(product([])).to_equal(1)
```

</details>

#### handles single element

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(product([5])).to_equal(5)
```

</details>

### tally

#### counts element frequencies

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = tally(["a", "b", "a", "c", "b", "a"])
expect(result.len()).to_equal(3)
```

</details>

#### returns empty for empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = tally([])
expect(result.len()).to_equal(0)
```

</details>

### compress

#### filters by boolean selectors

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = compress(["a", "b", "c", "d"], [true, false, true, false])
expect(result.len()).to_equal(2)
expect(result[0]).to_equal("a")
expect(result[1]).to_equal("c")
```

</details>

#### handles shorter selector array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = compress(["a", "b", "c"], [true])
expect(result.len()).to_equal(1)
```

</details>

### values_at

#### gets elements at specified indices

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = values_at(["a", "b", "c", "d"], [0, 2, 3])
expect(result.len()).to_equal(3)
expect(result[0]).to_equal("a")
expect(result[1]).to_equal("c")
expect(result[2]).to_equal("d")
```

</details>

### fill

#### fills array with value

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = fill([1, 2, 3], 0)
expect(result.len()).to_equal(3)
expect(result[0]).to_equal(0)
expect(result[1]).to_equal(0)
expect(result[2]).to_equal(0)
```

</details>

### reduce_right

#### folds from right to left

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = reduce_right(["a", "b", "c"], "", \acc, x: acc + x)
expect(result).to_equal("cba")
```

</details>

#### returns init for empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = reduce_right([], 0, \acc, x: acc + x)
expect(result).to_equal(0)
```

</details>

### replace_range

#### replaces range of elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = replace_range([1, 2, 3, 4, 5], 1, 3, [20, 30, 40])
expect(result.len()).to_equal(6)
expect(result[0]).to_equal(1)
expect(result[1]).to_equal(20)
expect(result[2]).to_equal(30)
expect(result[3]).to_equal(40)
expect(result[4]).to_equal(4)
```

</details>

### zip_longest

#### zips with fill for unequal lengths

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = zip_longest([1, 2, 3], ["a", "b"], 0, "z")
expect(result.len()).to_equal(3)
```

</details>

### slice_when

#### splits when predicate true between elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = slice_when([1, 2, 4, 5, 7], \a, b: b - a > 1)
expect(result.len()).to_equal(3)
expect(result[0].len()).to_equal(2)
expect(result[1].len()).to_equal(2)
expect(result[2].len()).to_equal(1)
```

</details>

#### returns empty for empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = slice_when([], \a, b: true)
expect(result.len()).to_equal(0)
```

</details>

### chunk_while

#### chunks while predicate true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = chunk_while([1, 2, 4, 5, 7], \a, b: b - a <= 1)
expect(result.len()).to_equal(3)
```

</details>

### top_n

#### returns n largest

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = top_n([3, 1, 4, 1, 5, 9], 3)
expect(result.len()).to_equal(3)
expect(result[0]).to_equal(9)
expect(result[1]).to_equal(5)
expect(result[2]).to_equal(4)
```

</details>

#### returns empty for n=0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = top_n([1, 2], 0)
expect(result.len()).to_equal(0)
```

</details>

### bottom_n

#### returns n smallest

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = bottom_n([3, 1, 4, 1, 5, 9], 3)
expect(result.len()).to_equal(3)
expect(result[0]).to_equal(1)
expect(result[1]).to_equal(1)
expect(result[2]).to_equal(3)
```

</details>

### arr_compare

#### compares less

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(arr_compare([1, 2, 3], [1, 2, 4])).to_equal(-1)
```

</details>

#### compares equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(arr_compare([1, 2, 3], [1, 2, 3])).to_equal(0)
```

</details>

#### compares greater

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(arr_compare([1, 2, 4], [1, 2, 3])).to_equal(1)
```

</details>

#### shorter is less

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(arr_compare([1, 2], [1, 2, 3])).to_equal(-1)
```

</details>

### dedup_by

#### removes consecutive duplicates

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = dedup_by([1, 1, 2, 2, 3, 1], \a, b: a == b)
expect(result.len()).to_equal(4)
expect(result[0]).to_equal(1)
expect(result[1]).to_equal(2)
expect(result[2]).to_equal(3)
expect(result[3]).to_equal(1)
```

</details>

#### returns empty for empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = dedup_by([], \a, b: a == b)
expect(result.len()).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 70 |
| Active scenarios | 70 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/stdlib_helpers.md](doc/02_requirements/feature/stdlib_helpers.md)


</details>
