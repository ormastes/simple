# Set Specification

> <details>

<!-- sdn-diagram:id=set_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=set_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

set_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=set_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 51 | 51 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Set Specification

## Scenarios

### Set<T>

#### Construction

#### creates empty set with new()

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = {}
expect(s.len()).to_equal(0)
```

</details>

#### creates empty set with capacity

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Dict doesn't have capacity, but empty dict is equivalent
var s = {}
expect(s.len()).to_equal(0)
```

</details>

#### Basic operations

#### inserts element into set

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = {}
val was_new = not s.has("Alice")
s["Alice"] = true
expect(was_new).to_be(true)
expect(s.len()).to_equal(1)
```

</details>

#### insert returns false for duplicate

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = {}
s["Alice"] = true
val was_new = not s.has("Alice")
s["Alice"] = true
expect(was_new).to_be(false)
expect(s.len()).to_equal(1)
```

</details>

#### contains finds existing element

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = {}
s["Alice"] = true
expect(set_contains(s, "Alice")).to_be(true)
```

</details>

#### contains returns false for missing element

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = {}
expect(set_contains(s, "Alice")).to_be(false)
```

</details>

#### removes existing element

1. s remove
   - Expected: s.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = {}
s["Alice"] = true
val existed = s.has("Alice")
s.remove("Alice")
expect(existed).to_be(true)
expect(s.len()).to_equal(0)
```

</details>

#### remove returns false for missing element

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = {}
val existed = s.has("Alice")
expect(existed).to_be(false)
```

</details>

#### clear removes all elements

1. s clear
   - Expected: s.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = {}
s["Alice"] = true
s["Bob"] = true
s["Charlie"] = true
s.clear()
expect(s.len()).to_equal(0)
```

</details>

#### Multiple elements

#### handles multiple unique elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = {}
s["Alice"] = true
s["Bob"] = true
s["Charlie"] = true
expect(s.len()).to_equal(3)
expect(set_contains(s, "Alice")).to_be(true)
expect(set_contains(s, "Bob")).to_be(true)
expect(set_contains(s, "Charlie")).to_be(true)
```

</details>

#### deduplicates elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = {}
s["Alice"] = true
s["Bob"] = true
s["Alice"] = true
s["Bob"] = true
expect(s.len()).to_equal(2)
```

</details>

#### Conversion

#### converts to list

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = {}
s["Alice"] = true
s["Bob"] = true
s["Charlie"] = true
val list = s.keys()
expect(list.len()).to_equal(3)
```

</details>

#### to_list contains all elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = {}
s["Alice"] = true
s["Bob"] = true
val list = s.keys()
expect(list).to_contain("Alice")
expect(list).to_contain("Bob")
```

</details>

#### Iteration

#### for_each executes action for all elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = {}
s["Alice"] = true
s["Bob"] = true
s["Charlie"] = true
var count = 0
for k in s.keys():
    count = count + 1
expect(count).to_equal(3)
```

</details>

#### Set operations - union

#### union combines two sets

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s1 = {}
s1["Alice"] = true
s1["Bob"] = true
var s2 = {}
s2["Charlie"] = true
s2["David"] = true
val result = set_union(s1, s2)
expect(result.len()).to_equal(4)
expect(set_contains(result, "Alice")).to_be(true)
expect(set_contains(result, "Bob")).to_be(true)
expect(set_contains(result, "Charlie")).to_be(true)
expect(set_contains(result, "David")).to_be(true)
```

</details>

#### union handles overlapping sets

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s1 = {}
s1["Alice"] = true
s1["Bob"] = true
s1["Charlie"] = true
var s2 = {}
s2["Bob"] = true
s2["Charlie"] = true
s2["David"] = true
val result = set_union(s1, s2)
expect(result.len()).to_equal(4)
```

</details>

#### union doesn't modify original sets

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s1 = {}
s1["Alice"] = true
var s2 = {}
s2["Bob"] = true
val result = set_union(s1, s2)
expect(s1.len()).to_equal(1)
expect(s2.len()).to_equal(1)
```

</details>

#### Set operations - intersection

#### intersection finds common elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s1 = {}
s1["Alice"] = true
s1["Bob"] = true
s1["Charlie"] = true
var s2 = {}
s2["Bob"] = true
s2["Charlie"] = true
s2["David"] = true
val result = set_intersection(s1, s2)
expect(result.len()).to_equal(2)
expect(set_contains(result, "Bob")).to_be(true)
expect(set_contains(result, "Charlie")).to_be(true)
```

</details>

#### intersection returns empty for disjoint sets

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s1 = {}
s1["Alice"] = true
s1["Bob"] = true
var s2 = {}
s2["Charlie"] = true
s2["David"] = true
val result = set_intersection(s1, s2)
expect(result.len()).to_equal(0)
```

</details>

#### intersection doesn't modify original sets

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s1 = {}
s1["Alice"] = true
s1["Bob"] = true
var s2 = {}
s2["Bob"] = true
val result = set_intersection(s1, s2)
expect(s1.len()).to_equal(2)
expect(s2.len()).to_equal(1)
```

</details>

#### Set operations - difference

#### difference finds elements in first but not second

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s1 = {}
s1["Alice"] = true
s1["Bob"] = true
s1["Charlie"] = true
var s2 = {}
s2["Bob"] = true
s2["Charlie"] = true
s2["David"] = true
val result = set_difference(s1, s2)
expect(result.len()).to_equal(1)
expect(set_contains(result, "Alice")).to_be(true)
expect(set_contains(result, "Bob")).to_be(false)
expect(set_contains(result, "Charlie")).to_be(false)
```

</details>

#### difference returns empty when second is superset

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s1 = {}
s1["Alice"] = true
s1["Bob"] = true
var s2 = {}
s2["Alice"] = true
s2["Bob"] = true
s2["Charlie"] = true
val result = set_difference(s1, s2)
expect(result.len()).to_equal(0)
```

</details>

#### Set operations - symmetric difference

#### symmetric_difference finds elements in either but not both

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s1 = {}
s1["Alice"] = true
s1["Bob"] = true
s1["Charlie"] = true
var s2 = {}
s2["Bob"] = true
s2["Charlie"] = true
s2["David"] = true
val result = set_symmetric_difference(s1, s2)
expect(result.len()).to_equal(2)
expect(set_contains(result, "Alice")).to_be(true)
expect(set_contains(result, "David")).to_be(true)
expect(set_contains(result, "Bob")).to_be(false)
expect(set_contains(result, "Charlie")).to_be(false)
```

</details>

#### symmetric_difference returns union for disjoint sets

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s1 = {}
s1["Alice"] = true
s1["Bob"] = true
var s2 = {}
s2["Charlie"] = true
s2["David"] = true
val result = set_symmetric_difference(s1, s2)
expect(result.len()).to_equal(4)
```

</details>

#### Set predicates - subset

#### is_subset returns true when all elements in other

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s1 = {}
s1["Alice"] = true
s1["Bob"] = true
var s2 = {}
s2["Alice"] = true
s2["Bob"] = true
s2["Charlie"] = true
expect(set_is_subset(s1, s2)).to_be(true)
```

</details>

#### is_subset returns true for equal sets

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s1 = {}
s1["Alice"] = true
s1["Bob"] = true
var s2 = {}
s2["Alice"] = true
s2["Bob"] = true
expect(set_is_subset(s1, s2)).to_be(true)
```

</details>

#### is_subset returns false when element not in other

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s1 = {}
s1["Alice"] = true
s1["Bob"] = true
s1["Charlie"] = true
var s2 = {}
s2["Alice"] = true
s2["Bob"] = true
expect(set_is_subset(s1, s2)).to_be(false)
```

</details>

#### Set predicates - superset

#### is_superset returns true when contains all elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s1 = {}
s1["Alice"] = true
s1["Bob"] = true
s1["Charlie"] = true
var s2 = {}
s2["Alice"] = true
s2["Bob"] = true
expect(set_is_superset(s1, s2)).to_be(true)
```

</details>

#### is_superset returns false when missing element

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s1 = {}
s1["Alice"] = true
s1["Bob"] = true
var s2 = {}
s2["Alice"] = true
s2["Bob"] = true
s2["Charlie"] = true
expect(set_is_superset(s1, s2)).to_be(false)
```

</details>

#### Set predicates - disjoint

#### is_disjoint returns true for no overlap

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s1 = {}
s1["Alice"] = true
s1["Bob"] = true
var s2 = {}
s2["Charlie"] = true
s2["David"] = true
expect(set_is_disjoint(s1, s2)).to_be(true)
```

</details>

#### is_disjoint returns false when sets overlap

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s1 = {}
s1["Alice"] = true
s1["Bob"] = true
var s2 = {}
s2["Bob"] = true
s2["Charlie"] = true
expect(set_is_disjoint(s1, s2)).to_be(false)
```

</details>

#### Functional operations - filter

#### filter keeps matching elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = {}
s["1"] = true
s["2"] = true
s["3"] = true
s["4"] = true
s["5"] = true
val result = set_filter(s, int(_1) % 2 == 0)
expect(result.len()).to_equal(2)
expect(set_contains(result, "2")).to_be(true)
expect(set_contains(result, "4")).to_be(true)
```

</details>

#### filter returns empty when no matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = {}
s["Alice"] = true
s["Bob"] = true
val result = set_filter(s, _1 == "Charlie")
expect(result.len()).to_equal(0)
```

</details>

#### Functional operations - map

#### map transforms all elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = {}
s["1"] = true
s["2"] = true
s["3"] = true
val result = set_map(s, int(_1) * 2)
expect(result.len()).to_equal(3)
expect(set_contains(result, 2)).to_be(true)
expect(set_contains(result, 4)).to_be(true)
expect(set_contains(result, 6)).to_be(true)
```

</details>

#### map deduplicates transformed values

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = {}
s["1"] = true
s["2"] = true
s["3"] = true
val result = set_map(s, \_: 42)
expect(result.len()).to_equal(1)
expect(set_contains(result, 42)).to_be(true)
```

</details>

#### Functional operations - any

#### any returns true when element matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = {}
s["1"] = true
s["2"] = true
s["3"] = true
val result = set_any(s, int(_1) > 2)
expect(result).to_be(true)
```

</details>

#### any returns false when no element matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = {}
s["1"] = true
s["2"] = true
s["3"] = true
val result = set_any(s, int(_1) > 10)
expect(result).to_be(false)
```

</details>

#### any returns false for empty set

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = {}
val result = set_any(s, \_: true)
expect(result).to_be(false)
```

</details>

#### Functional operations - all

#### all returns true when all elements match

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = {}
s["1"] = true
s["2"] = true
s["3"] = true
val result = set_all(s, int(_1) > 0)
expect(result).to_be(true)
```

</details>

#### all returns false when one element doesn't match

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = {}
s["1"] = true
s["2"] = true
s["3"] = true
val result = set_all(s, int(_1) > 1)
expect(result).to_be(false)
```

</details>

#### all returns true for empty set

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = {}
val result = set_all(s, \_: false)
expect(result).to_be(true)
```

</details>

#### Utility operations

#### clone creates independent copy

1. var s2 = set clone
   - Expected: s1.len() equals `2`
   - Expected: s2.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s1 = {}
s1["Alice"] = true
s1["Bob"] = true
var s2 = set_clone(s1)
s2["Charlie"] = true
expect(s1.len()).to_equal(2)
expect(s2.len()).to_equal(3)
expect(set_contains(s1, "Charlie")).to_be(false)
```

</details>

#### extend adds all items from list

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = {}
s["Alice"] = true
val more = ["Bob", "Charlie", "David"]
for item in more:
    s[item] = true
expect(s.len()).to_equal(4)
expect(set_contains(s, "Bob")).to_be(true)
expect(set_contains(s, "Charlie")).to_be(true)
expect(set_contains(s, "David")).to_be(true)
```

</details>

#### extend deduplicates items from list

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = {}
s["Alice"] = true
val more = ["Alice", "Bob", "Alice", "Charlie", "Bob"]
for item in more:
    s[item] = true
expect(s.len()).to_equal(3)
```

</details>

#### Helper functions

#### set_from_list creates set from list

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = set_from_list(["Alice", "Bob", "Charlie", "Alice", "Bob"])
expect(s.len()).to_equal(3)
expect(set_contains(s, "Alice")).to_be(true)
expect(set_contains(s, "Bob")).to_be(true)
expect(set_contains(s, "Charlie")).to_be(true)
```

</details>

#### intersect_all finds common elements in multiple sets

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s1 = {}
s1["Alice"] = true
s1["Bob"] = true
s1["Charlie"] = true
var s2 = {}
s2["Bob"] = true
s2["Charlie"] = true
s2["David"] = true
var s3 = {}
s3["Charlie"] = true
s3["David"] = true
s3["Eve"] = true
val result = intersect_all([s1, s2, s3])
expect(result.len()).to_equal(1)
expect(set_contains(result, "Charlie")).to_be(true)
```

</details>

#### intersect_all returns empty for empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = intersect_all([])
expect(result.len()).to_equal(0)
```

</details>

#### union_all combines all sets

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s1 = {}
s1["Alice"] = true
s1["Bob"] = true
var s2 = {}
s2["Bob"] = true
s2["Charlie"] = true
var s3 = {}
s3["Charlie"] = true
s3["David"] = true
val result = union_all([s1, s2, s3])
expect(result.len()).to_equal(4)
expect(set_contains(result, "Alice")).to_be(true)
expect(set_contains(result, "Bob")).to_be(true)
expect(set_contains(result, "Charlie")).to_be(true)
expect(set_contains(result, "David")).to_be(true)
```

</details>

#### Edge cases

#### handles many elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = {}
for i in 0..100:
    s["item{i}"] = true
expect(s.len()).to_equal(100)
```

<details>
<summary>Rendered scenario source</summary>

> var s = {}<br>
> for i in 0..100:<br>
>     s["ite$i$"] = true<br>
> expect(s.len()).to_equal(100)

</details>

</details>

#### handles element removal during iteration

1. s remove
   - Expected: s.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = {}
s["Alice"] = true
s["Bob"] = true
s["Charlie"] = true
val items = s.keys()
for item in items:
    s.remove(item)
expect(s.len()).to_equal(0)
```

</details>

#### handles empty set operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s1 = {}
var s2 = {}
val union_result = set_union(s1, s2)
expect(union_result.len()).to_equal(0)
val intersect_result = set_intersection(s1, s2)
expect(intersect_result.len()).to_equal(0)
expect(set_is_subset(s1, s2)).to_be(true)
expect(set_is_disjoint(s1, s2)).to_be(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/shared/collections/set_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Set<T>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 51 |
| Active scenarios | 51 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
