# Set Api Parity Specification

> 1. var set = Set from array

<!-- sdn-diagram:id=set_api_parity_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=set_api_parity_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

set_api_parity_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=set_api_parity_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Set Api Parity Specification

## Scenarios

### nogc_async_mut pure Set API parity

#### supports construction, membership, and enumeration aliases

1. var set = Set from array
   - Expected: set.size() equals `3`
   - Expected: set contains `1`
   - Expected: set.has(2) is true
   - Expected: set contains `3`
   - Expected: set.to_list().len() equals `3`
2. var array set = Set from array
   - Expected: array_set.to_array().len() equals `3`
3. var added = Set from array
   - Expected: added.add(3) is true
   - Expected: added contains `3`
   - Expected: added.remove(2) is true
   - Expected: not_contains_2 is true
   - Expected: added.to_array().len() equals `2`
   - Expected: cloned contains `1`
   - Expected: cloned contains `3`
4. added clear
   - Expected: added.size() equals `0`
   - Expected: added.to_array().len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var set = Set.from_array([1, 2, 1, 3])
expect(set.size()).to_equal(3)
expect(set.contains(1)).to_equal(true)
expect(set.has(2)).to_equal(true)
expect(set.contains(3)).to_equal(true)
expect(set.to_list().len()).to_equal(3)

var array_set = Set.from_array([1, 2, 1, 3])
expect(array_set.to_array().len()).to_equal(3)

var added = Set.from_array([1, 2])
expect(added.add(3)).to_equal(true)
expect(added.contains(3)).to_equal(true)

expect(added.remove(2)).to_equal(true)
val not_contains_2 = not added.contains(2)
expect(not_contains_2).to_equal(true)
expect(added.to_array().len()).to_equal(2)

val cloned = added.clone()
expect(cloned.contains(1)).to_equal(true)
expect(cloned.contains(3)).to_equal(true)

added.clear()
expect(added.size()).to_equal(0)
expect(added.to_array().len()).to_equal(0)
```

</details>

#### supports subset and superset aliases

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val subset = Set.from_array([2])
val superset = Set.from_array([1, 2, 3])
expect(subset.is_subset(superset)).to_equal(true)
expect(superset.is_superset(subset)).to_equal(true)
val super_not_subset = not superset.is_subset(subset)
expect(super_not_subset).to_equal(true)
val sub_not_superset = not subset.is_superset(superset)
expect(sub_not_superset).to_equal(true)
```

</details>

#### supports binary set operation aliases

<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val left = Set.from_array([1, 2, 3])
val right = Set.from_array([2, 4])

val union_set = left.union(right)
expect(union_set.contains(1)).to_equal(true)
expect(union_set.contains(4)).to_equal(true)

val intersection_set = left.intersection(right)
expect(intersection_set.contains(2)).to_equal(true)
val intersect_not_1 = not intersection_set.contains(1)
expect(intersect_not_1).to_equal(true)

val difference_set = left.difference(right)
expect(difference_set.contains(1)).to_equal(true)
val diff_not_2 = not difference_set.contains(2)
expect(diff_not_2).to_equal(true)

val symmetric_set = left.symmetric_difference(right)
expect(symmetric_set.contains(1)).to_equal(true)
expect(symmetric_set.contains(4)).to_equal(true)
val sym_not_2 = not symmetric_set.contains(2)
expect(sym_not_2).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/src/set_api_parity_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_mut pure Set API parity

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
