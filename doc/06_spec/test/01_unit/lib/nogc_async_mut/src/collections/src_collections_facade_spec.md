# Src Collections Facade Specification

> 1. var map = HashMap new

<!-- sdn-diagram:id=src_collections_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=src_collections_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

src_collections_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=src_collections_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Src Collections Facade Specification

## Scenarios

### nogc_async_mut src collections facade

#### re-exports hash map, hash set, and btree map behavior

1. var map = HashMap new
   - Expected: map.is_empty() is true
   - Expected: map.insert_if_absent("a", "one") is true
   - Expected: map.insert_if_absent("a", "changed") is false
   - Expected: map.get("a").unwrap() equals `one`
2. map insert
3. map insert
4. map insert
   - Expected: map.len() equals `3`
   - Expected: map.get("a").unwrap() equals `one`
   - Expected: map.has("b") is true
   - Expected: map.get("Z9!").unwrap() equals `wide`
   - Expected: map.entries().len() equals `3`
   - Expected: mapped_values.get("b").unwrap() equals `two!`
   - Expected: filtered_map.len() equals `1`
   - Expected: filtered_map.get("b").unwrap() equals `two`
5. var reserved map = HashMap with capacity
6. reserved map insert
   - Expected: reserved_map.get("cap").unwrap() equals `ok`
   - Expected: map.remove("a").unwrap() equals `one`
7. var set = HashSet new
   - Expected: set.insert("red") is true
   - Expected: set.insert("red") is false
   - Expected: set contains `red`
   - Expected: set.remove("red") is true
8. var left = HashSet new
9. left insert
10. left insert
11. var right = HashSet new
12. right insert
13. right insert
   - Expected: union_set.len() equals `3`
   - Expected: union_set contains `red`
   - Expected: union_set contains `blue`
   - Expected: union_set contains `green`
   - Expected: intersection.len() equals `1`
   - Expected: intersection contains `blue`
   - Expected: difference.len() equals `1`
   - Expected: difference contains `red`
   - Expected: symmetric.len() equals `2`
   - Expected: symmetric contains `red`
   - Expected: symmetric contains `green`
   - Expected: intersection.is_subset(union_set) is true
   - Expected: union_set.is_superset(intersection) is true
   - Expected: left.to_array().len() equals `2`
   - Expected: mapped contains `red!`
   - Expected: filtered.len() equals `2`
14. var reserved set = HashSet with capacity
   - Expected: reserved_set.insert("cap") is true
   - Expected: reserved_set contains `cap`
15. var tree = BTreeMap new
16. tree insert
17. tree insert
   - Expected: tree.first_key().unwrap() equals `a`
   - Expected: tree.last_key().unwrap() equals `b`
   - Expected: tree.get("b").unwrap() equals `two`


<details>
<summary>Executable SSpec</summary>

Runnable source: 67 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var map = HashMap.new()
expect(map.is_empty()).to_equal(true)
expect(map.insert_if_absent("a", "one")).to_equal(true)
expect(map.insert_if_absent("a", "changed")).to_equal(false)
expect(map.get("a").unwrap()).to_equal("one")
map.insert("a", "one")
map.insert("b", "two")
map.insert("Z9!", "wide")
expect(map.len()).to_equal(3)
expect(map.get("a").unwrap()).to_equal("one")
expect(map.has("b")).to_equal(true)
expect(map.get("Z9!").unwrap()).to_equal("wide")
expect(map.entries().len()).to_equal(3)
val mapped_values = map.map_values(_1 + "!")
expect(mapped_values.get("b").unwrap()).to_equal("two!")
val filtered_map = map.filter(\key, value: key != "a" and value != "wide")
expect(filtered_map.len()).to_equal(1)
expect(filtered_map.get("b").unwrap()).to_equal("two")
var reserved_map = HashMap.with_capacity(64)
reserved_map.insert("cap", "ok")
expect(reserved_map.get("cap").unwrap()).to_equal("ok")
expect(map.remove("a").unwrap()).to_equal("one")

var set = HashSet.new()
expect(set.insert("red")).to_equal(true)
expect(set.insert("red")).to_equal(false)
expect(set.contains("red")).to_equal(true)
expect(set.remove("red")).to_equal(true)

var left = HashSet.new()
left.insert("red")
left.insert("blue")
var right = HashSet.new()
right.insert("blue")
right.insert("green")
val union_set = left.union(right)
expect(union_set.len()).to_equal(3)
expect(union_set.contains("red")).to_equal(true)
expect(union_set.contains("blue")).to_equal(true)
expect(union_set.contains("green")).to_equal(true)
val intersection = left.intersection(right)
expect(intersection.len()).to_equal(1)
expect(intersection.contains("blue")).to_equal(true)
val difference = left.difference(right)
expect(difference.len()).to_equal(1)
expect(difference.contains("red")).to_equal(true)
val symmetric = left.symmetric_difference(right)
expect(symmetric.len()).to_equal(2)
expect(symmetric.contains("red")).to_equal(true)
expect(symmetric.contains("green")).to_equal(true)
expect(intersection.is_subset(union_set)).to_equal(true)
expect(union_set.is_superset(intersection)).to_equal(true)
expect(left.to_array().len()).to_equal(2)
val mapped = left.map(_1 + "!")
expect(mapped.contains("red!")).to_equal(true)
val filtered = union_set.filter(_1 != "green")
expect(filtered.len()).to_equal(2)
var reserved_set = HashSet.with_capacity(64)
expect(reserved_set.insert("cap")).to_equal(true)
expect(reserved_set.contains("cap")).to_equal(true)

var tree = BTreeMap.new()
tree.insert("b", "two")
tree.insert("a", "one")
expect(tree.first_key().unwrap()).to_equal("a")
expect(tree.last_key().unwrap()).to_equal("b")
expect(tree.get("b").unwrap()).to_equal("two")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/src/collections/src_collections_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_mut src collections facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
