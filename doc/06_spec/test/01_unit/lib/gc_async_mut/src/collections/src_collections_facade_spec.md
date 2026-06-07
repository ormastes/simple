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

### gc_async_mut src collections facade

#### re-exports hash map, hash set, and btree map behavior

1. var map = HashMap new
   - Expected: map.is_empty() is true
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
8. var reserved set = HashSet with capacity
   - Expected: reserved_set.insert("cap") is true
   - Expected: reserved_set contains `cap`
9. var tree = BTreeMap new
10. tree insert
11. tree insert
   - Expected: tree.first_key().unwrap() equals `a`
   - Expected: tree.last_key().unwrap() equals `b`
   - Expected: tree.get("b").unwrap() equals `two`


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var map = HashMap.new()
expect(map.is_empty()).to_equal(true)
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
| Source | `test/01_unit/lib/gc_async_mut/src/collections/src_collections_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_mut src collections facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
