# Concurrent Collections Pure Specification

> <details>

<!-- sdn-diagram:id=concurrent_collections_pure_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=concurrent_collections_pure_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

concurrent_collections_pure_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=concurrent_collections_pure_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Concurrent Collections Pure Specification

## Scenarios

### nogc_async_mut concurrent collections pure Simple

#### stores hash map values without runtime handles

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val map = hashmap_new()
expect(map.insert("name", "Alice")).to_equal(true)
expect(map.insert("name", "Ada")).to_equal(false)
expect(map.contains_key("name")).to_equal(true)
expect(map.get("name")).to_equal("Ada")
expect(map.len()).to_equal(1)
expect(map.remove("name")).to_equal("Ada")
expect(map.contains_key("name")).to_equal(false)
```

</details>

#### performs hash set membership operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val set = hashset_new()
expect(set.insert("apple")).to_equal(true)
expect(set.insert("apple")).to_equal(false)
expect(set.insert("banana")).to_equal(true)
expect(set.contains("banana")).to_equal(true)
expect(set.len()).to_equal(2)
expect(set.remove("apple")).to_equal(true)
expect(set.contains("apple")).to_equal(false)
```

</details>

#### keeps btree map keys sorted

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val map = btreemap_new()
expect(map.insert("z", 1)).to_equal(true)
expect(map.insert("a", 2)).to_equal(true)
expect(map.insert("m", 3)).to_equal(true)
expect(map.first_key()).to_equal("a")
expect(map.last_key()).to_equal("z")
expect(map.get("m")).to_equal(3)
expect(map.remove("a")).to_equal(2)
expect(map.first_key()).to_equal("m")
```

</details>

#### computes btree set operations

1. left insert
2. left insert
3. right insert
4. right insert
   - Expected: both contains `b`
   - Expected: both does not contain `a`
   - Expected: only_left contains `a`
   - Expected: either.len() equals `3`
   - Expected: either.first() equals `a`
   - Expected: either.last() equals `c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val left = btreeset_new()
val right = btreeset_new()
left.insert("a")
left.insert("b")
right.insert("b")
right.insert("c")

val both = left.intersection(right)
val only_left = left.difference(right)
val either = left.union(right)

expect(both.contains("b")).to_equal(true)
expect(both.contains("a")).to_equal(false)
expect(only_left.contains("a")).to_equal(true)
expect(either.len()).to_equal(3)
expect(either.first()).to_equal("a")
expect(either.last()).to_equal("c")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/concurrent_collections_pure_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_mut concurrent collections pure Simple

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
