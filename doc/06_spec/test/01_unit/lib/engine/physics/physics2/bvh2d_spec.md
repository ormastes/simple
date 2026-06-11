# Bvh2d Specification

> <details>

<!-- sdn-diagram:id=bvh2d_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bvh2d_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bvh2d_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bvh2d_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bvh2d Specification

## Scenarios

### DynamicBvh2D

#### empty tree has null root

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bvh = DynamicBvh2D.create(0.1)
expect(bvh.root).to_equal(NULL_NODE)
```

</details>

#### inserting one body sets root

1. var bvh = DynamicBvh2D create
2. bvh insert
   - Expected: bvh.root != NULL_NODE is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bvh = DynamicBvh2D.create(0.1)
val aabb = AABB2D(min_x: -1.0, min_y: -1.0, max_x: 1.0, max_y: 1.0)
bvh.insert(aabb, 0)
expect(bvh.root != NULL_NODE).to_equal(true)
```

</details>

#### two non-overlapping produce no pairs

1. var bvh = DynamicBvh2D create
2. bvh insert
3. bvh insert
   - Expected: pairs.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bvh = DynamicBvh2D.create(0.0)
val a = AABB2D(min_x: 0.0, min_y: 0.0, max_x: 1.0, max_y: 1.0)
val b = AABB2D(min_x: 5.0, min_y: 5.0, max_x: 6.0, max_y: 6.0)
bvh.insert(a, 0)
bvh.insert(b, 1)
val pairs = bvh.query_all_pairs()
expect(pairs.len()).to_equal(0)
```

</details>

#### two overlapping produce one pair

1. var bvh = DynamicBvh2D create
2. bvh insert
3. bvh insert
   - Expected: pairs.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bvh = DynamicBvh2D.create(0.0)
val a = AABB2D(min_x: 0.0, min_y: 0.0, max_x: 2.0, max_y: 2.0)
val b = AABB2D(min_x: 1.0, min_y: 1.0, max_x: 3.0, max_y: 3.0)
bvh.insert(a, 0)
bvh.insert(b, 1)
val pairs = bvh.query_all_pairs()
expect(pairs.len()).to_equal(1)
```

</details>

#### three bodies all overlapping produces three pairs

1. var bvh = DynamicBvh2D create
2. bvh insert
3. bvh insert
4. bvh insert
   - Expected: pairs.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bvh = DynamicBvh2D.create(0.0)
val a = AABB2D(min_x: 0.0, min_y: 0.0, max_x: 2.0, max_y: 2.0)
val b = AABB2D(min_x: 1.0, min_y: 1.0, max_x: 3.0, max_y: 3.0)
val c = AABB2D(min_x: 2.0, min_y: 2.0, max_x: 4.0, max_y: 4.0)
bvh.insert(a, 0)
bvh.insert(b, 1)
bvh.insert(c, 2)
val pairs = bvh.query_all_pairs()
expect(pairs.len()).to_equal(3)
```

</details>

#### AABB overlap detection works

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = AABB2D(min_x: 0.0, min_y: 0.0, max_x: 2.0, max_y: 2.0)
val b = AABB2D(min_x: 1.5, min_y: 1.5, max_x: 3.0, max_y: 3.0)
val c = AABB2D(min_x: 5.0, min_y: 5.0, max_x: 6.0, max_y: 6.0)
expect(a.overlaps(b)).to_equal(true)
expect(a.overlaps(c)).to_equal(false)
expect(b.overlaps(c)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/physics/physics2/bvh2d_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- DynamicBvh2D

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
