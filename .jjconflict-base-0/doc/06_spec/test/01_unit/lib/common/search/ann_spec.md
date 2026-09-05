# Ann Specification

> <details>

<!-- sdn-diagram:id=ann_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ann_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ann_spec -> std
ann_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ann_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ann Specification

## Scenarios

### l2_sq_distance (integer, exact)

#### computes squared Euclidean distance over fixed-point components

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = vec2(1, 1)
val b = vec2(4, 5)
# (4-1)^2 + (5-1)^2 = 9 + 16 = 25
expect(l2_sq_distance(a, b)).to_equal(25)
```

</details>

#### is zero for identical vectors

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = vec3(2, 3, 4)
expect(l2_sq_distance(a, a)).to_equal(0)
```

</details>

#### is symmetric

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = vec3(1, 2, 3)
val b = vec3(4, 0, 1)
expect(l2_sq_distance(a, b)).to_equal(l2_sq_distance(b, a))
```

</details>

### ExactKnn ORACLE — known nearest neighbor

#### returns the single KNOWN nearest id for query (1,1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val idx = build_fixture()
# ids 6 (1,0) and 7 (0,1) both at distance 1; tie-break picks smaller id 6.
expect(idx.nearest_id(vec2(1, 1))).to_equal(6)
```

</details>

#### returns top-3 in KNOWN nearest-first order with id tie-break

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val idx = build_fixture()
val top = idx.query(vec2(1, 1), 3)
expect(top.len()).to_equal(3)
# distance 1: id6, id7 (tie -> id6 first); distance 2: id0
expect(top[0].doc_id()).to_equal(6)
expect(top[0].distance()).to_equal(1)
expect(top[1].doc_id()).to_equal(7)
expect(top[1].distance()).to_equal(1)
expect(top[2].doc_id()).to_equal(0)
expect(top[2].distance()).to_equal(2)
```

</details>

#### equidistant points are ordered by ascending id (tie case)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val idx = build_fixture()
val top = idx.query(vec2(1, 1), 2)
# Both id6 and id7 sit at distance 1; deterministic order is 6 then 7.
expect(top[0].doc_id()).to_equal(6)
expect(top[1].doc_id()).to_equal(7)
```

</details>

#### finds the far corner for a far query

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val idx = build_fixture()
# Query (11,11) is nearest to id3 (10,10): distance 1+1 = 2.
expect(idx.nearest_id(vec2(11, 11))).to_equal(3)
```

</details>

#### 3D oracle picks the known nearest

- var idx = ExactKnn new
- idx add
- idx add
- idx add
   - Expected: idx.nearest_id(vec3(0, 0, 1)) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var idx = ExactKnn.new()
idx.add(0, vec3(0, 0, 0))
idx.add(1, vec3(5, 5, 5))
idx.add(2, vec3(1, 0, 0))
# Query (0,0,1): id0 dist 1, id2 dist 2, id1 dist 75 -> nearest id0.
expect(idx.nearest_id(vec3(0, 0, 1))).to_equal(0)
```

</details>

### Neighbor typed result

#### carries id and distance and a closer=higher Score

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n = Neighbor.of(7, 25)
expect(n.doc_id()).to_equal(7)
expect(n.distance()).to_equal(25)
# score is -distance so nearer ranks higher
expect(n.score().raw_value()).to_equal(0 - 25)
```

</details>

#### is_nearer_than orders by smaller distance

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_nearer).to_equal(true)
```

</details>

### IvfIndex APPROXIMATE — recall vs exact oracle

#### achieves recall@3 >= 0.8 against the independent exact oracle

- var ivf = IvfIndex new
- ivf add
- ivf add
- ivf add
- ivf add
- ivf add
- ivf add
- ivf add
- ivf add


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Build the SAME fixture into both the oracle and the IVF index.
val oracle = build_fixture()
var ivf = IvfIndex.new(3, 2)
ivf.add(0, vec2(0, 0))
ivf.add(1, vec2(10, 0))
ivf.add(2, vec2(0, 10))
ivf.add(3, vec2(10, 10))
ivf.add(4, vec2(3, 3))
ivf.add(5, vec2(7, 7))
ivf.add(6, vec2(1, 0))
ivf.add(7, vec2(0, 1))

val q = vec2(1, 1)
val exact = oracle.query(q, 3)
val approx = ivf.query(q, 3)
val r = recall_permille(approx, exact)
# Stated threshold: >= 0.8 (800 per-mille) of the true top-3.
expect(r).to_be_greater_than(799)
```

</details>

#### finds the true top-1 via the approximate index

- var ivf = IvfIndex new
- ivf add
- ivf add
- ivf add
- ivf add
- ivf add
- ivf add
- ivf add
- ivf add
   - Expected: approx_top1 equals `true_top1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val oracle = build_fixture()
var ivf = IvfIndex.new(3, 2)
ivf.add(0, vec2(0, 0))
ivf.add(1, vec2(10, 0))
ivf.add(2, vec2(0, 10))
ivf.add(3, vec2(10, 10))
ivf.add(4, vec2(3, 3))
ivf.add(5, vec2(7, 7))
ivf.add(6, vec2(1, 0))
ivf.add(7, vec2(0, 1))

val q = vec2(1, 1)
val true_top1 = oracle.nearest_id(q)
val approx_top1 = ivf.nearest_id(q)
expect(approx_top1).to_equal(true_top1)
```

</details>

#### with nprobe = nlist the IVF index degenerates to exact (recall 1.0)

- var ivf = IvfIndex new
- ivf add
- ivf add
- ivf add
- ivf add
- ivf add
- ivf add
- ivf add
- ivf add
   - Expected: recall_permille(approx, exact) equals `1000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Probing every cluster must reproduce the exact oracle exactly.
val oracle = build_fixture()
var ivf = IvfIndex.new(3, 3)
ivf.add(0, vec2(0, 0))
ivf.add(1, vec2(10, 0))
ivf.add(2, vec2(0, 10))
ivf.add(3, vec2(10, 10))
ivf.add(4, vec2(3, 3))
ivf.add(5, vec2(7, 7))
ivf.add(6, vec2(1, 0))
ivf.add(7, vec2(0, 1))

val q = vec2(1, 1)
val exact = oracle.query(q, 3)
val approx = ivf.query(q, 3)
expect(recall_permille(approx, exact)).to_equal(1000)
```

</details>

#### assigns every point to a cluster and seeds nlist centroids

- var ivf = IvfIndex new
- ivf add
- ivf add
- ivf add
- ivf add
- ivf add
   - Expected: ivf.size() equals `5`
   - Expected: ivf.cluster_count() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ivf = IvfIndex.new(3, 2)
ivf.add(0, vec2(0, 0))
ivf.add(1, vec2(10, 0))
ivf.add(2, vec2(0, 10))
ivf.add(3, vec2(10, 10))
ivf.add(4, vec2(3, 3))
expect(ivf.size()).to_equal(5)
expect(ivf.cluster_count()).to_equal(3)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/search/ann_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- l2_sq_distance (integer, exact)
- ExactKnn ORACLE — known nearest neighbor
- Neighbor typed result
- IvfIndex APPROXIMATE — recall vs exact oracle

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
