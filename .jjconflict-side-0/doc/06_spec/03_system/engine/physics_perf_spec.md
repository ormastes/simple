# Physics Perf Specification

> 1. var bvh = DynamicBvh2D create

<!-- sdn-diagram:id=physics_perf_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=physics_perf_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

physics_perf_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=physics_perf_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Physics Perf Specification

## Scenarios

### Physics2 BVH Performance

#### BVH inserts 200 bodies without crash

1. var bvh = DynamicBvh2D create
2. insert grid
   - Expected: bvh.node_count > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bvh = DynamicBvh2D.create(0.1)
insert_grid(bvh, 200, 10.0)
expect(bvh.node_count > 0).to_equal(true)
```

</details>

#### scattered bodies have nodes proportional to body count

1. var bvh = DynamicBvh2D create
2. insert grid
   - Expected: bvh.node_count equals `399`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bvh = DynamicBvh2D.create(0.1)
insert_grid(bvh, 200, 10.0)
# BVH uses 2*N-1 nodes (N leaves + N-1 internal nodes)
expect(bvh.node_count).to_equal(399)
```

</details>

#### clustered bodies have nodes proportional to body count

1. var bvh = DynamicBvh2D create
2. insert cluster
   - Expected: bvh.node_count equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bvh = DynamicBvh2D.create(0.1)
insert_cluster(bvh, 50)
expect(bvh.node_count).to_equal(99)
```

</details>

#### grid with spacing has nodes proportional to body count

1. var bvh = DynamicBvh2D create
2. insert grid
   - Expected: bvh.node_count equals `199`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bvh = DynamicBvh2D.create(0.1)
insert_grid(bvh, 100, 3.0)
expect(bvh.node_count).to_equal(199)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/engine/physics_perf_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Physics2 BVH Performance

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
