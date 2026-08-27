# Tensor Bridge Batch Conversion

> Tests batch conversion between math vector types (Vec3, Vec3d) and flat tensor arrays. Validates flattening Vec3 lists to float arrays, unflattening arrays back to Vec3 lists, round-trip consistency, and equivalent operations for double-precision Vec3d types.

<!-- sdn-diagram:id=tensor_bridge_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tensor_bridge_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tensor_bridge_spec -> math
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tensor_bridge_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tensor Bridge Batch Conversion

Tests batch conversion between math vector types (Vec3, Vec3d) and flat tensor arrays. Validates flattening Vec3 lists to float arrays, unflattening arrays back to Vec3 lists, round-trip consistency, and equivalent operations for double-precision Vec3d types.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #ML-001 |
| Category | Runtime |
| Status | Active |
| Source | `test/03_system/feature/usage/tensor_bridge_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests batch conversion between math vector types (Vec3, Vec3d) and flat tensor
arrays. Validates flattening Vec3 lists to float arrays, unflattening arrays
back to Vec3 lists, round-trip consistency, and equivalent operations for
double-precision Vec3d types.

## Syntax

```simple
val vecs = [math.Vec3(1.0, 2.0, 3.0), math.Vec3(4.0, 5.0, 6.0)]
val arr = math.vecs_to_tensor(vecs)
val restored = math.tensor_to_vecs(arr)
```

## Scenarios

### Tensor Bridge Batch Conversion

#### arrtens Vec3 list to array

1. math Vec3
2. math Vec3
3. expect arr len


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vecs = [
    math.Vec3(1.0, 2.0, 3.0),
    math.Vec3(4.0, 5.0, 6.0)
]
val arr = math.vecs_to_tensor(vecs)
expect arr.len() == 6
expect arr[0] == 1.0
expect arr[1] == 2.0
expect arr[2] == 3.0
expect arr[3] == 4.0
expect arr[4] == 5.0
expect arr[5] == 6.0
```

</details>

#### unarrtens array to Vec3 list

1. expect vecs len


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0]
val vecs = math.tensor_to_vecs(arr)
expect vecs.len() == 2
expect vecs[0].x == 1.0
expect vecs[0].y == 2.0
expect vecs[0].z == 3.0
expect vecs[1].x == 4.0
```

</details>

#### round-trips Vec3 list

1. math Vec3
2. math Vec3
3. expect restored len


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = [
    math.Vec3(10.0, 20.0, 30.0),
    math.Vec3(40.0, 50.0, 60.0)
]
val arr = math.vecs_to_tensor(original)
val restored = math.tensor_to_vecs(arr)
expect restored.len() == 2
expect restored[0].x == 10.0
expect restored[1].z == 60.0
```

</details>

### Tensor Bridge Vec3d Batch Conversion

#### arrtens Vec3d list to f64 array

1. math Vec3d
2. math Vec3d
3. expect arr len


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vecs = [
    math.Vec3d(1.0, 2.0, 3.0),
    math.Vec3d(4.0, 5.0, 6.0)
]
val arr = math.vecs3d_to_tensor(vecs)
expect arr.len() == 6
expect arr[0] == 1.0
```

</details>

#### unarrtens f64 array to Vec3d list

1. expect vecs len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0]
val vecs = math.tensor_to_vecs3d(arr)
expect vecs.len() == 2
expect vecs[0].x == 1.0
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
