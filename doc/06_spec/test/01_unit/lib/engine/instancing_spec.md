# Instancing Specification

> 1. var batch = InstanceBatch new

<!-- sdn-diagram:id=instancing_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=instancing_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

instancing_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=instancing_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Instancing Specification

## Scenarios

### InstanceBatch

#### adds instances up to max

1. var batch = InstanceBatch new
2. batch add instance
3. batch add instance
4. batch add instance
   - Expected: batch.instance_count() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var batch = InstanceBatch.new("tree", "bark_mat", 3)
val i1 = InstanceData.new(1.0, 0.0, 0.0)
val i2 = InstanceData.new(2.0, 0.0, 0.0)
val i3 = InstanceData.new(3.0, 0.0, 0.0)
batch.add_instance(i1)
batch.add_instance(i2)
batch.add_instance(i3)
expect(batch.instance_count()).to_equal(3)
```

</details>

#### rejects instance when full

1. var batch = InstanceBatch new
2. batch add instance
   - Expected: idx equals `-1`
   - Expected: batch.instance_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var batch = InstanceBatch.new("tree", "bark_mat", 1)
val i1 = InstanceData.new(1.0, 0.0, 0.0)
val i2 = InstanceData.new(2.0, 0.0, 0.0)
batch.add_instance(i1)
val idx = batch.add_instance(i2)
expect(idx).to_equal(-1)
expect(batch.instance_count()).to_equal(1)
```

</details>

#### removes instance by index

1. var batch = InstanceBatch new
2. batch add instance
3. batch add instance
4. batch remove instance
   - Expected: batch.instance_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var batch = InstanceBatch.new("rock", "stone_mat", 10)
val i1 = InstanceData.new(1.0, 0.0, 0.0)
val i2 = InstanceData.new(2.0, 0.0, 0.0)
batch.add_instance(i1)
batch.add_instance(i2)
batch.remove_instance(0)
expect(batch.instance_count()).to_equal(1)
```

</details>

#### toggles visibility

1. var batch = InstanceBatch new
   - Expected: batch.is_visible() is true
2. batch set visible
   - Expected: batch.is_visible() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var batch = InstanceBatch.new("bush", "leaf_mat", 10)
expect(batch.is_visible()).to_equal(true)
batch.set_visible(false)
expect(batch.is_visible()).to_equal(false)
```

</details>

#### clears all instances

1. var batch = InstanceBatch new
2. batch add instance
3. batch add instance
4. batch clear
   - Expected: batch.instance_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var batch = InstanceBatch.new("grass", "grass_mat", 100)
val i1 = InstanceData.new(1.0, 0.0, 0.0)
val i2 = InstanceData.new(2.0, 0.0, 0.0)
batch.add_instance(i1)
batch.add_instance(i2)
batch.clear()
expect(batch.instance_count()).to_equal(0)
```

</details>

### InstanceRenderer

#### manages batches and counts total instances

1. var renderer = InstanceRenderer new
2. var b1 = InstanceBatch new
3. var b2 = InstanceBatch new
4. b1 add instance
5. b1 add instance
6. b2 add instance
7. renderer add batch
8. renderer add batch
   - Expected: renderer.batch_count() equals `2`
   - Expected: renderer.total_instance_count() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var renderer = InstanceRenderer.new()
var b1 = InstanceBatch.new("tree", "bark", 100)
var b2 = InstanceBatch.new("rock", "stone", 100)
val t1 = InstanceData.new(0.0, 0.0, 0.0)
val t2 = InstanceData.new(1.0, 0.0, 0.0)
val r1 = InstanceData.new(5.0, 0.0, 0.0)
b1.add_instance(t1)
b1.add_instance(t2)
b2.add_instance(r1)
renderer.add_batch(b1)
renderer.add_batch(b2)
expect(renderer.batch_count()).to_equal(2)
expect(renderer.total_instance_count()).to_equal(3)
```

</details>

#### excludes hidden batches from total count

1. var renderer = InstanceRenderer new
2. var b1 = InstanceBatch new
3. b1 add instance
4. b1 add instance
5. b1 set visible
6. renderer add batch
   - Expected: renderer.total_instance_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var renderer = InstanceRenderer.new()
var b1 = InstanceBatch.new("tree", "bark", 100)
val i1 = InstanceData.new(0.0, 0.0, 0.0)
val i2 = InstanceData.new(1.0, 0.0, 0.0)
b1.add_instance(i1)
b1.add_instance(i2)
b1.set_visible(false)
renderer.add_batch(b1)
expect(renderer.total_instance_count()).to_equal(0)
```

</details>

### InstanceData

#### creates with default scale

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inst = InstanceData.new(3.0, 4.0, 5.0)
expect(inst.scale_x).to_equal(1.0)
expect(inst.scale_y).to_equal(1.0)
expect(inst.position_x).to_equal(3.0)
```

</details>

#### creates with custom scale

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inst = InstanceData.with_scale(1.0, 2.0, 3.0, 0.5, 0.5, 0.5)
expect(inst.scale_x).to_equal(0.5)
expect(inst.position_z).to_equal(3.0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/instancing_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- InstanceBatch
- InstanceRenderer
- InstanceData

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
