# Paint Controller Specification

> <details>

<!-- sdn-diagram:id=paint_controller_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=paint_controller_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

paint_controller_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=paint_controller_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Paint Controller Specification

## Scenarios

### PaintController

#### commit on empty controller yields zero chunks

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctrl = PaintController.new()
val artifact = ctrl.commit()
expect(artifact.chunk_count()).to_equal(0)
```

</details>

#### single property set with three items yields one chunk

1. ctrl update properties
2. ctrl record item
3. ctrl record item
4. ctrl record item
   - Expected: artifact.chunk_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctrl = PaintController.new()
val props = PaintChunkProperties(transform_id: 0, clip_id: 0, effect_id: 0)
ctrl.update_properties(props)
ctrl.record_item(DisplayItem.create(0, PaintOp.PopClip))
ctrl.record_item(DisplayItem.create(0, PaintOp.PopClip))
ctrl.record_item(DisplayItem.create(0, PaintOp.PopClip))
val artifact = ctrl.commit()
expect(artifact.chunk_count()).to_equal(1)
```

</details>

#### one chunk spans items 0..3

1. ctrl update properties
2. ctrl record item
3. ctrl record item
4. ctrl record item
   - Expected: chunk.begin_index equals `0`
   - Expected: chunk.end_index equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctrl = PaintController.new()
val props = PaintChunkProperties(transform_id: 0, clip_id: 0, effect_id: 0)
ctrl.update_properties(props)
ctrl.record_item(DisplayItem.create(0, PaintOp.PopClip))
ctrl.record_item(DisplayItem.create(0, PaintOp.PopClip))
ctrl.record_item(DisplayItem.create(0, PaintOp.PopClip))
val artifact = ctrl.commit()
val chunk = artifact.chunks.get(0).unwrap()
expect(chunk.begin_index).to_equal(0)
expect(chunk.end_index).to_equal(3)
```

</details>

#### switching properties produces two chunks

1. ctrl update properties
2. ctrl record item
3. ctrl record item
4. ctrl record item
5. ctrl update properties
6. ctrl record item
7. ctrl record item
   - Expected: artifact.chunk_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctrl = PaintController.new()
val props_a = PaintChunkProperties(transform_id: 0, clip_id: 0, effect_id: 0)
val props_b = PaintChunkProperties(transform_id: 1, clip_id: 0, effect_id: 0)
ctrl.update_properties(props_a)
ctrl.record_item(DisplayItem.create(0, PaintOp.PopClip))
ctrl.record_item(DisplayItem.create(0, PaintOp.PopClip))
ctrl.record_item(DisplayItem.create(0, PaintOp.PopClip))
ctrl.update_properties(props_b)
ctrl.record_item(DisplayItem.create(0, PaintOp.PopClip))
ctrl.record_item(DisplayItem.create(0, PaintOp.PopClip))
val artifact = ctrl.commit()
expect(artifact.chunk_count()).to_equal(2)
```

</details>

#### first chunk covers items 0..3, second chunk covers 3..5

1. ctrl update properties
2. ctrl record item
3. ctrl record item
4. ctrl record item
5. ctrl update properties
6. ctrl record item
7. ctrl record item
   - Expected: chunk0.begin_index equals `0`
   - Expected: chunk0.end_index equals `3`
   - Expected: chunk1.begin_index equals `3`
   - Expected: chunk1.end_index equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctrl = PaintController.new()
val props_a = PaintChunkProperties(transform_id: 0, clip_id: 0, effect_id: 0)
val props_b = PaintChunkProperties(transform_id: 1, clip_id: 0, effect_id: 0)
ctrl.update_properties(props_a)
ctrl.record_item(DisplayItem.create(0, PaintOp.PopClip))
ctrl.record_item(DisplayItem.create(0, PaintOp.PopClip))
ctrl.record_item(DisplayItem.create(0, PaintOp.PopClip))
ctrl.update_properties(props_b)
ctrl.record_item(DisplayItem.create(0, PaintOp.PopClip))
ctrl.record_item(DisplayItem.create(0, PaintOp.PopClip))
val artifact = ctrl.commit()
val chunk0 = artifact.chunks.get(0).unwrap()
val chunk1 = artifact.chunks.get(1).unwrap()
expect(chunk0.begin_index).to_equal(0)
expect(chunk0.end_index).to_equal(3)
expect(chunk1.begin_index).to_equal(3)
expect(chunk1.end_index).to_equal(5)
```

</details>

#### second chunk carries the new transform_id

1. ctrl update properties
2. ctrl record item
3. ctrl update properties
4. ctrl record item
   - Expected: chunk1.properties.transform_id equals `7`
   - Expected: chunk1.properties.clip_id equals `2`
   - Expected: chunk1.properties.effect_id equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctrl = PaintController.new()
val props_a = PaintChunkProperties(transform_id: 0, clip_id: 0, effect_id: 0)
val props_b = PaintChunkProperties(transform_id: 7, clip_id: 2, effect_id: 3)
ctrl.update_properties(props_a)
ctrl.record_item(DisplayItem.create(0, PaintOp.PopClip))
ctrl.update_properties(props_b)
ctrl.record_item(DisplayItem.create(0, PaintOp.PopClip))
val artifact = ctrl.commit()
val chunk1 = artifact.chunks.get(1).unwrap()
expect(chunk1.properties.transform_id).to_equal(7)
expect(chunk1.properties.clip_id).to_equal(2)
expect(chunk1.properties.effect_id).to_equal(3)
```

</details>

#### item_count matches total recorded items

1. ctrl update properties
2. ctrl record item
3. ctrl record item
   - Expected: artifact.item_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctrl = PaintController.new()
val props = PaintChunkProperties(transform_id: 0, clip_id: 0, effect_id: 0)
ctrl.update_properties(props)
ctrl.record_item(DisplayItem.create(0, PaintOp.PopClip))
ctrl.record_item(DisplayItem.create(0, PaintOp.PopClip))
val artifact = ctrl.commit()
expect(artifact.item_count()).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/blink/paint_controller_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- PaintController

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
