# Blink PaintChunk Specification

> Tests for the Blink-style PaintChunk — a grouped drawing unit that batches consecutive DisplayItems sharing the same PropertyTreeState (transform id + clip id + effect id + scroll id). Covers root-state construction, factory initialization, size/empty helpers, property-state equality, and bounds overlap detection.

<!-- sdn-diagram:id=paint_chunk_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=paint_chunk_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

paint_chunk_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=paint_chunk_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Blink PaintChunk Specification

Tests for the Blink-style PaintChunk — a grouped drawing unit that batches consecutive DisplayItems sharing the same PropertyTreeState (transform id + clip id + effect id + scroll id). Covers root-state construction, factory initialization, size/empty helpers, property-state equality, and bounds overlap detection.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Browser / Blink |
| Status | Stub |
| Source | `test/01_unit/lib/blink/paint_chunk_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for the Blink-style PaintChunk — a grouped drawing unit that batches
consecutive DisplayItems sharing the same PropertyTreeState (transform id +
clip id + effect id + scroll id). Covers root-state construction, factory
initialization, size/empty helpers, property-state equality, and bounds
overlap detection.

## Scenarios

### property_tree_state_root

#### all ids are -1

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = property_tree_state_root()
expect(state.transform_id).to_equal(-1)
expect(state.clip_id).to_equal(-1)
expect(state.effect_id).to_equal(-1)
expect(state.scroll_id).to_equal(-1)
```

</details>

### paint_chunk_new

#### begin/end/id/bounds set correctly; is_cacheable defaults true

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val id = PaintChunkId(owner_node_id: 42, display_item_index: 7)
val state = property_tree_state_root()
val bounds = sk_rect(0.0, 0.0, 100.0, 50.0)
val chunk = paint_chunk_new(2, 9, id, state, bounds)
expect(chunk.begin_index).to_equal(2)
expect(chunk.end_index).to_equal(9)
expect(chunk.id.owner_node_id).to_equal(42)
expect(chunk.id.display_item_index).to_equal(7)
expect(chunk.bounds.right).to_equal(100.0)
expect(chunk.bounds.bottom).to_equal(50.0)
expect(chunk.is_cacheable).to_equal(true)
```

</details>

### size

#### end - begin

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val id = PaintChunkId(owner_node_id: 0, display_item_index: 0)
val state = property_tree_state_root()
val bounds = sk_rect(0.0, 0.0, 10.0, 10.0)
val chunk = paint_chunk_new(3, 8, id, state, bounds)
expect(chunk.size()).to_equal(5)
expect(chunk.size()).to_be_greater_than(0)
```

</details>

### is_empty

#### begin == end returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val id = PaintChunkId(owner_node_id: 0, display_item_index: 0)
val state = property_tree_state_root()
val bounds = sk_rect(0.0, 0.0, 10.0, 10.0)
val chunk = paint_chunk_new(4, 4, id, state, bounds)
expect(chunk.is_empty()).to_equal(true)
```

</details>

### has_same_property_state

#### same ids returns true, different returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val id = PaintChunkId(owner_node_id: 0, display_item_index: 0)
val bounds = sk_rect(0.0, 0.0, 10.0, 10.0)
val state_a = PropertyTreeState(transform_id: 1, clip_id: 2, effect_id: 3, scroll_id: 4)
val state_b = PropertyTreeState(transform_id: 1, clip_id: 2, effect_id: 3, scroll_id: 4)
val state_c = PropertyTreeState(transform_id: 1, clip_id: 2, effect_id: 9, scroll_id: 4)
val chunk_a = paint_chunk_new(0, 1, id, state_a, bounds)
val chunk_b = paint_chunk_new(0, 1, id, state_b, bounds)
val chunk_c = paint_chunk_new(0, 1, id, state_c, bounds)
expect(chunk_a.has_same_property_state(chunk_b)).to_equal(true)
expect(chunk_a.has_same_property_state(chunk_c)).to_equal(false)
```

</details>

### overlaps

#### disjoint bounds returns false, overlapping returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val id = PaintChunkId(owner_node_id: 0, display_item_index: 0)
val state = property_tree_state_root()
val bounds_a = sk_rect(0.0, 0.0, 10.0, 10.0)
val bounds_b = sk_rect(20.0, 20.0, 30.0, 30.0)
val bounds_c = sk_rect(5.0, 5.0, 15.0, 15.0)
val chunk_a = paint_chunk_new(0, 1, id, state, bounds_a)
val chunk_b = paint_chunk_new(0, 1, id, state, bounds_b)
val chunk_c = paint_chunk_new(0, 1, id, state, bounds_c)
expect(chunk_a.overlaps(chunk_b)).to_equal(false)
expect(chunk_a.overlaps(chunk_c)).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
