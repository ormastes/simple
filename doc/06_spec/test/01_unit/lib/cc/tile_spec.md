# Tile Specification

> <details>

<!-- sdn-diagram:id=tile_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tile_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tile_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tile_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tile Specification

## Scenarios

### Tile

#### tile_new: default priority is Eventually, draw_state is Unrasterized

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = _make_tile()
expect(t.priority == TilePriority.Eventually).to_equal(true)
expect(t.draw_state == TileDrawState.Unrasterized).to_equal(true)
expect(t.has_raster_task).to_equal(false)
expect(t.required_for_activation).to_equal(false)
expect(t.id.layer_id).to_equal(7)
expect(t.content_rect.right).to_be_greater_than(0.0)
```

</details>

#### set_priority: updates priority field

1. var t =  make tile
2. t set priority
   - Expected: t.priority == TilePriority.Now is true
3. t set priority
   - Expected: t.priority == TilePriority.Soon is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var t = _make_tile()
t.set_priority(TilePriority.Now)
expect(t.priority == TilePriority.Now).to_equal(true)
t.set_priority(TilePriority.Soon)
expect(t.priority == TilePriority.Soon).to_equal(true)
```

</details>

#### begin_raster: sets InProgress and has_raster_task=true

1. var t =  make tile
2. t begin raster
   - Expected: t.draw_state == TileDrawState.InProgress is true
   - Expected: t.has_raster_task is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var t = _make_tile()
t.begin_raster()
expect(t.draw_state == TileDrawState.InProgress).to_equal(true)
expect(t.has_raster_task).to_equal(true)
```

</details>

#### complete_raster: sets Ready state with provided bitmap

1. var t =  make tile
2. t begin raster
3. t complete raster
   - Expected: t.draw_state == TileDrawState.Ready is true
   - Expected: t.has_raster_task is false
   - Expected: t.bitmap.width equals `64`
   - Expected: t.bitmap.height equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var t = _make_tile()
t.begin_raster()
val bmp = Bitmap.zeros(64, 64)
t.complete_raster(bmp)
expect(t.draw_state == TileDrawState.Ready).to_equal(true)
expect(t.has_raster_task).to_equal(false)
expect(t.bitmap.width).to_equal(64)
expect(t.bitmap.height).to_equal(64)
```

</details>

#### fail_raster: sets Failed state

1. var t =  make tile
2. t begin raster
3. t fail raster
   - Expected: t.draw_state == TileDrawState.Failed is true
   - Expected: t.has_raster_task is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var t = _make_tile()
t.begin_raster()
t.fail_raster()
expect(t.draw_state == TileDrawState.Failed).to_equal(true)
expect(t.has_raster_task).to_equal(false)
```

</details>

#### is_ready: true only when draw_state is Ready

1. var t =  make tile
   - Expected: t.is_ready is false
2. t begin raster
   - Expected: t.is_ready is false
3. t complete raster
   - Expected: t.is_ready is true
4. var t2 =  make tile
5. t2 begin raster
6. t2 fail raster
   - Expected: t2.is_ready is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var t = _make_tile()
expect(t.is_ready).to_equal(false)
t.begin_raster()
expect(t.is_ready).to_equal(false)
val bmp = Bitmap.zeros(32, 32)
t.complete_raster(bmp)
expect(t.is_ready).to_equal(true)
# Failed is not Ready
var t2 = _make_tile()
t2.begin_raster()
t2.fail_raster()
expect(t2.is_ready).to_equal(false)
```

</details>

#### mark_required_for_activation: updates flag

1. var t =  make tile
   - Expected: t.required_for_activation is false
2. t mark required for activation
   - Expected: t.required_for_activation is true
3. t mark required for activation
   - Expected: t.required_for_activation is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var t = _make_tile()
expect(t.required_for_activation).to_equal(false)
t.mark_required_for_activation(true)
expect(t.required_for_activation).to_equal(true)
t.mark_required_for_activation(false)
expect(t.required_for_activation).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/cc/tile_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Tile

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
