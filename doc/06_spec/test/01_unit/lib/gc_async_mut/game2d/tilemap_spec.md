# Tilemap Specification

> <details>

<!-- sdn-diagram:id=tilemap_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tilemap_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tilemap_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tilemap_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tilemap Specification

## Scenarios

### TileMap

### create

#### stores tileset texture id

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cells = [[0, 1], [2, 3]]
val tm = TestTileMap.create(tid: 5, tw: 16, th: 16, cells: cells)
expect(tm.tileset_texture_id).to_equal(5)
```

</details>

#### stores tile dimensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cells = [[0]]
val tm = TestTileMap.create(tid: 1, tw: 32, th: 24, cells: cells)
expect(tm.tile_w).to_equal(32)
expect(tm.tile_h).to_equal(24)
```

</details>

#### computes row and column counts

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cells = [[0, 1, 2], [3, 4, 5], [6, 7, 8]]
val tm = TestTileMap.create(tid: 1, tw: 16, th: 16, cells: cells)
expect(tm.rows).to_equal(3)
expect(tm.cols).to_equal(3)
```

</details>

### tile_at

#### returns tile index for valid position

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cells = [[0, 1, 2], [3, 4, 5]]
val tm = TestTileMap.create(tid: 1, tw: 16, th: 16, cells: cells)
expect(tm.tile_at(0, 1)).to_equal(1)
expect(tm.tile_at(1, 2)).to_equal(5)
```

</details>

#### returns -1 for out-of-bounds positions

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cells = [[0, 1]]
val tm = TestTileMap.create(tid: 1, tw: 16, th: 16, cells: cells)
expect(tm.tile_at(5, 0)).to_equal(-1)
expect(tm.tile_at(0, 5)).to_equal(-1)
```

</details>

#### respects -1 empty tile in cells

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cells = [[-1, 2], [3, -1]]
val tm = TestTileMap.create(tid: 1, tw: 8, th: 8, cells: cells)
expect(tm.tile_at(0, 0)).to_equal(-1)
expect(tm.tile_at(1, 1)).to_equal(-1)
```

</details>

### render_tilemap

#### counts non-empty tiles

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cells = [[0, 1, -1], [3, -1, 5]]
val tm = TestTileMap.create(tid: 1, tw: 8, th: 8, cells: cells)
expect(tm.rendered_tiles()).to_equal(4)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/game2d/tilemap_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- TileMap
- create
- tile_at
- render_tilemap

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
