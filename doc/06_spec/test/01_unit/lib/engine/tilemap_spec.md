# tilemap_spec

> Engine TileMap — TileMapData pure math/data tests

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
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# tilemap_spec

Engine TileMap — TileMapData pure math/data tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/tilemap_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Engine TileMap — TileMapData pure math/data tests

Tests tile grid creation, get/set round-trip, coordinate conversion,
source rect computation, map bounds, and visibility culling.

## Scenarios

### TileMapData

#### create fills tiles with -1

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tex_id = TextureId(raw: RawHandle.new(0, 1))
val tm = TileMapData.create(tex_id, 16, 16, 10, 10)
expect(tm.map_width).to_equal(10)
expect(tm.map_height).to_equal(10)
expect(tm.tile_width).to_equal(16)
expect(tm.tile_height).to_equal(16)
expect(tm.tiles.len()).to_equal(100)
# All tiles should be -1
expect(tm.tiles[0]).to_equal(-1)
expect(tm.tiles[99]).to_equal(-1)
```

</details>

#### get_tile and set_tile round-trip

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tex_id = TextureId(raw: RawHandle.new(0, 1))
val tm = TileMapData.create(tex_id, 16, 16, 10, 10)
val coord = TileCoord(col: 3, row: 5)
val updated = tm.set_tile(coord, TileIndex(value: 42))
val tile = updated.get_tile(coord)
expect(tile.value).to_equal(42)
```

</details>

#### get_tile returns -1 for out-of-bounds

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tex_id = TextureId(raw: RawHandle.new(0, 1))
val tm = TileMapData.create(tex_id, 16, 16, 10, 10)
# Column out of bounds
val oob_col = tm.get_tile(TileCoord(col: 20, row: 0))
expect(oob_col.value).to_equal(-1)
# Row out of bounds
val oob_row = tm.get_tile(TileCoord(col: 0, row: 20))
expect(oob_row.value).to_equal(-1)
# Negative column
val neg_col = tm.get_tile(TileCoord(col: -1, row: 0))
expect(neg_col.value).to_equal(-1)
```

</details>

#### world_to_tile converts world position to tile coordinates

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tex_id = TextureId(raw: RawHandle.new(0, 1))
val tm = TileMapData.create(tex_id, 32, 32, 10, 10)
# Position (48.0, 64.0) with 32x32 tiles => col=1, row=2
val coord = tm.world_to_tile(Vec2(x: 48.0, y: 64.0))
expect(coord.col).to_equal(1)
expect(coord.row).to_equal(2)
```

</details>

#### tile_to_world converts tile coordinates to world center

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tex_id = TextureId(raw: RawHandle.new(0, 1))
val tm = TileMapData.create(tex_id, 32, 32, 10, 10)
# Tile (2, 3) with 32x32 tiles => world center (2*32+16, 3*32+16) = (80, 112)
val world_pos = tm.tile_to_world(TileCoord(col: 2, row: 3))
val wx_i = world_pos.x * 10.0
val wy_i = world_pos.y * 10.0
expect(wx_i).to_be_greater_than(799.0)
expect(wx_i).to_be_less_than(801.0)
expect(wy_i).to_be_greater_than(1119.0)
expect(wy_i).to_be_less_than(1121.0)
```

</details>

#### tile_src_rect returns correct Rect2

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tex_id = TextureId(raw: RawHandle.new(0, 1))
val tm = TileMapData.create(tex_id, 16, 16, 10, 10)
# Tile index 12 with map_width=10 => col=2, row=1 => (32, 16, 16, 16)
val rect = tm.tile_src_rect(TileIndex(value: 12))
val rx_i = rect.x * 10.0
val ry_i = rect.y * 10.0
expect(rx_i).to_be_greater_than(319.0)
expect(rx_i).to_be_less_than(321.0)
expect(ry_i).to_be_greater_than(159.0)
expect(ry_i).to_be_less_than(161.0)
val rw_i = rect.width * 10.0
expect(rw_i).to_be_greater_than(159.0)
expect(rw_i).to_be_less_than(161.0)
```

</details>

#### tile_src_rect returns zero rect for negative index

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tex_id = TextureId(raw: RawHandle.new(0, 1))
val tm = TileMapData.create(tex_id, 16, 16, 10, 10)
val rect = tm.tile_src_rect(TileIndex(value: -1))
val rw_i = rect.width * 10.0
expect(rw_i).to_be_greater_than(-1.0)
expect(rw_i).to_be_less_than(1.0)
```

</details>

#### map_bounds matches expected world-space rect

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tex_id = TextureId(raw: RawHandle.new(0, 1))
val tm = TileMapData.create(tex_id, 16, 16, 10, 8)
# 10*16=160 wide, 8*16=128 tall
val bounds = tm.map_bounds()
val bx_i = bounds.x * 10.0
expect(bx_i).to_be_greater_than(-1.0)
expect(bx_i).to_be_less_than(1.0)
val bw_i = bounds.width * 10.0
expect(bw_i).to_be_greater_than(1599.0)
expect(bw_i).to_be_less_than(1601.0)
val bh_i = bounds.height * 10.0
expect(bh_i).to_be_greater_than(1279.0)
expect(bh_i).to_be_less_than(1281.0)
```

</details>

#### tiles_in_rect returns correct subset

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tex_id = TextureId(raw: RawHandle.new(0, 1))
val tm = TileMapData.create(tex_id, 16, 16, 10, 10)
# Query a rect covering tiles (1,1) to (2,2) in world space: (16, 16, 32, 32)
val rect = Rect2(x: 16.0, y: 16.0, width: 32.0, height: 32.0)
val tiles = tm.tiles_in_rect(rect)
# Should include tiles at cols 1-3, rows 1-3 => up to 9 tiles
expect(tiles.len()).to_be_greater_than(0)
# Verify first tile is within expected range
val first = tiles[0]
expect(first.col).to_be_greater_than(0)
expect(first.row).to_be_greater_than(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
