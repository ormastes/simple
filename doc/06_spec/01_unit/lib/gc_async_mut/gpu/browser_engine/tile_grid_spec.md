# tile_grid_spec

> Tile render culling core spec (T1 + T3)

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# tile_grid_spec

Tile render culling core spec (T1 + T3)

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/tile_grid_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Tile render culling core spec (T1 + T3)

Unit coverage for the 256px tile grid: op->tile binning (boundary rects,
multi-tile spans, negative coords), hidden/zero-area drop at bin time,
FNV-1a per-tile checksum stability, viewport+margin live-tile set from a
scroll offset, and conservative full-tile opaque occlusion.

Plan: doc/03_plan/ui/rendering/tile_render_culling_plan.md

@tag: rendering, simple-web, tiles, culling
@cover src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_paint_tiles.spl 90%

## Scenarios

### tile grid math

#### floor-divides negative coordinates toward negative infinity

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- floor-divides negative coordinates toward negative infinity
   - Expected: tile_floor_div(0, 256) equals `0`
   - Expected: tile_floor_div(255, 256) equals `0`
   - Expected: tile_floor_div(256, 256) equals `1`
   - Expected: tile_floor_div(-1, 256) equals `-1`
   - Expected: tile_floor_div(-256, 256) equals `-1`
   - Expected: tile_floor_div(-257, 256) equals `-2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("floor-divides negative coordinates toward negative infinity")
expect(tile_floor_div(0, 256)).to_equal(0)
expect(tile_floor_div(255, 256)).to_equal(0)
expect(tile_floor_div(256, 256)).to_equal(1)
expect(tile_floor_div(-1, 256)).to_equal(-1)
expect(tile_floor_div(-256, 256)).to_equal(-1)
expect(tile_floor_div(-257, 256)).to_equal(-2)
```

</details>

#### sizes the grid from a document rect

- sizes the grid from a document rect
   - Expected: grid.tiles_x equals `4`
   - Expected: grid.tiles_y equals `16`
   - Expected: tile_count(grid) equals `64`
   - Expected: ragged.tiles_x equals `5`
   - Expected: ragged.tiles_y equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("sizes the grid from a document rect")
val grid = tile_grid_make(0, 0, 1024, 4096)
expect(grid.tiles_x).to_equal(4)
expect(grid.tiles_y).to_equal(16)
expect(tile_count(grid)).to_equal(64)
# Non-multiple sizes round up to a covering tile.
val ragged = tile_grid_make(0, 0, 1025, 257)
expect(ragged.tiles_x).to_equal(5)
expect(ragged.tiles_y).to_equal(2)
```

</details>

#### returns an empty grid for a degenerate document rect

- returns an empty grid for a degenerate document rect
   - Expected: tile_count(grid) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns an empty grid for a degenerate document rect")
val grid = tile_grid_make(0, 0, 0, 4096)
expect(tile_count(grid)).to_equal(0)
```

</details>

#### clips the ragged bottom-right 8K tile to the exact viewport

- clips the ragged bottom-right 8K tile to the exact viewport
   - Expected: grid.tiles_x equals `30`
   - Expected: grid.tiles_y equals `17`
   - Expected: tile_count(grid) equals `510`
   - Expected: tile_rect_x0(grid, 509) equals `7424`
   - Expected: tile_rect_x1(grid, 509) equals `7680`
   - Expected: tile_rect_y0(grid, 509) equals `4096`
   - Expected: tile_rect_y1(grid, 509) equals `4320`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("clips the ragged bottom-right 8K tile to the exact viewport")
val grid = tile_grid_make(0, 0, 7680, 4320)
expect(grid.tiles_x).to_equal(30)
expect(grid.tiles_y).to_equal(17)
expect(tile_count(grid)).to_equal(510)
expect(tile_rect_x0(grid, 509)).to_equal(7424)
expect(tile_rect_x1(grid, 509)).to_equal(7680)
expect(tile_rect_y0(grid, 509)).to_equal(4096)
expect(tile_rect_y1(grid, 509)).to_equal(4320)
```

</details>

#### clips a non-aligned leading tile to the document origin

- clips a non-aligned leading tile to the document origin
   - Expected: tile_rect_x0(grid, 0) equals `10`
   - Expected: tile_rect_y0(grid, 0) equals `20`
   - Expected: tile_rect_x1(grid, 0) equals `256`
   - Expected: tile_rect_y1(grid, 0) equals `256`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("clips a non-aligned leading tile to the document origin")
val grid = tile_grid_make(10, 20, 300, 310)
expect(tile_rect_x0(grid, 0)).to_equal(10)
expect(tile_rect_y0(grid, 0)).to_equal(20)
expect(tile_rect_x1(grid, 0)).to_equal(256)
expect(tile_rect_y1(grid, 0)).to_equal(256)
```

</details>

#### exposes tile rect origins by index

- exposes tile rect origins by index
   - Expected: tile_rect_x0(grid, 0) equals `0`
   - Expected: tile_rect_y0(grid, 0) equals `0`
   - Expected: tile_rect_x0(grid, 5) equals `TILE_PX`
   - Expected: tile_rect_y0(grid, 5) equals `TILE_PX`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("exposes tile rect origins by index")
val grid = tile_grid_make(0, 0, 1024, 1024)
expect(tile_rect_x0(grid, 0)).to_equal(0)
expect(tile_rect_y0(grid, 0)).to_equal(0)
expect(tile_rect_x0(grid, 5)).to_equal(TILE_PX)
expect(tile_rect_y0(grid, 5)).to_equal(TILE_PX)
```

</details>

### tile binning

#### does not bin an op wholly inside a non-aligned grid's padded edge

- does not bin an op wholly inside a non-aligned grid's padded edge
   - Expected: bins.items.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("does not bin an op wholly inside a non-aligned grid's padded edge")
val grid = tile_grid_make(10, 20, 300, 310)
val bins = tile_bin_ops([_box(0, 0, 0, 9, 19)], grid)
expect(bins.items.len()).to_equal(0)
```

</details>

#### bins an intersecting rect without overflowing its far edge

- bins an intersecting rect without overflowing its far edge
   - Expected: bins.items.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("bins an intersecting rect without overflowing its far edge")
val grid = tile_grid_make(2147483000, 0, 2147483600, 256)
val bins = tile_bin_ops([_box(0, 2147483500, 0, 500, 256)], grid)
expect(bins.items.len()).to_equal(1)
```

</details>

#### bins an op spanning four tiles into all four

- bins an op spanning four tiles into all four
   - Expected: _bin_count(bins, 0) equals `1`
   - Expected: _bin_count(bins, 1) equals `1`
   - Expected: _bin_count(bins, 4) equals `1`
   - Expected: _bin_count(bins, 5) equals `1`
   - Expected: _bin_count(bins, 2) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("bins an op spanning four tiles into all four")
val grid = tile_grid_make(0, 0, 1024, 1024)
val ops = [_box(0, 200, 200, 112, 112)]
val bins = tile_bin_ops(ops, grid)
expect(_bin_count(bins, 0)).to_equal(1)
expect(_bin_count(bins, 1)).to_equal(1)
expect(_bin_count(bins, 4)).to_equal(1)
expect(_bin_count(bins, 5)).to_equal(1)
expect(_bin_count(bins, 2)).to_equal(0)
```

</details>

#### keeps an exact tile-boundary rect inside one tile

- keeps an exact tile-boundary rect inside one tile
   - Expected: _bin_count(bins, 5) equals `1`
   - Expected: _bin_count(bins, 6) equals `0`
   - Expected: _bin_count(bins, 9) equals `0`
   - Expected: _bin_count(bins, 0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps an exact tile-boundary rect inside one tile")
val grid = tile_grid_make(0, 0, 1024, 1024)
# [256, 512) x [256, 512) is exactly tile (1, 1): the exclusive
# right/bottom edges must not leak into tiles (2, 1) / (1, 2).
val ops = [_box(0, 256, 256, 256, 256)]
val bins = tile_bin_ops(ops, grid)
expect(_bin_count(bins, 5)).to_equal(1)
expect(_bin_count(bins, 6)).to_equal(0)
expect(_bin_count(bins, 9)).to_equal(0)
expect(_bin_count(bins, 0)).to_equal(0)
```

</details>

#### drops hidden and zero-area ops at bin time

- drops hidden and zero-area ops at bin time
   - Expected: _bin_count(bins, 0) equals `1`
   - Expected: bins.items[bins.starts[0]] equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("drops hidden and zero-area ops at bin time")
val grid = tile_grid_make(0, 0, 512, 512)
val ops = [
    tile_op(0, 0, 10, 10, 100, 100, true, false, 7, -1),
    _box(1, 10, 10, 0, 100),
    _box(2, 10, 10, 100, 0),
    _box(3, 10, 10, 100, 100)
]
val bins = tile_bin_ops(ops, grid)
expect(_bin_count(bins, 0)).to_equal(1)
expect(bins.items[bins.starts[0]]).to_equal(3)
```

</details>

#### clamps negative-coordinate ops to the grid edge tiles

- clamps negative-coordinate ops to the grid edge tiles
   - Expected: _bin_count(bins, 0) equals `1`
   - Expected: bins.items[bins.starts[0]] equals `0`
   - Expected: _bin_count(bins, 1) equals `0`
   - Expected: _bin_count(bins, 2) equals `0`
   - Expected: _bin_count(bins, 3) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("clamps negative-coordinate ops to the grid edge tiles")
val grid = tile_grid_make(0, 0, 512, 512)
val ops = [_box(0, -100, -100, 200, 200), _box(1, -300, -300, 100, 100)]
val bins = tile_bin_ops(ops, grid)
# Op 0 straddles the origin: only tile (0,0) sees it. Op 1 is fully
# outside the document: binned nowhere.
expect(_bin_count(bins, 0)).to_equal(1)
expect(bins.items[bins.starts[0]]).to_equal(0)
expect(_bin_count(bins, 1)).to_equal(0)
expect(_bin_count(bins, 2)).to_equal(0)
expect(_bin_count(bins, 3)).to_equal(0)
```

</details>

#### reports no coverage for rects outside the grid

- reports no coverage for rects outside the grid
   - Expected: x1a < x0a is true
   - Expected: x1b < x0b is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports no coverage for rects outside the grid")
val grid = tile_grid_make(0, 0, 512, 512)
val (x0a, y0a, x1a, y1a) = tile_cover_range(grid, 600, 0, 50, 50)
expect(x1a < x0a).to_equal(true)
val (x0b, y0b, x1b, y1b) = tile_cover_range(grid, 0, 0, 0, 50)
expect(x1b < x0b).to_equal(true)
```

</details>

#### preserves op order inside a tile bin

- preserves op order inside a tile bin
   - Expected: _bin_count(bins, 0) equals `3`
   - Expected: bins.items[bins.starts[0]] equals `0`
   - Expected: bins.items[bins.starts[0] + 1] equals `1`
   - Expected: bins.items[bins.starts[0] + 2] equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("preserves op order inside a tile bin")
val grid = tile_grid_make(0, 0, 512, 512)
val ops = [_box(0, 0, 0, 64, 64), _box(1, 32, 32, 64, 64), _box(2, 16, 16, 64, 64)]
val bins = tile_bin_ops(ops, grid)
expect(_bin_count(bins, 0)).to_equal(3)
expect(bins.items[bins.starts[0]]).to_equal(0)
expect(bins.items[bins.starts[0] + 1]).to_equal(1)
expect(bins.items[bins.starts[0] + 2]).to_equal(2)
```

</details>

### tile checksums

#### is stable for identical op lists and sensitive to changes

- is stable for identical op lists and sensitive to changes
   - Expected: tile_checksum(ops_a, bins_a, 0) equals `tile_checksum(ops_b, bins_b, 0)`
   - Expected: tile_checksum(ops_a, bins_a, 3) equals `tile_checksum(ops_b, bins_b, 3)`
   - Expected: tile_checksum(ops_c, bins_c, 0) equals `tile_checksum(ops_a, bins_a, 0)`
   - Expected: tile_checksum(ops_c, bins_c, 3) != tile_checksum(ops_a, bins_a, 3) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("is stable for identical op lists and sensitive to changes")
val grid = tile_grid_make(0, 0, 512, 512)
val ops_a = [_box(0, 0, 0, 64, 64), _box(1, 300, 300, 64, 64)]
val ops_b = [_box(0, 0, 0, 64, 64), _box(1, 300, 300, 64, 64)]
val bins_a = tile_bin_ops(ops_a, grid)
val bins_b = tile_bin_ops(ops_b, grid)
expect(tile_checksum(ops_a, bins_a, 0)).to_equal(tile_checksum(ops_b, bins_b, 0))
expect(tile_checksum(ops_a, bins_a, 3)).to_equal(tile_checksum(ops_b, bins_b, 3))
# Moving the op in tile 3 changes only tile 3's checksum.
val ops_c = [_box(0, 0, 0, 64, 64), _box(1, 301, 300, 64, 64)]
val bins_c = tile_bin_ops(ops_c, grid)
expect(tile_checksum(ops_c, bins_c, 0)).to_equal(tile_checksum(ops_a, bins_a, 0))
expect(tile_checksum(ops_c, bins_c, 3) != tile_checksum(ops_a, bins_a, 3)).to_equal(true)
```

</details>

#### computes per-tile checksum arrays with a shared empty value

- computes per-tile checksum arrays with a shared empty value
   - Expected: sums.len() equals `4`
   - Expected: sums[1] equals `sums[2]`
   - Expected: sums[0] != sums[1] is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("computes per-tile checksum arrays with a shared empty value")
val grid = tile_grid_make(0, 0, 512, 512)
val ops = [_box(0, 0, 0, 64, 64)]
val sums = tile_checksums(ops, tile_bin_ops(ops, grid), grid)
expect(sums.len()).to_equal(4)
expect(sums[1]).to_equal(sums[2])
expect(sums[0] != sums[1]).to_equal(true)
```

</details>

### tile live set from scroll

#### marks viewport plus 512px margin tiles live

- marks viewport plus 512px margin tiles live
   - Expected: live[8 * 4] is true
   - Expected: live[9 * 4 + 3] is true
   - Expected: live[6 * 4] is true
   - Expected: live[11 * 4 + 3] is true
   - Expected: live[5 * 4] is false
   - Expected: live[12 * 4] is false
   - Expected: live[0] is false
   - Expected: live[15 * 4 + 3] is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("marks viewport plus 512px margin tiles live")
# Document 1024 x 4096 = 4 x 16 tiles; viewport 1024x512 at scroll 2048.
val grid = tile_grid_make(0, 0, 1024, 4096)
val live = tile_live_set(grid, 0, 2048, 1024, 512, TILE_MARGIN_PX)
# Rows 8..9 are the viewport; margin extends to rows 6..11.
expect(live[8 * 4]).to_equal(true)
expect(live[9 * 4 + 3]).to_equal(true)
expect(live[6 * 4]).to_equal(true)
expect(live[11 * 4 + 3]).to_equal(true)
expect(live[5 * 4]).to_equal(false)
expect(live[12 * 4]).to_equal(false)
expect(live[0]).to_equal(false)
expect(live[15 * 4 + 3]).to_equal(false)
```

</details>

#### marks everything live at scroll zero on a short document

- marks everything live at scroll zero on a short document
   - Expected: all_live is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("marks everything live at scroll zero on a short document")
val grid = tile_grid_make(0, 0, 512, 512)
val live = tile_live_set(grid, 0, 0, 512, 512, TILE_MARGIN_PX)
var t = 0
var all_live = true
while t < tile_count(grid):
    if not live[t]:
        all_live = false
    t = t + 1
expect(all_live).to_equal(true)
```

</details>

### tile occlusion

#### lets a full 8K opaque viewport occlude the ragged last tile

- lets a full 8K opaque viewport occlude the ragged last tile
   - Expected: survivors equals `[false, true]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("lets a full 8K opaque viewport occlude the ragged last tile")
val grid = tile_grid_make(0, 0, 7680, 4320)
val ops = [
    _box(0, 7500, 4200, 20, 20),
    _opaque(1, 0, 0, 7680, 4320),
]
val bins = tile_bin_ops(ops, grid)
expect(tile_occluder_slot(ops, bins, grid, 509)).to_equal(
    bins.starts[509] + 1)
val live = tile_live_set(grid, 0, 0, 7680, 4320, 0)
val survivors = tile_survivors(ops, bins, grid, live)
expect(survivors).to_equal([false, true])
```

</details>

#### finds the latest full-tile opaque op as the occluder

- finds the latest full-tile opaque op as the occluder
   - Expected: tile_occluder_slot(ops, bins, grid, 0) equals `bins.starts[0] + 1`
   - Expected: tile_occluder_slot(ops, bins, grid, 1) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("finds the latest full-tile opaque op as the occluder")
val grid = tile_grid_make(0, 0, 512, 512)
val ops = [
    _box(0, 0, 0, 100, 100),
    _opaque(1, 0, 0, 256, 256),
    _box(2, 10, 10, 50, 50)
]
val bins = tile_bin_ops(ops, grid)
expect(tile_occluder_slot(ops, bins, grid, 0)).to_equal(bins.starts[0] + 1)
expect(tile_occluder_slot(ops, bins, grid, 1)).to_equal(-1)
```

</details>

#### does not treat a partial-coverage opaque op as an occluder

- does not treat a partial-coverage opaque op as an occluder
   - Expected: tile_occluder_slot(ops, bins, grid, 0) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("does not treat a partial-coverage opaque op as an occluder")
val grid = tile_grid_make(0, 0, 512, 512)
val ops = [_box(0, 0, 0, 100, 100), _opaque(1, 0, 0, 255, 256)]
val bins = tile_bin_ops(ops, grid)
expect(tile_occluder_slot(ops, bins, grid, 0)).to_equal(-1)
```

</details>

#### culls ops behind a full-tile opaque op but keeps later ops

- culls ops behind a full-tile opaque op but keeps later ops
   - Expected: surv[0] is false
   - Expected: surv[1] is true
   - Expected: surv[2] is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("culls ops behind a full-tile opaque op but keeps later ops")
val grid = tile_grid_make(0, 0, 512, 512)
val ops = [
    _box(0, 0, 0, 100, 100),
    _opaque(1, 0, 0, 256, 256),
    _box(2, 10, 10, 50, 50)
]
val bins = tile_bin_ops(ops, grid)
val live = tile_live_set(grid, 0, 0, 512, 512, 0)
val surv = tile_survivors(ops, bins, grid, live)
expect(surv[0]).to_equal(false)
expect(surv[1]).to_equal(true)
expect(surv[2]).to_equal(true)
```

</details>

#### keeps an occluded op alive when another live tile still shows it

- keeps an occluded op alive when another live tile still shows it
   - Expected: surv[0] is true
   - Expected: surv[1] is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps an occluded op alive when another live tile still shows it")
val grid = tile_grid_make(0, 0, 512, 512)
# Op 0 spans tiles (0,0) and (1,0); the occluder covers only (0,0).
val ops = [_box(0, 0, 0, 400, 100), _opaque(1, 0, 0, 256, 256)]
val bins = tile_bin_ops(ops, grid)
val live = tile_live_set(grid, 0, 0, 512, 512, 0)
val surv = tile_survivors(ops, bins, grid, live)
expect(surv[0]).to_equal(true)
expect(surv[1]).to_equal(true)
```

</details>

#### culls ops binned only in non-live tiles

- culls ops binned only in non-live tiles
   - Expected: surv[0] is true
   - Expected: surv[1] is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("culls ops binned only in non-live tiles")
val grid = tile_grid_make(0, 0, 1024, 4096)
val ops = [_box(0, 0, 0, 100, 100), _box(1, 0, 3800, 100, 100)]
val bins = tile_bin_ops(ops, grid)
# Viewport at the top, no margin: the bottom-of-document op is dead.
val live = tile_live_set(grid, 0, 0, 1024, 512, 0)
val surv = tile_survivors(ops, bins, grid, live)
expect(surv[0]).to_equal(true)
expect(surv[1]).to_equal(false)
```

</details>

### tile flag and counters

#### defaults the tile paint flag to off

- defaults the tile paint flag to off
   - Expected: tile_paint_flag_enabled() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("defaults the tile paint flag to off")
# The suite never sets SIMPLE_WEB_TILE_PAINT; default must be OFF so
# the flag-off render path stays byte-identical.
expect(tile_paint_flag_enabled()).to_equal(false)
```

</details>

#### records and exposes benchmark counters

- records and exposes benchmark counters
   - Expected: tile_stats_ops_total() equals `100`
   - Expected: tile_stats_ops_painted() equals `25`
   - Expected: tile_stats_tiles_total() equals `64`
   - Expected: tile_stats_tiles_live() equals `12`
   - Expected: tile_stats_tiles_skipped() equals `52`
   - Expected: tile_stats_tiles_occluded() equals `3`
   - Expected: tile_stats_ops_total() equals `0`
   - Expected: tile_stats_tiles_skipped() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("records and exposes benchmark counters")
tile_stats_record(100, 25, 64, 12, 52, 3)
expect(tile_stats_ops_total()).to_equal(100)
expect(tile_stats_ops_painted()).to_equal(25)
expect(tile_stats_tiles_total()).to_equal(64)
expect(tile_stats_tiles_live()).to_equal(12)
expect(tile_stats_tiles_skipped()).to_equal(52)
expect(tile_stats_tiles_occluded()).to_equal(3)
tile_stats_reset()
expect(tile_stats_ops_total()).to_equal(0)
expect(tile_stats_tiles_skipped()).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `37624336fe602b1930ab5a3479df85ddb838c9dd18dd44a9b217d90903b6bcd1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `37624336fe602b1930ab5a3479df85ddb838c9dd18dd44a9b217d90903b6bcd1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `37624336fe602b1930ab5a3479df85ddb838c9dd18dd44a9b217d90903b6bcd1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/tile_grid_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/tile_grid_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/tile_grid_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/tile_grid_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/tile_grid_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 58 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/tile_grid_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'floor-divides negative coordinates toward negative infinity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/tile_grid_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sizes the grid from a document rect' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/tile_grid_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns an empty grid for a degenerate document rect' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
