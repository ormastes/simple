# Tiled-Model Wave Function Collapse Generation

> `std.common.wfc` generates a seeded tiled-model Wave Function Collapse (WFC) map: a small tile set with per-side (N/E/S/W) adjacency rules collapses, lowest-entropy cell first, into a `[[i32]]` grid of tile ids. On a contradiction (a cell filtered to zero remaining possibilities) generation restarts from a seed deterministically derived from the original seed, up to a bounded number of restarts, then reports `Err` — it never hangs.

<!-- sdn-diagram:id=wfc_gen_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wfc_gen_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wfc_gen_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wfc_gen_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tiled-Model Wave Function Collapse Generation

`std.common.wfc` generates a seeded tiled-model Wave Function Collapse (WFC) map: a small tile set with per-side (N/E/S/W) adjacency rules collapses, lowest-entropy cell first, into a `[[i32]]` grid of tile ids. On a contradiction (a cell filtered to zero remaining possibilities) generation restarts from a seed deterministically derived from the original seed, up to a bounded number of restarts, then reports `Err` — it never hangs.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #scene-map-gen-wfc |
| Category | App / Procedural Generation |
| Status | Implemented |
| Source | `test/02_integration/app/game_tools/wfc_gen_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`std.common.wfc` generates a seeded tiled-model Wave Function Collapse (WFC)
map: a small tile set with per-side (N/E/S/W) adjacency rules collapses,
lowest-entropy cell first, into a `[[i32]]` grid of tile ids. On a
contradiction (a cell filtered to zero remaining possibilities) generation
restarts from a seed deterministically derived from the original seed, up to
a bounded number of restarts, then reports `Err` — it never hangs.

A built-in grass/water/coast demo tileset ships for the CLI default (coast
mediates grass<->water, so the two are never directly adjacent); rules are
overridable via an SDN tileset file.

`simple model3d gen wfc --seed N --w W --h H [--tileset file.sdn] --out
map.sdn` runs the generator through the CLI and emits the exact same
`tilemap: { cols, rows, cells }` SDN shape `gen tilemap` does (loadable
identically).

## Key Concepts

| Concept | Description |
|---------|-------------|
| Lowest-entropy collapse | Each step picks the uncollapsed cell with fewest remaining tile possibilities |
| Arc-consistency propagation | After each collapse, neighbor possibility lists are filtered to only tiles compatible in both directions |
| Contradiction / restart | A cell filtered to 0 possibilities restarts generation from a derived seed (bounded), then `Err` |
| Determinism | Two `gen wfc` runs with the same seed produce byte-identical SDN files |

## Scenarios

### WFC generate

#### has zero adjacency rule violations across the whole map (THE oracle)

- Generate a 16x12 map from the demo tileset
- Then an independent whole-grid adjacency scan finds no violation
- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Generate a 16x12 map from the demo tileset")
val tileset = demo_tileset()
val cells = _unwrap_cells(wfc_generate(tileset, W, H, SEED))

step("Then an independent whole-grid adjacency scan finds no violation")
assert_false(_grid_has_violation(tileset, cells, W, H))
```

</details>

#### is seed-deterministic: same seed always yields the same grid

- Generate the same map twice from the same seed
- Then the two grids are cell-for-cell identical
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Generate the same map twice from the same seed")
val tileset = demo_tileset()
val a = _unwrap_cells(wfc_generate(tileset, W, H, SEED))
val b = _unwrap_cells(wfc_generate(tileset, W, H, SEED))

step("Then the two grids are cell-for-cell identical")
assert_true(_cells_equal(a, b))
```

</details>

#### diverges across seeds

- Generate maps from two different seeds at the same size
- Then the two grids are not cell-for-cell identical
- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Generate maps from two different seeds at the same size")
val tileset = demo_tileset()
val a = _unwrap_cells(wfc_generate(tileset, W, H, 1))
val b = _unwrap_cells(wfc_generate(tileset, W, H, 2))

step("Then the two grids are not cell-for-cell identical")
assert_false(_cells_equal(a, b))
```

</details>

#### never emits grass adjacent to water in the demo tileset

- Generate several maps from different seeds
- Then none of them ever place grass next to water
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Generate several maps from different seeds")
val tileset = demo_tileset()
val a = _unwrap_cells(wfc_generate(tileset, W, H, 10))
val b = _unwrap_cells(wfc_generate(tileset, W, H, 11))
val c = _unwrap_cells(wfc_generate(tileset, W, H, 12))

step("Then none of them ever place grass next to water")
val all_ok = (_no_grass_water_adjacent(a, W, H) and _no_grass_water_adjacent(b, W, H) and _no_grass_water_adjacent(c, W, H))
assert_true(all_ok)
```

</details>

#### returns Err (not a hang) for a contradiction tileset

- Build a single-tile ruleset that disallows itself as a neighbor in every direction
- Then generating even a tiny 2x1 map cleanly fails, no restart hang
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build a single-tile ruleset that disallows itself as a neighbor in every direction")
val solo = Tile(id: 0, name: "solo", n: [], e: [], s: [], w: [])
val impossible = TileSet(tiles: [solo])

step("Then generating even a tiny 2x1 map cleanly fails, no restart hang")
val r = wfc_generate(impossible, 2, 1, 1)
assert_true(_is_err(r))
```

</details>

### model3d gen wfc CLI

#### emits a tilemap SDN with the requested dimensions

- Generate a 16x12 WFC map via the CLI
- mkdir p
   - Expected: r.exit_code equals `0`
- assert true
- Then the SDN declares the tilemap block with matching cols/rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Generate a 16x12 WFC map via the CLI")
mkdir_p(OUT_DIR)
val out = OUT_DIR + "/wfc_probe.sdn"
val r = run_cli("gen wfc --seed {SEED} --w {W} --h {H} --out {out}")
expect(r.exit_code).to_equal(0)
assert_true(file_exists(out))

step("Then the SDN declares the tilemap block with matching cols/rows")
val body = file_read(out)
expect(body).to_contain("tilemap:")
expect(body).to_contain("cols: 16")
expect(body).to_contain("rows: 12")
```

</details>

#### is byte-identical for the same seed

- Generate the same WFC map twice
- mkdir p
   - Expected: ra.exit_code equals `0`
   - Expected: rb.exit_code equals `0`
- Then both SDN files hash identically
   - Expected: ha equals `hb`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Generate the same WFC map twice")
mkdir_p(OUT_DIR)
val out_a = OUT_DIR + "/wfc_det_a.sdn"
val out_b = OUT_DIR + "/wfc_det_b.sdn"
val ra = run_cli("gen wfc --seed 7 --w 12 --h 10 --out " + out_a)
val rb = run_cli("gen wfc --seed 7 --w 12 --h 10 --out " + out_b)
expect(ra.exit_code).to_equal(0)
expect(rb.exit_code).to_equal(0)

step("Then both SDN files hash identically")
val ha = file_hash_sha256(out_a)
val hb = file_hash_sha256(out_b)
expect(ha.len()).to_be_greater_than(0)
expect(ha).to_equal(hb)
```

</details>

#### differs across seeds

- Generate WFC maps from two different seeds
- mkdir p
   - Expected: ra.exit_code equals `0`
   - Expected: rb.exit_code equals `0`
- Then the two SDN files hash differently
- assert not equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Generate WFC maps from two different seeds")
mkdir_p(OUT_DIR)
val out_a = OUT_DIR + "/wfc_seed_a.sdn"
val out_b = OUT_DIR + "/wfc_seed_b.sdn"
val ra = run_cli("gen wfc --seed 1 --w 12 --h 10 --out " + out_a)
val rb = run_cli("gen wfc --seed 2 --w 12 --h 10 --out " + out_b)
expect(ra.exit_code).to_equal(0)
expect(rb.exit_code).to_equal(0)

step("Then the two SDN files hash differently")
val ha = file_hash_sha256(out_a)
val hb = file_hash_sha256(out_b)
assert_not_equal(ha, hb)
```

</details>

#### exits 1 (not a hang) for a contradiction tileset file

- Write a single-tile ruleset that disallows itself as a neighbor
- mkdir p
- write file
- Then `gen wfc` against it exits 1 cleanly instead of hanging
   - Expected: r.exit_code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Write a single-tile ruleset that disallows itself as a neighbor")
mkdir_p(OUT_DIR)
val tileset_path = OUT_DIR + "/wfc_impossible_tileset.sdn"
write_file(tileset_path, "tileset:\n  tiles: [{ id: 0, name: \"solo\", n: [], e: [], s: [], w: [] }]\n")

step("Then `gen wfc` against it exits 1 cleanly instead of hanging")
val out = OUT_DIR + "/wfc_impossible_out.sdn"
val r = run_cli("gen wfc --seed 1 --w 2 --h 1 --tileset {tileset_path} --out {out}")
expect(r.exit_code).to_equal(1)
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
