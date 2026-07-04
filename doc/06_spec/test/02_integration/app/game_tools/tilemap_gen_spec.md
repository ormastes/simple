# Cellular-Automata Cave Generation

> `std.common.cave_ca` generates seeded cellular-automata caves (the "4-5 rule": a cell becomes wall with more than 4 wall neighbors, floor with fewer than 4, else unchanged) over a `[[i32]]` grid (1 = wall, 0 = floor). It is deterministic (same seed, same output) and uses `random_pure`'s explicit-state `LcgRng` for its initial random fill — not noise.spl's position-pure gradient noise, and not random_pure's shared-state module functions (call order matters for a scatter/dice generator).

<!-- sdn-diagram:id=tilemap_gen_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tilemap_gen_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tilemap_gen_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tilemap_gen_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cellular-Automata Cave Generation

`std.common.cave_ca` generates seeded cellular-automata caves (the "4-5 rule": a cell becomes wall with more than 4 wall neighbors, floor with fewer than 4, else unchanged) over a `[[i32]]` grid (1 = wall, 0 = floor). It is deterministic (same seed, same output) and uses `random_pure`'s explicit-state `LcgRng` for its initial random fill — not noise.spl's position-pure gradient noise, and not random_pure's shared-state module functions (call order matters for a scatter/dice generator).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #scene-map-gen-tilemap |
| Category | App / Procedural Generation |
| Status | Implemented |
| Source | `test/02_integration/app/game_tools/tilemap_gen_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`std.common.cave_ca` generates seeded cellular-automata caves (the "4-5
rule": a cell becomes wall with more than 4 wall neighbors, floor with fewer
than 4, else unchanged) over a `[[i32]]` grid (1 = wall, 0 = floor). It is
deterministic (same seed, same output) and uses `random_pure`'s
explicit-state `LcgRng` for its initial random fill — not noise.spl's
position-pure gradient noise, and not random_pure's shared-state module
functions (call order matters for a scatter/dice generator).

`simple model3d gen tilemap --seed N --w W --h H --out map.sdn` runs the
same generator through the CLI and emits a `tilemap: { cols, rows, cells }`
SDN file.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Fixpoint | `ca_generate` iterates `ca_step` until an extra pass changes 0 cells |
| No isolated cell | At a fixpoint, no wall cell has 0 wall neighbors and no floor cell has 8 wall neighbors (both would flip) |
| Floor reachability | `ca_floor_reachable` flood-fills from one floor cell; true iff it reaches every floor cell |
| Determinism | Two `gen tilemap` runs with the same seed produce byte-identical SDN files |

## Scenarios

### CA cave gen

#### reaches a fixpoint: extra iteration changes 0 cells

- Generate the pinned reference cave
- Then applying one more CA step changes nothing
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Generate the pinned reference cave")
val cave = ca_generate(SEED, COLS, ROWS, FILL_PROB, MAX_ITERS)

step("Then applying one more CA step changes nothing")
val stepped = ca_step(cave)
assert_true(_grids_equal(cave, stepped))
```

</details>

#### has no isolated single-cell wall or floor

- Generate the pinned reference cave
- Then no cell in the whole grid violates the 4-5 neighborhood invariant
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Generate the pinned reference cave")
val cave = ca_generate(SEED, COLS, ROWS, FILL_PROB, MAX_ITERS)

step("Then no cell in the whole grid violates the 4-5 neighborhood invariant")
assert_true(_no_isolated_cell(cave))
```

</details>

#### keeps all floor reachable

- Generate the pinned reference cave
- Then a flood fill from any floor cell reaches every floor cell
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Generate the pinned reference cave")
val cave = ca_generate(SEED, COLS, ROWS, FILL_PROB, MAX_ITERS)

step("Then a flood fill from any floor cell reaches every floor cell")
assert_true(ca_floor_reachable(cave))
```

</details>

#### is seed-deterministic: same seed always yields the same grid

- Generate the pinned reference cave twice from the same seed
- Then the two grids are cell-for-cell identical
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Generate the pinned reference cave twice from the same seed")
val a = ca_generate(SEED, COLS, ROWS, FILL_PROB, MAX_ITERS)
val b = ca_generate(SEED, COLS, ROWS, FILL_PROB, MAX_ITERS)

step("Then the two grids are cell-for-cell identical")
assert_true(_grids_equal(a, b))
```

</details>

#### diverges across seeds

- Generate caves from two different seeds at the same size
- Then the two grids are not cell-for-cell identical
- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Generate caves from two different seeds at the same size")
val a = ca_generate(1, COLS, ROWS, FILL_PROB, MAX_ITERS)
val b = ca_generate(99, COLS, ROWS, FILL_PROB, MAX_ITERS)

step("Then the two grids are not cell-for-cell identical")
assert_false(_grids_equal(a, b))
```

</details>

### model3d gen tilemap CLI

#### emits a tilemap SDN with the requested dimensions

- Generate a 24x18 tilemap via the CLI
- mkdir p
   - Expected: r.exit_code equals `0`
- assert true
- Then the SDN declares the tilemap block with matching cols/rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Generate a 24x18 tilemap via the CLI")
mkdir_p(OUT_DIR)
val out = OUT_DIR + "/tilemap_probe.sdn"
val r = run_cli("gen tilemap --seed {SEED} --w {COLS} --h {ROWS} --out {out}")
expect(r.exit_code).to_equal(0)
assert_true(file_exists(out))

step("Then the SDN declares the tilemap block with matching cols/rows")
val body = file_read(out)
expect(body).to_contain("tilemap:")
expect(body).to_contain("cols: 24")
expect(body).to_contain("rows: 18")
```

</details>

#### is byte-identical for the same seed

- Generate the same tilemap twice
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
step("Generate the same tilemap twice")
mkdir_p(OUT_DIR)
val out_a = OUT_DIR + "/tilemap_det_a.sdn"
val out_b = OUT_DIR + "/tilemap_det_b.sdn"
val ra = run_cli("gen tilemap --seed 5 --w 20 --h 15 --out " + out_a)
val rb = run_cli("gen tilemap --seed 5 --w 20 --h 15 --out " + out_b)
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

- Generate tilemaps from two different seeds
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
step("Generate tilemaps from two different seeds")
mkdir_p(OUT_DIR)
val out_a = OUT_DIR + "/tilemap_seed_a.sdn"
val out_b = OUT_DIR + "/tilemap_seed_b.sdn"
val ra = run_cli("gen tilemap --seed 1 --w 20 --h 15 --out " + out_a)
val rb = run_cli("gen tilemap --seed 2 --w 20 --h 15 --out " + out_b)
expect(ra.exit_code).to_equal(0)
expect(rb.exit_code).to_equal(0)

step("Then the two SDN files hash differently")
val ha = file_hash_sha256(out_a)
val hb = file_hash_sha256(out_b)
assert_not_equal(ha, hb)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
