# model3d gen heightmap

> `simple model3d gen heightmap --seed N --w W --d D --out scene.sdn` samples seeded `fbm2` per column and emits one box node per column (height -> `size.y`, `center.y = h/2`, color banded by height). The output is ordinary box-node scene SDN — it loads and renders through the existing `model3d inspect`/`render` commands unchanged, with zero new loader code.

<!-- sdn-diagram:id=scene_gen_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scene_gen_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scene_gen_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scene_gen_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# model3d gen heightmap

`simple model3d gen heightmap --seed N --w W --d D --out scene.sdn` samples seeded `fbm2` per column and emits one box node per column (height -> `size.y`, `center.y = h/2`, color banded by height). The output is ordinary box-node scene SDN — it loads and renders through the existing `model3d inspect`/`render` commands unchanged, with zero new loader code.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #scene-map-gen-heightmap |
| Category | App / CLI Surface |
| Status | Implemented |
| Source | `test/02_integration/app/game_tools/scene_gen_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`simple model3d gen heightmap --seed N --w W --d D --out scene.sdn` samples
seeded `fbm2` per column and emits one box node per column (height ->
`size.y`, `center.y = h/2`, color banded by height). The output is ordinary
box-node scene SDN — it loads and renders through the existing `model3d
inspect`/`render` commands unchanged, with zero new loader code.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Node count | Exactly `W * D` — one box per grid column |
| Determinism | Two `gen heightmap` runs with the same seed produce byte-identical SDN files |
| Roundtrip | Generated SDN passes `model3d inspect` (exit 0) and `model3d render` (exit 0) unchanged |

## Scenarios

### gen heightmap

#### emits SDN that model3d inspect accepts, with node count == W*D

- Generate a 5x4 heightmap via the CLI
- mkdir p
   - Expected: r.exit_code equals `0`
- assert true
- Then model3d inspect accepts it and reports 20 nodes
   - Expected: ir.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Generate a 5x4 heightmap via the CLI")
mkdir_p(OUT_DIR)
val out = OUT_DIR + "/heightmap_probe.sdn"
val r = run_cli("gen heightmap --seed 7 --w 5 --d 4 --out {out}")
expect(r.exit_code).to_equal(0)
assert_true(file_exists(out))

step("Then model3d inspect accepts it and reports 20 nodes")
val ir = run_cli("inspect {out}")
expect(ir.exit_code).to_equal(0)
expect(ir.stdout).to_contain("nodes: 20")
```

</details>

#### passes model3d render unchanged

- Generate a 5x4 heightmap via the CLI
- mkdir p
   - Expected: r.exit_code equals `0`
- Then model3d render produces a PPM for it
   - Expected: rr.exit_code equals `0`
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Generate a 5x4 heightmap via the CLI")
mkdir_p(OUT_DIR)
val out = OUT_DIR + "/heightmap_render.sdn"
val r = run_cli("gen heightmap --seed 7 --w 5 --d 4 --out {out}")
expect(r.exit_code).to_equal(0)

step("Then model3d render produces a PPM for it")
val ppm = OUT_DIR + "/heightmap_render.ppm"
val rr = run_cli("render {out} --out {ppm} --width 32 --height 24")
expect(rr.exit_code).to_equal(0)
assert_true(file_exists(ppm))
val body = file_read(ppm)
expect(body).to_start_with("P3")
```

</details>

#### is byte-identical for the same seed

- Generate the same heightmap twice
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
step("Generate the same heightmap twice")
mkdir_p(OUT_DIR)
val out_a = OUT_DIR + "/heightmap_det_a.sdn"
val out_b = OUT_DIR + "/heightmap_det_b.sdn"
val ra = run_cli("gen heightmap --seed 11 --w 6 --d 5 --out {out_a}")
val rb = run_cli("gen heightmap --seed 11 --w 6 --d 5 --out {out_b}")
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

- Generate heightmaps from two different seeds at the same size
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
step("Generate heightmaps from two different seeds at the same size")
mkdir_p(OUT_DIR)
val out_a = OUT_DIR + "/heightmap_seed_a.sdn"
val out_b = OUT_DIR + "/heightmap_seed_b.sdn"
val ra = run_cli("gen heightmap --seed 1 --w 6 --d 5 --out {out_a}")
val rb = run_cli("gen heightmap --seed 2 --w 6 --d 5 --out {out_b}")
expect(ra.exit_code).to_equal(0)
expect(rb.exit_code).to_equal(0)

step("Then the two SDN files hash differently")
val ha = file_hash_sha256(out_a)
val hb = file_hash_sha256(out_b)
assert_not_equal(ha, hb)
```

</details>

### gen heightmap usage errors

#### exits 2 when --seed is missing

- Run gen heightmap without --seed
   - Expected: r.exit_code equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run gen heightmap without --seed")
val r = run_cli("gen heightmap --w 4 --d 4 --out " + OUT_DIR + "/never.sdn")
expect(r.exit_code).to_equal(2)
expect(r.stdout).to_contain("missing --seed")
```

</details>

#### exits 2 when --w/--d are not positive

- Run gen heightmap with --w 0
   - Expected: r.exit_code equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run gen heightmap with --w 0")
val r = run_cli("gen heightmap --seed 1 --w 0 --d 4 --out " + OUT_DIR + "/never.sdn")
expect(r.exit_code).to_equal(2)
expect(r.stdout).to_contain("must be positive integers")
```

</details>

#### exits 2 on an unknown gen mode

- Run gen with a bogus mode
   - Expected: r.exit_code equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run gen with a bogus mode")
val r = run_cli("gen frobnicate --seed 1 --out " + OUT_DIR + "/never.sdn")
expect(r.exit_code).to_equal(2)
expect(r.stdout).to_contain("unknown gen mode: frobnicate")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
