# Tiled-Model Wave Function Collapse Generation

> `std.common.wfc` generates a seeded tiled-model Wave Function Collapse (WFC) map: a small tile set with per-side (N/E/S/W) adjacency rules collapses, lowest-entropy cell first, into a `[[i32]]` grid of tile ids. On a contradiction (a cell filtered to zero remaining possibilities) generation restarts from a seed deterministically derived from the original seed, up to a bounded number of restarts, then reports `Err` — it never hangs.

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
| Updated | 2026-08-26 |
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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- has zero adjacency rule violations across the whole map (THE oracle)
- Generate a 16x12 map from the demo tileset
- Then an independent whole-grid adjacency scan finds no violation


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("has zero adjacency rule violations across the whole map (THE oracle)")
step("Generate a 16x12 map from the demo tileset")
val tileset = demo_tileset()
val cells = _unwrap_cells(wfc_generate(tileset, W, H, SEED))

step("Then an independent whole-grid adjacency scan finds no violation")
assert_false(_grid_has_violation(tileset, cells, W, H))
```

</details>

#### is seed-deterministic: same seed always yields the same grid

- is seed-deterministic: same seed always yields the same grid
- Generate the same map twice from the same seed
- Then the two grids are cell-for-cell identical


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("is seed-deterministic: same seed always yields the same grid")
step("Generate the same map twice from the same seed")
val tileset = demo_tileset()
val a = _unwrap_cells(wfc_generate(tileset, W, H, SEED))
val b = _unwrap_cells(wfc_generate(tileset, W, H, SEED))

step("Then the two grids are cell-for-cell identical")
assert_true(_cells_equal(a, b))
```

</details>

#### diverges across seeds

- diverges across seeds
- Generate maps from two different seeds at the same size
- Then the two grids are not cell-for-cell identical


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("diverges across seeds")
step("Generate maps from two different seeds at the same size")
val tileset = demo_tileset()
val a = _unwrap_cells(wfc_generate(tileset, W, H, 1))
val b = _unwrap_cells(wfc_generate(tileset, W, H, 2))

step("Then the two grids are not cell-for-cell identical")
assert_false(_cells_equal(a, b))
```

</details>

#### never emits grass adjacent to water in the demo tileset

- never emits grass adjacent to water in the demo tileset
- Generate several maps from different seeds
- Then none of them ever place grass next to water


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("never emits grass adjacent to water in the demo tileset")
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

- returns Err (not a hang) for a contradiction tileset
- Build a single-tile ruleset that disallows itself as a neighbor in every direction
- Then generating even a tiny 2x1 map cleanly fails, no restart hang


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("returns Err (not a hang) for a contradiction tileset")
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

- emits a tilemap SDN with the requested dimensions
- Generate a 16x12 WFC map via the CLI
   - Expected: r.exit_code equals `0`
- Then the SDN declares the tilemap block with matching cols/rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("emits a tilemap SDN with the requested dimensions")
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

- is byte-identical for the same seed
- Generate the same WFC map twice
   - Expected: ra.exit_code equals `0`
   - Expected: rb.exit_code equals `0`
- Then both SDN files hash identically
   - Expected: ha equals `hb`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("is byte-identical for the same seed")
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

- differs across seeds
- Generate WFC maps from two different seeds
   - Expected: ra.exit_code equals `0`
   - Expected: rb.exit_code equals `0`
- Then the two SDN files hash differently


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("differs across seeds")
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

- exits 1 (not a hang) for a contradiction tileset file
- Write a single-tile ruleset that disallows itself as a neighbor
- Then `gen wfc` against it exits 1 cleanly instead of hanging
   - Expected: r.exit_code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("exits 1 (not a hang) for a contradiction tileset file")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `61e0e2135984d4cd793cbcf4ffcb839682bee8114ce5741dcbdbce9bb3c53e0d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `61e0e2135984d4cd793cbcf4ffcb839682bee8114ce5741dcbdbce9bb3c53e0d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `61e0e2135984d4cd793cbcf4ffcb839682bee8114ce5741dcbdbce9bb3c53e0d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/02_integration/app/game_tools/wfc_gen_spec.spl
mirror: doc/06_spec/02_integration/app/game_tools/wfc_gen_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/app/game_tools/wfc_gen_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/app/game_tools/wfc_gen_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/app/game_tools/wfc_gen_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/app/game_tools/wfc_gen_spec.spl:151:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has zero adjacency rule violations across the whole map (THE oracle)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/game_tools/wfc_gen_spec.spl:161:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is seed-deterministic: same seed always yields the same grid' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/game_tools/wfc_gen_spec.spl:172:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'diverges across seeds' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
