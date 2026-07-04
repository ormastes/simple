# model3d CLI

> `simple model3d` is the production CLI over the engine3d software raster: `inspect` validates a 3D scene description (SDN) and prints the node tree, mesh/vertex counts, materials, and bounds; `render` rasterizes the scene headless to a P3 PPM. Scene files are a trust boundary — malformed input must produce a clean, path-qualified error and exit code 1, never a crash.

<!-- sdn-diagram:id=model3d_cli_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=model3d_cli_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

model3d_cli_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=model3d_cli_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# model3d CLI

`simple model3d` is the production CLI over the engine3d software raster: `inspect` validates a 3D scene description (SDN) and prints the node tree, mesh/vertex counts, materials, and bounds; `render` rasterizes the scene headless to a P3 PPM. Scene files are a trust boundary — malformed input must produce a clean, path-qualified error and exit code 1, never a crash.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #model3d-cli |
| Category | App / CLI Surface |
| Status | Implemented |
| Source | `test/02_integration/app/model3d/model3d_cli_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`simple model3d` is the production CLI over the engine3d software raster:
`inspect` validates a 3D scene description (SDN) and prints the node tree,
mesh/vertex counts, materials, and bounds; `render` rasterizes the scene
headless to a P3 PPM. Scene files are a trust boundary — malformed input must
produce a clean, path-qualified error and exit code 1, never a crash.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Scene SDN | `scene:` block with `name`, `background`, `camera`, `nodes` (inline array of box nodes) |
| Exit codes | 0 success, 1 failure (bad/missing scene, write failure), 2 usage error |
| Pixel oracle | Rendered PPM center pixel = object color; corner pixel = background color |
| Determinism | Two renders of the same scene are byte-identical |

## Scenarios

### model3d CLI inspect

#### prints the node tree, counts, materials and bounds for a valid scene

- Inspect the valid two-node fixture scene
   - Expected: r.exit_code equals `0`
- Then the scene header and camera are reported
- Then every node appears in the tree with mesh and material detail
- Then totals and world bounds are computed


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect the valid two-node fixture scene")
val r = run_cli("inspect " + VALID)
expect(r.exit_code).to_equal(0)

step("Then the scene header and camera are reported")
expect(r.stdout).to_contain("scene probe")
expect(r.stdout).to_contain("camera: eye=(0, 0, 6) target=(0, 0, 0) fov=60")
expect(r.stdout).to_contain("background: #203040")

step("Then every node appears in the tree with mesh and material detail")
expect(r.stdout).to_contain("nodes: 2")
expect(r.stdout).to_contain("+- cube  box  center=(0, 0, 0) size=(2, 2, 2)  material=unlit(#CC3020)  tris=12 verts=36")
expect(r.stdout).to_contain("+- floor  box  center=(0, -2.5, 0) size=(8, 0.5, 8)  material=unlit(#3060A0)  tris=12 verts=36")

step("Then totals and world bounds are computed")
expect(r.stdout).to_contain("totals: tris=24 verts=72")
expect(r.stdout).to_contain("bounds: min=(-4, -2.75, -4) max=(4, 1, 4)")
```

</details>

#### rejects an SDN file that is not a scene, without crashing

- Inspect a well-formed SDN file with no scene block
- Then fails cleanly


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect a well-formed SDN file with no scene block")
val r = run_cli("inspect " + NOT_A_SCENE)
Then_fails_cleanly(r)
expect(r.stdout).to_contain("missing top-level `scene` block")
```

</details>

#### rejects a scene with an unsupported node shape, naming the node

- Inspect a scene whose node declares shape sphere
- Then fails cleanly


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect a scene whose node declares shape sphere")
val r = run_cli("inspect " + BAD_SHAPE)
Then_fails_cleanly(r)
expect(r.stdout).to_contain("unsupported shape \"sphere\"")
expect(r.stdout).to_contain("\"blob\"")
```

</details>

#### fails with exit 1 when the scene file does not exist

- Inspect a path that is not on disk
   - Expected: r.exit_code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect a path that is not on disk")
val r = run_cli("inspect test/fixtures/model3d/there_is_no_such_file.sdn")
expect(r.exit_code).to_equal(1)
expect(r.stdout).to_contain("error: scene file not found")
```

</details>

### model3d CLI usage errors

#### exits 2 with usage text when no subcommand is given

- Run the CLI with no arguments
   - Expected: r.exit_code equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the CLI with no arguments")
val r = run_cli("")
expect(r.exit_code).to_equal(2)
expect(r.stdout).to_contain("Usage: simple model3d")
```

</details>

#### exits 2 on an unknown subcommand

- Run the CLI with a bogus subcommand
   - Expected: r.exit_code equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the CLI with a bogus subcommand")
val r = run_cli("frobnicate")
expect(r.exit_code).to_equal(2)
expect(r.stdout).to_contain("unknown subcommand: frobnicate")
```

</details>

#### exits 2 when render is missing --out

- Run render without an output path
   - Expected: r.exit_code equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run render without an output path")
val r = run_cli("render " + VALID)
expect(r.exit_code).to_equal(2)
expect(r.stdout).to_contain("missing --out")
```

</details>

#### exits 2 on out-of-range render dimensions

- Ask for a 5000-pixel-wide frame
   - Expected: r.exit_code equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Ask for a 5000-pixel-wide frame")
val r = run_cli("render " + VALID + " --out " + OUT_DIR + "/never.ppm --width 5000")
expect(r.exit_code).to_equal(2)
expect(r.stdout).to_contain("--width/--height must be in 8..1024")
```

</details>

#### exits 2 on a malformed camera override

- Pass a non-numeric --eye value
   - Expected: r.exit_code equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pass a non-numeric --eye value")
val r = run_cli("render " + VALID + " --out " + OUT_DIR + "/never.ppm --eye bad")
expect(r.exit_code).to_equal(2)
expect(r.stdout).to_contain("--eye expects X,Y,Z numbers")
```

</details>

### model3d CLI render

#### renders the scene to a PPM with exact header and pixel colors

- Render the fixture scene at 96x72
- mkdir p
   - Expected: r.exit_code equals `0`
- assert true
- Then the PPM header declares P3 96x72 at depth 255
   - Expected: lines[0] equals `P3`
   - Expected: lines[1] equals `96 72`
   - Expected: lines[2] equals `255`
- Then the center pixel is exactly the cube color
   - Expected: ppm_pixel_line(lines, 96, 48, 36) equals `CUBE_RGB`
- Then the top corners are exactly the background color
   - Expected: ppm_pixel_line(lines, 96, 0, 0) equals `BG_RGB`
   - Expected: ppm_pixel_line(lines, 96, 95, 0) equals `BG_RGB`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render the fixture scene at 96x72")
mkdir_p(OUT_DIR)
val out = OUT_DIR + "/probe.ppm"
val r = run_cli("render " + VALID + " --out " + out + " --width 96 --height 72")
expect(r.exit_code).to_equal(0)
expect(r.stdout).to_contain("wrote " + out + " (96x72, 2 nodes)")
assert_true(file_exists(out))

step("Then the PPM header declares P3 96x72 at depth 255")
val body = file_read(out)
val lines = body.split("\n")
expect(lines[0]).to_equal("P3")
expect(lines[1]).to_equal("96 72")
expect(lines[2]).to_equal("255")

step("Then the center pixel is exactly the cube color")
expect(ppm_pixel_line(lines, 96, 48, 36)).to_equal(CUBE_RGB)

step("Then the top corners are exactly the background color")
expect(ppm_pixel_line(lines, 96, 0, 0)).to_equal(BG_RGB)
expect(ppm_pixel_line(lines, 96, 95, 0)).to_equal(BG_RGB)
```

</details>

#### renders the same scene byte-identically twice

- Render the fixture scene twice to two files
- mkdir p
   - Expected: ra.exit_code equals `0`
   - Expected: rb.exit_code equals `0`
- Then both PPM files hash identically
   - Expected: ha equals `hb`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render the fixture scene twice to two files")
mkdir_p(OUT_DIR)
val out_a = OUT_DIR + "/det_a.ppm"
val out_b = OUT_DIR + "/det_b.ppm"
val ra = run_cli("render " + VALID + " --out " + out_a + " --width 96 --height 72")
val rb = run_cli("render " + VALID + " --out " + out_b + " --width 96 --height 72")
expect(ra.exit_code).to_equal(0)
expect(rb.exit_code).to_equal(0)

step("Then both PPM files hash identically")
val ha = file_hash_sha256(out_a)
val hb = file_hash_sha256(out_b)
expect(ha.len()).to_be_greater_than(0)
expect(ha).to_equal(hb)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
