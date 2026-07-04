# spritesheet pack

> `simple spritesheet pack <dir-or-files> --out atlas.png --manifest atlas.sdn [--max-width N]` decodes a set of PNG sprites, packs them with the existing shelf packer (`AtlasBuilder`), composites the packed rects into one RGBA buffer, and encodes it as one atlas PNG plus an SDN manifest in the exact shape `std.nogc_sync_mut.game2d.asset.table.load_assets` already parses.

<!-- sdn-diagram:id=spritesheet_cli_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=spritesheet_cli_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

spritesheet_cli_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=spritesheet_cli_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# spritesheet pack

`simple spritesheet pack <dir-or-files> --out atlas.png --manifest atlas.sdn [--max-width N]` decodes a set of PNG sprites, packs them with the existing shelf packer (`AtlasBuilder`), composites the packed rects into one RGBA buffer, and encodes it as one atlas PNG plus an SDN manifest in the exact shape `std.nogc_sync_mut.game2d.asset.table.load_assets` already parses.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #game-tools-spritesheet-pack |
| Category | App / CLI Surface |
| Status | Implemented |
| Requirements | N/A |
| Plan | doc/03_plan/app/game_tools/image_object_design_plan.md |
| Design | N/A |
| Research | doc/01_research/app/game_tools/image_object_design.md |
| Source | `test/02_integration/app/spritesheet/spritesheet_cli_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`simple spritesheet pack <dir-or-files> --out atlas.png --manifest atlas.sdn
[--max-width N]` decodes a set of PNG sprites, packs them with the existing
shelf packer (`AtlasBuilder`), composites the packed rects into one RGBA
buffer, and encodes it as one atlas PNG plus an SDN manifest in the exact
shape `std.nogc_sync_mut.game2d.asset.table.load_assets` already parses.

Plan: doc/03_plan/app/game_tools/image_object_design_plan.md (spritesheet
CLI section).

## Key Concepts

| Concept | Description |
|---------|-------------|
| Pixel-exact packing | Every sprite's source pixels reappear byte-for-byte at its manifest-declared rect inside the atlas PNG |
| Manifest interop | The emitted `atlas.sdn` loads through `load_assets` with zero loader changes |
| Determinism | Two `pack` runs over the same inputs to the same output path produce byte-identical `atlas.png`/`atlas.sdn` |
| Trust boundary | A non-PNG file among the inputs fails cleanly (exit 1, path-qualified message), never a panic |

## Syntax

```
simple spritesheet pack <dir-or-files> --out atlas.png --manifest atlas.sdn [--max-width N]
```

## Examples

```
simple spritesheet pack assets/sprites --out build/atlas.png --manifest build/atlas.sdn
# wrote build/atlas.png and build/atlas.sdn (2 sprites, 4x2)
```

## Note on assertion shape

Each `it` block below folds every check into a single boolean and ends with
exactly one `assert_true(...)`/`expect(...)` call. `std.spec`'s `it` runner
only reports the *last* assertion executed in a block (see
`doc/08_tracking/bug/spec_it_block_last_expect_wins_masks_earlier_failure_2026-07-03.md`
— an earlier failing `expect()` is silently discarded if a later one in the
same block passes), so a block with several independent `expect()` calls is
not a trustworthy oracle here. Diagnostic `print`s are unconditional so a
failure is still debuggable from stdout.

## Scenarios

### spritesheet pack

#### packs 2 fixture PNGs into one atlas.png with pixel-exact rects

- Pack the two fixture sprites
- mkdir p
- Then the manifest loads through the game2d asset loader and every sprite's pixels are exact at its manifest rect
- var ok =
- ok = ok and loaded is ok
- ok = ok and table atlases contains
- ok = ok and atlas regions contains
- ok = ok and decoded r is ok
- ok = ok and one rect len
- ok = ok and img pixels[
- ok = ok and img pixels[
- ok = ok and two rect len
- ok = ok and img pixels[
- ok = ok and img pixels[
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pack the two fixture sprites")
mkdir_p(OUT_DIR)
val out_png = OUT_DIR + "/atlas.png"
val out_sdn = OUT_DIR + "/atlas.sdn"
val r = run_cli("pack {SPRITES_DIR} --out {out_png} --manifest {out_sdn}")

step("Then the manifest loads through the game2d asset loader and every sprite's pixels are exact at its manifest rect")
var ok = (r.exit_code == 0) and file_exists(out_png) and file_exists(out_sdn)
val loaded = load_assets(out_sdn)
ok = ok and loaded.is_ok()
if val Ok(table) = loaded:
    ok = ok and table.atlases.contains("atlas")
    if table.atlases.contains("atlas"):
        val atlas = table.atlases["atlas"]
        ok = ok and atlas.image_width == 4 and atlas.image_height == 2
        ok = ok and atlas.regions.contains("one") and atlas.regions.contains("two")
        val bytes = file_read_bytes(out_png)
        val decoded_r = decode_png_to_argb(bytes)
        ok = ok and decoded_r.is_ok()
        if val Ok(img) = decoded_r:
            ok = ok and img.width == 4 and img.height == 2
            if atlas.regions.contains("one"):
                val one_rect = atlas.regions["one"]
                ok = ok and one_rect.len() == 4
                ok = ok and one_rect[0] == 0 and one_rect[1] == 0 and one_rect[2] == 2 and one_rect[3] == 2
                ok = ok and img.pixels[one_rect[1] * img.width + one_rect[0]] == ONE[0]
                ok = ok and img.pixels[one_rect[1] * img.width + one_rect[0] + 1] == ONE[1]
                ok = ok and img.pixels[(one_rect[1] + 1) * img.width + one_rect[0]] == ONE[2]
                ok = ok and img.pixels[(one_rect[1] + 1) * img.width + one_rect[0] + 1] == ONE[3]
            if atlas.regions.contains("two"):
                val two_rect = atlas.regions["two"]
                ok = ok and two_rect.len() == 4
                ok = ok and two_rect[0] == 2 and two_rect[1] == 0 and two_rect[2] == 2 and two_rect[3] == 2
                ok = ok and img.pixels[two_rect[1] * img.width + two_rect[0]] == TWO[0]
                ok = ok and img.pixels[two_rect[1] * img.width + two_rect[0] + 1] == TWO[1]
                ok = ok and img.pixels[(two_rect[1] + 1) * img.width + two_rect[0]] == TWO[2]
                ok = ok and img.pixels[(two_rect[1] + 1) * img.width + two_rect[0] + 1] == TWO[3]
print "DIAG pack exit_code={r.exit_code} stdout={r.stdout}"
assert_true(ok)
```

</details>

#### is byte-identical across two pack runs over the same inputs

- Pack the fixture sprites to a fixed output path
- mkdir p
- Then repacking the same inputs to the same path is byte-identical
- hash png 1 len
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pack the fixture sprites to a fixed output path")
mkdir_p(OUT_DIR)
val out_png = OUT_DIR + "/det_atlas.png"
val out_sdn = OUT_DIR + "/det_atlas.sdn"
val r1 = run_cli("pack {SPRITES_DIR} --out {out_png} --manifest {out_sdn}")
val hash_png_1 = file_hash_sha256(out_png)
val hash_sdn_1 = file_hash_sha256(out_sdn)

step("Then repacking the same inputs to the same path is byte-identical")
val r2 = run_cli("pack {SPRITES_DIR} --out {out_png} --manifest {out_sdn}")
val hash_png_2 = file_hash_sha256(out_png)
val hash_sdn_2 = file_hash_sha256(out_sdn)
val ok = (r1.exit_code == 0) and (r2.exit_code == 0) and
    hash_png_1.len() > 0 and (hash_png_1 == hash_png_2) and (hash_sdn_1 == hash_sdn_2)
print "DIAG det r1={r1.exit_code} r2={r2.exit_code} hash_png_1={hash_png_1} hash_png_2={hash_png_2}"
assert_true(ok)
```

</details>

### spritesheet pack error paths

#### rejects a directory containing a non-PNG file with a path-qualified error, exit 1

- Create a directory with one valid PNG and one garbage file
- mkdir p
- file write bytes
- write file
- Then pack fails cleanly, naming the offending file
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create a directory with one valid PNG and one garbage file")
val bad_dir = OUT_DIR + "/bad_input"
mkdir_p(bad_dir)
file_write_bytes(bad_dir + "/ok.png", encode_argb_to_png(ONE, 2, 2))
write_file(bad_dir + "/notes.txt", "this is not a PNG file")

step("Then pack fails cleanly, naming the offending file")
val r = run_cli("pack {bad_dir} --out {OUT_DIR}/never.png --manifest {OUT_DIR}/never.sdn")
val ok = (r.exit_code == 1) and r.stdout.contains("notes.txt")
print "DIAG bad_input exit_code={r.exit_code} stdout={r.stdout}"
assert_true(ok)
```

</details>

#### rejects a missing input path, exit 1

- Pack a nonexistent file
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pack a nonexistent file")
val r = run_cli("pack {OUT_DIR}/does_not_exist.png --out {OUT_DIR}/never2.png --manifest {OUT_DIR}/never2.sdn")
val ok = (r.exit_code == 1) and r.stdout.contains("does_not_exist.png")
print "DIAG missing_input exit_code={r.exit_code} stdout={r.stdout}"
assert_true(ok)
```

</details>

#### exits 2 when --out is missing

- Run pack without --out
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run pack without --out")
val r = run_cli("pack {SPRITES_DIR} --manifest {OUT_DIR}/never3.sdn")
val ok = (r.exit_code == 2) and r.stdout.contains("missing --out")
print "DIAG no_out exit_code={r.exit_code} stdout={r.stdout}"
assert_true(ok)
```

</details>

#### exits 2 when --manifest is missing

- Run pack without --manifest
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run pack without --manifest")
val r = run_cli("pack {SPRITES_DIR} --out {OUT_DIR}/never3.png")
val ok = (r.exit_code == 2) and r.stdout.contains("missing --manifest")
print "DIAG no_manifest exit_code={r.exit_code} stdout={r.stdout}"
assert_true(ok)
```

</details>

#### exits 2 when no input is given

- Run pack with no positional input
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run pack with no positional input")
val r = run_cli("pack --out {OUT_DIR}/never4.png --manifest {OUT_DIR}/never4.sdn")
val ok = (r.exit_code == 2) and r.stdout.contains("missing input")
print "DIAG no_input exit_code={r.exit_code} stdout={r.stdout}"
assert_true(ok)
```

</details>

#### exits 2 on an unknown option

- Run pack with a bogus flag
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run pack with a bogus flag")
val r = run_cli("pack {SPRITES_DIR} --out {OUT_DIR}/never5.png --manifest {OUT_DIR}/never5.sdn --frobnicate")
val ok = (r.exit_code == 2) and r.stdout.contains("unknown option")
print "DIAG unknown_option exit_code={r.exit_code} stdout={r.stdout}"
assert_true(ok)
```

</details>

#### exits 2 on an unknown subcommand

- Run an unrecognized subcommand
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run an unrecognized subcommand")
val r = run_cli("bogus")
val ok = (r.exit_code == 2) and r.stdout.contains("unknown subcommand")
print "DIAG unknown_subcommand exit_code={r.exit_code} stdout={r.stdout}"
assert_true(ok)
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


## Related Documentation

- **Plan:** [doc/03_plan/app/game_tools/image_object_design_plan.md](doc/03_plan/app/game_tools/image_object_design_plan.md)
- **Research:** [doc/01_research/app/game_tools/image_object_design.md](doc/01_research/app/game_tools/image_object_design.md)


</details>
