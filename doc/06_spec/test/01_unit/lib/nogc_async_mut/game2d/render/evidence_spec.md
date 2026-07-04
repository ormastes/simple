# game2d.render.evidence — pixel-evidence oracle unit specs

> Direct unit specs for the pixel-evidence oracles extracted from Rollball

<!-- sdn-diagram:id=evidence_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=evidence_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

evidence_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=evidence_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# game2d.render.evidence — pixel-evidence oracle unit specs

Direct unit specs for the pixel-evidence oracles extracted from Rollball

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Design | src/lib/nogc_async_mut/game2d/render/evidence.spl |
| Source | `test/01_unit/lib/nogc_async_mut/game2d/render/evidence_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Direct unit specs for the pixel-evidence oracles extracted from Rollball
(`find_centroid`, `diff_count`, `dump_ppm`): absolute expected values on
small, hand-constructed pixel buffers — no rendering, no game state.

## Scenarios

### game2d.render.evidence — find_centroid

#### single marked pixel in a 4x4 buffer returns its exact coordinates

- assert equal
- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bg: u32 = 0xFF000000
val mark: u32 = 0xFFFF0000
var px: [u32] = [bg; 16]
px[1 * 4 + 2] = mark
val c = find_centroid(px, 4, 4, mark)
assert_equal(c[0], 2)
assert_equal(c[1], 1)
assert_equal(c[2], 1)
```

</details>

#### two marked pixels average to the exact integer centroid

- assert equal
- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bg: u32 = 0xFF000000
val mark: u32 = 0xFF00FF00
var px: [u32] = [bg; 16]
px[0 * 4 + 0] = mark
px[3 * 4 + 2] = mark
val c = find_centroid(px, 4, 4, mark)
assert_equal(c[0], 1)
assert_equal(c[1], 1)
assert_equal(c[2], 2)
```

</details>

#### no matching pixel returns the [-1, -1, 0] sentinel

- assert equal
- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bg: u32 = 0xFF000000
var px: [u32] = [bg; 16]
val c = find_centroid(px, 4, 4, 0xFFFFFFFF)
assert_equal(c[0], -1)
assert_equal(c[1], -1)
assert_equal(c[2], 0)
```

</details>

### game2d.render.evidence — diff_count

#### counts the exact number of differing pixels

- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a: [u32] = [0; 16]
var b: [u32] = [0; 16]
b[0] = 1
b[5] = 1
b[15] = 1
assert_equal(diff_count(a, b, 16), 3)
```

</details>

#### identical buffers diff to exactly zero

- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a: [u32] = [7; 16]
var b: [u32] = [7; 16]
assert_equal(diff_count(a, b, 16), 0)
```

</details>

### game2d.render.evidence — dump_ppm

#### writes an exact P3 header and pixel bytes for a known 2x1 buffer

- assert true
- assert true
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val _ = rt_dir_create("build/test-scratch", true)
val path = "build/test-scratch/evidence_dump_ppm_spec.ppm"
val px: [u32] = [0xFFFF0000, 0xFF00FF00]
assert_true(dump_ppm(path, px, 2, 1))
assert_true(file_exists(path))
val content = file_read(path)
assert_equal(content, "P3\n2 1\n255\n255 0 0\n0 255 0\n")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Design:** [src/lib/nogc_async_mut/game2d/render/evidence.spl](src/lib/nogc_async_mut/game2d/render/evidence.spl)


</details>
