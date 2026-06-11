# Backend Software Simd Specification

> <details>

<!-- sdn-diagram:id=backend_software_simd_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=backend_software_simd_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

backend_software_simd_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=backend_software_simd_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Software Simd Specification

## Scenarios

### SoftwareBackend SIMD integration

### clear

#### AC-6: clear uses simd_fill_row when available

- var backend = SoftwareBackend create
- reset simd hits
- backend clear
   - Expected: pixels[0] equals `0xFFFF0000`
   - Expected: pixels[63] equals `0xFFFF0000`
- backend shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = SoftwareBackend.create()
reset_simd_hits()
if backend.init(64, 64):
    backend.clear(0xFFFF0000)
    val pixels = backend.read_pixels()
    expect(pixels[0]).to_equal(0xFFFF0000)
    expect(pixels[63]).to_equal(0xFFFF0000)
    expect(simd_hit_counts().fill_hits).to_be_greater_than(0)
    backend.shutdown()
```

</details>

#### AC-6: clear produces same result with and without SIMD

- var backend = SoftwareBackend create
- backend clear
   - Expected: all_green is true
- backend shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = SoftwareBackend.create()
if backend.init(64, 64):
    backend.clear(0xFF00FF00)
    val pixels = backend.read_pixels()
    var i = 0
    var all_green = true
    while i < 64:
        if pixels[i] != 0xFF00FF00:
            all_green = false
        i = i + 1
    expect(all_green).to_equal(true)
    backend.shutdown()
```

</details>

### blit_image

#### AC-6: blit uses simd_blit_row for row copies

- var backend = SoftwareBackend create
- reset simd hits
- backend clear
- backend blit image
   - Expected: pixels[0] equals `0xFFFF0000`
- backend shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = SoftwareBackend.create()
reset_simd_hits()
val src_pixels: [u32] = [0xFFFF0000; 16]
if backend.init(64, 64):
    backend.clear(0xFF000000)
    backend.blit_image(0, 0, 4, 4, src_pixels)
    val pixels = backend.read_pixels()
    expect(pixels[0]).to_equal(0xFFFF0000)
    expect(simd_hit_counts().copy_hits).to_be_greater_than(0)
    backend.shutdown()
```

</details>

### alpha blending

#### AC-6: draw_rect_filled opaque spans record simd fill hits

- var backend = SoftwareBackend create
- reset simd hits
- backend draw rect filled
   - Expected: pixels[5 * 64 + 4] equals `0xFFFF0000`
- backend shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = SoftwareBackend.create()
reset_simd_hits()
if backend.init(64, 64):
    backend.draw_rect_filled(4, 5, 16, 8, 0xFFFF0000)
    val pixels = backend.read_pixels()
    expect(pixels[5 * 64 + 4]).to_equal(0xFFFF0000)
    expect(simd_hit_counts().fill_hits).to_be_greater_than(0)
    backend.shutdown()
```

</details>

#### AC-6: draw_rect_filled with alpha uses simd_blend_row

- var backend = SoftwareBackend create
- reset simd hits
- backend clear
- backend draw rect filled
- backend shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = SoftwareBackend.create()
reset_simd_hits()
if backend.init(64, 64):
    backend.clear(0xFF0000FF)
    backend.draw_rect_filled(0, 0, 32, 32, 0x80FF0000)
    val pixels = backend.read_pixels()
    val r = (pixels[0] >> 16) & 0xFF
    expect(r).to_be_greater_than(50)
    expect(simd_hit_counts().alpha_hits).to_be_greater_than(0)
    backend.shutdown()
```

</details>

### scalar fallback

#### AC-6: works correctly when no SIMD available

- var backend = SoftwareBackend create
- backend clear
- backend draw line
   - Expected: pixels[0] equals `0xFFFFFFFF`
- backend shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = SoftwareBackend.create()
if backend.init(8, 8):
    backend.clear(0xFFAABBCC)
    backend.draw_line(0, 0, 7, 7, 0xFFFFFFFF, 1)
    val pixels = backend.read_pixels()
    expect(pixels[0]).to_equal(0xFFFFFFFF)
    backend.shutdown()
```

</details>

#### AC-6: tile-based rendering preserved with SIMD

- var backend = SoftwareBackend create
- backend clear
- backend draw rect filled
- backend present
   - Expected: pixels[0] equals `0xFFFF0000`
- backend shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = SoftwareBackend.create()
if backend.init(128, 128):
    backend.clear(0xFF000000)
    backend.draw_rect_filled(0, 0, 128, 128, 0xFFFF0000)
    backend.present()
    val pixels = backend.read_pixels()
    expect(pixels[0]).to_equal(0xFFFF0000)
    backend.shutdown()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine2d/backend_software_simd_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SoftwareBackend SIMD integration
- clear
- blit_image
- alpha blending
- scalar fallback

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
