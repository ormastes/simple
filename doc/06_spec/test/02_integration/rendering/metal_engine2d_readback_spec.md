# Metal Engine2d Readback Specification

> <details>

<!-- sdn-diagram:id=metal_engine2d_readback_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=metal_engine2d_readback_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

metal_engine2d_readback_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=metal_engine2d_readback_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Metal Engine2d Readback Specification

## Scenarios

### Metal Engine2D framebuffer readback

#### raw GPU pixels

#### downloads clear and rect_filled pixels from the Metal framebuffer

- var b = MetalBackend create
   - Expected: b.init(16, 16) is true
- b clear
- b draw rect filled
- b draw rect filled
   - Expected: b.gpu_frame_complete is true
   - Expected: pixels.len() equals `256`
   - Expected: pixels[0] equals `0x10203040 as u32`
   - Expected: pixels[4 + (4 * 16)] equals `0xFF020304 as u32`
   - Expected: pixels[8 + (8 * 16)] equals `0x101F2F3F as u32`
- b shutdown
   - Expected: is_macos() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_macos():
    var b = MetalBackend.create()
    expect(b.init(16, 16)).to_equal(true)
    b.clear(0x10203040 as u32)
    # Opaque fill (alpha=0xFF): overwrite semantics, the raw
    # framebuffer-download proof this spec exists for.
    b.draw_rect_filled(4, 4, 4, 4, 0xFF020304 as u32)
    # Semi-transparent fill (alpha=0x01): pins the src-over blend
    # contract shared bit-exact by the CPU mirror (color.blend())
    # and the Metal kernel (blend_src_over() in
    # backend_metal_msl.spl), added in commit 97e3699cd3.
    b.draw_rect_filled(8, 8, 4, 4, 0x01020304 as u32)
    expect(b.gpu_frame_complete).to_equal(true)
    val pixels = b.read_pixels()
    expect(pixels.len()).to_equal(256)
    expect(pixels[0]).to_equal(0x10203040 as u32)
    expect(pixels[4 + (4 * 16)]).to_equal(0xFF020304 as u32)
    # src-over blend of 0x01020304 over clear color 0x10203040:
    #   inv = 255 - 1 = 254
    #   r = (0x02*1 + 0x20*254) / 255 = 8130 / 255  = 31 = 0x1F
    #   g = (0x03*1 + 0x30*254) / 255 = 12195 / 255 = 47 = 0x2F
    #   b = (0x04*1 + 0x40*254) / 255 = 16260 / 255 = 63 = 0x3F
    #   a = 1 + (0x10*254) / 255       = 1 + 15      = 16 = 0x10
    # => 0x101F2F3F
    expect(pixels[8 + (8 * 16)]).to_equal(0x101F2F3F as u32)
    b.shutdown()
else:
    expect(is_macos()).to_equal(false)
```

</details>

#### falls back after CPU-only text rendering invalidates GPU completeness

- var b = MetalBackend create
   - Expected: b.init(16, 16) is true
- b clear
- b draw text
   - Expected: b.gpu_frame_complete is false
   - Expected: pixels.len() equals `256`
- b shutdown
   - Expected: is_macos() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_macos():
    var b = MetalBackend.create()
    expect(b.init(16, 16)).to_equal(true)
    b.clear(0x10203040 as u32)
    b.draw_text(1, 1, "A", 0x01020304 as u32, 8)
    expect(b.gpu_frame_complete).to_equal(false)
    val pixels = b.read_pixels()
    expect(pixels.len()).to_equal(256)
    b.shutdown()
else:
    expect(is_macos()).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/metal_engine2d_readback_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Metal Engine2D framebuffer readback

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
