# Metal Engine2d Readback Specification

## Scenarios

### Metal Engine2D framebuffer readback

#### raw GPU pixels

#### downloads clear and rect_filled pixels from the Metal framebuffer

1. var b = MetalBackend create
   - Expected: b.init(16, 16) is true

2. b clear

3. b draw rect filled
   - Expected: b.gpu_frame_complete is true
   - Expected: pixels.len() equals `256`
   - Expected: pixels[0] equals `0x10203040 as u32`
   - Expected: pixels[4 + (4 * 16)] equals `0x01020304 as u32`

4. b shutdown
   - Expected: is_macos() is false


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if is_macos():
    var b = MetalBackend.create()
    expect(b.init(16, 16)).to_equal(true)
    b.clear(0x10203040 as u32)
    b.draw_rect_filled(4, 4, 4, 4, 0x01020304 as u32)
    expect(b.gpu_frame_complete).to_equal(true)
    val pixels = b.read_pixels()
    expect(pixels.len()).to_equal(256)
    expect(pixels[0]).to_equal(0x10203040 as u32)
    expect(pixels[4 + (4 * 16)]).to_equal(0x01020304 as u32)
    b.shutdown()
else:
    expect(is_macos()).to_equal(false)
```

</details>

#### falls back after CPU-only text rendering invalidates GPU completeness

1. var b = MetalBackend create
   - Expected: b.init(16, 16) is true

2. b clear

3. b draw text
   - Expected: b.gpu_frame_complete is false
   - Expected: pixels.len() equals `256`

4. b shutdown
   - Expected: is_macos() is false


<details>
<summary>Executable SPipe</summary>

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
| Source | `test/integration/rendering/metal_engine2d_readback_spec.spl` |
| Updated | 2026-06-01 |
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

