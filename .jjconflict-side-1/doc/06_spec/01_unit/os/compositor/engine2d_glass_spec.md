# Engine2d Glass Specification

> _Engine2D path glass dispatch — native, no rt_gui_*.""_

<!-- sdn-diagram:id=engine2d_glass_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=engine2d_glass_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

engine2d_glass_spec -> std
engine2d_glass_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=engine2d_glass_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine2d Glass Specification

## Scenarios

### Engine2dCompositorBackend CompositorGlassCapable (D2 Phase 2)
_Engine2D path glass dispatch — native, no rt_gui_*.""_

#### as_glass_capable
_Backend opts back in to the glass subtrait in Phase 2._

#### opts in (returns non-nil, unlike Phase 1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = _make_backend(16, 16, 0xFF000000)
val cap = backend.as_glass_capable()
expect(cap != nil).to_equal(true)
```

</details>

#### blend_rect

#### alpha-blends a coloured overlay onto the framebuffer

1. cap blend rect
   - Expected: r > 0u32 and r < 255u32 is true
   - Expected: g > 0u32 and g < 255u32 is true
   - Expected: b > 0u32 and b < 255u32 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Blend white at 50% alpha over a black background; the
# affected pixel should land between black and white (every
# channel strictly between 0 and 255).
val backend = _make_backend(8, 8, 0xFF000000)
cap_blend_rect(backend, 0, 0, 4, 4, 0xFFFFFFFF, 128u8)
val sample = cap_read_pixel(backend, 1, 1)
val r = (sample >> 16) & 0xFFu32
val g = (sample >> 8) & 0xFFu32
val b = sample & 0xFFu32
expect(r > 0u32 and r < 255u32).to_equal(true)
expect(g > 0u32 and g < 255u32).to_equal(true)
expect(b > 0u32 and b < 255u32).to_equal(true)
```

</details>

#### leaves pixels outside the rect untouched

1. cap blend rect
   - Expected: outside == 0xFF000000u32 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = _make_backend(8, 8, 0xFF000000)
cap_blend_rect(backend, 0, 0, 2, 2, 0xFFFFFFFF, 200u8)
val outside = cap_read_pixel(backend, 7, 7)
expect(outside == 0xFF000000u32).to_equal(true)
```

</details>

#### gradient_v

#### paints a vertical gradient via Engine2D draw_gradient_rect

1. cap gradient v
   - Expected: top_r < bot_r is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = _make_backend(4, 8, 0xFF808080)
cap_gradient_v(backend, 0, 0, 4, 8, 0xFF000000, 0xFFFFFFFF)
val top = cap_read_pixel(backend, 0, 0)
val bottom = cap_read_pixel(backend, 0, 7)
val top_r = (top >> 16) & 0xFFu32
val bot_r = (bottom >> 16) & 0xFFu32
# Top should be darker than bottom along the gradient axis.
expect(top_r < bot_r).to_equal(true)
```

</details>

#### blur_region

#### averages neighbouring pixels (smooths a hard edge)

1. backend engine draw rect filled
2. backend engine present
3. cap blur region
   - Expected: seam_r > 0u32 and seam_r < 255u32 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Build a 4x4 framebuffer with a hard black/white split at
# column 2. Blurring across the seam must produce an
# in-between grey pixel — the proof that the impl is reading
# AND writing through Engine2D, not just no-oping.
val backend = _make_backend(4, 4, 0xFF000000)
backend.engine.draw_rect_filled(2, 0, 2, 4, 0xFFFFFFFF)
backend.engine.present()
cap_blur_region(backend, 0, 0, 4, 4, 1u32)
val seam = cap_read_pixel(backend, 1, 1)
val seam_r = (seam >> 16) & 0xFFu32
expect(seam_r > 0u32 and seam_r < 255u32).to_equal(true)
```

</details>

#### read_pixel

#### returns the framebuffer colour at (x, y)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = _make_backend(4, 4, 0xFF112233)
val px = cap_read_pixel(backend, 2, 2)
expect(px == 0xFF112233u32).to_equal(true)
```

</details>

#### returns 0 for out-of-bounds reads

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = _make_backend(4, 4, 0xFFFFFFFF)
val oob = cap_read_pixel(backend, 99, 99)
expect(oob == 0u32).to_equal(true)
```

</details>

#### blit_pixels

#### copies WebRenderer artifact pixels through Engine2D draw_image

1. backend blit pixels
   - Expected: cap_read_pixel(backend, 2, 1) equals `0xFF112233u32`
   - Expected: cap_read_pixel(backend, 4, 1) equals `0xFF778899u32`
   - Expected: cap_read_pixel(backend, 2, 2) equals `0xFF99AABBu32`
   - Expected: cap_read_pixel(backend, 4, 2) equals `0xFFFFFFFFu32`
   - Expected: cap_read_pixel(backend, 0, 0) equals `0xFF000000u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = _make_backend(6, 5, 0xFF000000)
val pixels: [u32] = [
    0xFF112233u32, 0xFF445566u32, 0xFF778899u32,
    0xFF99AABBu32, 0xFFCCDDEEu32, 0xFFFFFFFFu32
]
backend.blit_pixels(2, 1, 3, 2, pixels)
expect(cap_read_pixel(backend, 2, 1)).to_equal(0xFF112233u32)
expect(cap_read_pixel(backend, 4, 1)).to_equal(0xFF778899u32)
expect(cap_read_pixel(backend, 2, 2)).to_equal(0xFF99AABBu32)
expect(cap_read_pixel(backend, 4, 2)).to_equal(0xFFFFFFFFu32)
expect(cap_read_pixel(backend, 0, 0)).to_equal(0xFF000000u32)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/compositor/engine2d_glass_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Engine2dCompositorBackend CompositorGlassCapable (D2 Phase 2)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
