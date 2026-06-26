# Helpers Parity Specification

> <details>

<!-- sdn-diagram:id=helpers_parity_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=helpers_parity_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

helpers_parity_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=helpers_parity_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 67 | 67 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Helpers Parity Specification

## Scenarios

### helpers_clip — bounds checking

#### clip_point_in_bounds: interior point is in bounds

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(clip_point_in_bounds(5, 5, 10, 10)).to_be(true)
```

</details>

#### clip_point_in_bounds: (0,0) is in bounds

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(clip_point_in_bounds(0, 0, 10, 10)).to_be(true)
```

</details>

#### clip_point_in_bounds: right edge (exclusive) is out of bounds

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(clip_point_in_bounds(10, 5, 10, 10)).to_be(false)
```

</details>

#### clip_point_in_bounds: bottom edge (exclusive) is out of bounds

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(clip_point_in_bounds(5, 10, 10, 10)).to_be(false)
```

</details>

#### clip_point_in_bounds: negative x is out of bounds

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(clip_point_in_bounds(-1, 5, 10, 10)).to_be(false)
```

</details>

#### clip_point_in_rect: point inside clip rect

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(clip_point_in_rect(6, 6, 5, 5, 5, 5)).to_be(true)
```

</details>

#### clip_point_in_rect: point outside clip rect

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(clip_point_in_rect(3, 3, 5, 5, 5, 5)).to_be(false)
```

</details>

#### clip_pixel_allowed: no clip — passes bounds check

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(clip_pixel_allowed(3, 3, 10, 10, false, 0, 0, 10, 10)).to_be(true)
```

</details>

#### clip_pixel_allowed: clip enabled, point inside — allowed

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(clip_pixel_allowed(6, 6, 10, 10, true, 5, 5, 5, 5)).to_be(true)
```

</details>

#### clip_pixel_allowed: clip enabled, point outside — blocked

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(clip_pixel_allowed(3, 3, 10, 10, true, 5, 5, 5, 5)).to_be(false)
```

</details>

#### clip_pixel_allowed: out of framebuffer — blocked regardless of clip

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(clip_pixel_allowed(-1, 5, 10, 10, false, 0, 0, 10, 10)).to_be(false)
```

</details>

#### rect_intersect_w: overlapping rects

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = rect_intersect_w(0, 8, 4, 8)
expect(w).to_equal(4)
```

</details>

#### rect_intersect_w: disjoint rects yields non-positive width

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = rect_intersect_w(0, 5, 10, 5)
expect(w).to_be_less_than(1)
```

</details>

#### rect_intersect_h: overlapping rects

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = rect_intersect_h(0, 8, 4, 8)
expect(h).to_equal(4)
```

</details>

#### clip_rect_to_viewport: rect fully inside

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(clip_rect_to_viewport(1, 1, 5, 5, 10, 10)).to_be(true)
```

</details>

#### clip_rect_to_viewport: rect fully outside right

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(clip_rect_to_viewport(15, 0, 5, 5, 10, 10)).to_be(false)
```

</details>

#### clip_rect_to_viewport: rect fully outside top

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(clip_rect_to_viewport(0, -10, 5, 5, 10, 10)).to_be(false)
```

</details>

#### pixel_index: correct flat index

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(pixel_index(3, 2, 10)).to_equal(23)
```

</details>

### helpers_clip — mask

#### mask_blocks_at: empty mask never blocks

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var empty_mask: [u8] = []
expect(mask_blocks_at(empty_mask, 10, 5, 5)).to_be(false)
```

</details>

#### mask_blocks_at: mask byte 0 blocks

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mask: [u8] = [1u8, 0u8, 1u8]
expect(mask_blocks_at(mask, 3, 1, 0)).to_be(true)
```

</details>

#### mask_blocks_at: mask byte 1 does not block

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mask: [u8] = [1u8, 0u8, 1u8]
expect(mask_blocks_at(mask, 3, 0, 0)).to_be(false)
```

</details>

#### mask_blocks_at: out-of-range coordinate does not block

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mask: [u8] = [0u8]
expect(mask_blocks_at(mask, 1, 5, 5)).to_be(false)
```

</details>

### helpers_pixel — buffer access

#### buf_get_pixel: returns 0 for out-of-bounds

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf: [u32] = [0xFFFF0000u32]
expect(buf_get_pixel(buf, 1, 0, 1, 1)).to_equal(0u32)
```

</details>

#### buf_get_pixel: reads in-bounds pixel

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf: [u32] = [0u32, 0u32, 0xAABBCCDDu32, 0u32]
val got = buf_get_pixel(buf, 2, 0, 4, 1)
expect(got).to_equal(0xAABBCCDDu32)
```

</details>

#### buf_set_pixel: writes in-bounds pixel

- buf = buf set pixel
   - Expected: buf[2] equals `0xDEADBEEFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf: [u32] = [0u32, 0u32, 0u32, 0u32]
buf = buf_set_pixel(buf, 2, 0, 4, 1, 0xDEADBEEFu32)
expect(buf[2]).to_equal(0xDEADBEEFu32)
```

</details>

#### buf_set_pixel: out-of-bounds write is ignored

- buf = buf set pixel
   - Expected: buf[0] equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf: [u32] = [0u32]
buf = buf_set_pixel(buf, 5, 5, 1, 1, 0xFFFFFFFFu32)
expect(buf[0]).to_equal(0u32)
```

</details>

#### buf_set_pixel_blend: opaque src replaces dst

- var buf: [u32] = [rgb
- buf = buf set pixel blend
   - Expected: color_r(buf[0]) equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf: [u32] = [rgb(0, 0, 0)]
val src = rgb(255, 0, 0)
buf = buf_set_pixel_blend(buf, 0, 0, 1, 1, src)
expect(color_r(buf[0])).to_equal(255)
```

</details>

#### buf_set_pixel_blend: transparent src leaves dst unchanged

- var buf: [u32] = [rgb
- buf = buf set pixel blend
   - Expected: color_g(buf[0]) equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf: [u32] = [rgb(0, 255, 0)]
val src = rgba(255, 0, 0, 0)
buf = buf_set_pixel_blend(buf, 0, 0, 1, 1, src)
expect(color_g(buf[0])).to_equal(255)
```

</details>

### helpers_pixel — alpha compositing

#### alpha_premultiply: opaque color is unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = rgb(100, 150, 200)
expect(alpha_premultiply(c)).to_equal(c)
```

</details>

#### alpha_premultiply: transparent returns 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = rgba(255, 255, 255, 0)
expect(alpha_premultiply(c)).to_equal(0u32)
```

</details>

#### alpha_premultiply: 50% alpha halves RGB

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = rgba(200, 200, 200, 128)
val pm = alpha_premultiply(c)
val r = color_r(pm)
expect(r).to_be_greater_than(97)
expect(r).to_be_less_than(103)
```

</details>

#### alpha_unpremultiply: zero alpha returns 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(alpha_unpremultiply(0u32)).to_equal(0u32)
```

</details>

#### alpha_unpremultiply: opaque color is unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = rgb(80, 160, 240)
expect(alpha_unpremultiply(c)).to_equal(c)
```

</details>

#### pixels_to_bytes: 4 bytes per pixel

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(pixels_to_bytes(10)).to_equal(40)
```

</details>

#### bytes_to_pixels: inverse of pixels_to_bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_to_pixels(pixels_to_bytes(7))).to_equal(7)
```

</details>

### helpers_text — dimensions

#### text_buf_height equals glyph_height at font_size 7

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = text_buf_height(7)
expect(h).to_equal(7)
```

</details>

#### text_buf_height scales with font_size

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = text_buf_height(14)
expect(h).to_equal(14)
```

</details>

#### text_buf_width: empty string returns 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_buf_width("", 7)).to_equal(0)
```

</details>

#### text_buf_width: single char at scale 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# advance = 6 * scale; scale = 7/7 = 1
expect(text_buf_width("A", 7)).to_equal(6)
```

</details>

#### text_buf_width: 3 chars at scale 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_buf_width("ABC", 7)).to_equal(18)
```

</details>

#### text_scale: font_size 7 gives scale 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_scale(7)).to_equal(1)
```

</details>

#### text_scale: font_size 14 gives scale 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_scale(14)).to_equal(2)
```

</details>

#### text_scale: font_size < 7 is clamped to 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(text_scale(1)).to_equal(1)
```

</details>

### helpers_text — render_to_buf

#### text_render_to_buf: empty text returns empty buffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = text_render_to_buf("", 0xFFFFFFFFu32, 0xFF000000u32, 7)
expect(buf.len()).to_equal(0)
```

</details>

#### text_render_to_buf: buffer size matches dimensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = text_render_to_buf("Hi", 0xFFFFFFFFu32, 0xFF000000u32, 7)
val expected_len = text_buf_width("Hi", 7) * text_buf_height(7)
expect(buf.len()).to_equal(expected_len)
```

</details>

#### text_render_to_buf: background color fills non-glyph pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bg = rgba(0, 0, 255, 255)
val fg = rgba(255, 0, 0, 255)
val buf = text_render_to_buf(" ", fg, bg, 7)
# Space glyph has no set bits — entire buffer should be background
var all_bg = true
var bi = 0
while bi < buf.len():
    if buf[bi] != bg:
        all_bg = false
    bi = bi + 1
expect(all_bg).to_be(true)
```

</details>

#### text_render_to_buf: parity with inline draw_text_bg pattern

- inline buf push
- inline buf = render text to buffer
   - Expected: helper_buf.len() equals `inline_buf.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This mirrors the body in each GPU backend's draw_text_bg:
#   fill buffer with bg, call render_text_to_buffer, blit.
# We verify text_render_to_buf produces same buffer as the inline form.
use std.gpu.engine2d.glyph.{glyph_height, glyph_advance, render_text_to_buffer}
val text_val = "X"
val font_size = 7
val fg = rgb(255, 255, 255)
val bg = rgb(0, 0, 0)
val gh = glyph_height()
var scale = font_size / gh
if scale < 1:
    scale = 1
val advance = glyph_advance(scale)
val text_w = text_val.len().to_i32() * advance
val text_h = gh * scale
var inline_buf: [u32] = []
var fill_i = 0
while fill_i < text_w * text_h:
    inline_buf.push(bg)
    fill_i = fill_i + 1
inline_buf = render_text_to_buffer(inline_buf, text_w, text_h, 0, 0, text_val, fg, font_size)
val helper_buf = text_render_to_buf(text_val, fg, bg, font_size)
expect(helper_buf.len()).to_equal(inline_buf.len())
var match_ok = true
var ci = 0
while ci < inline_buf.len():
    if inline_buf[ci] != helper_buf[ci]:
        match_ok = false
    ci = ci + 1
expect(match_ok).to_be(true)
```

</details>

### helpers_availability — backend names

#### backend_display_name: rocm includes HIP

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n = backend_display_name("rocm")
expect(n).to_equal("AMD ROCm/HIP")
```

</details>

#### backend_display_name: vulkan

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n = backend_display_name("vulkan")
expect(n).to_equal("Vulkan Compute")
```

</details>

#### backend_display_name: cpu

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n = backend_display_name("cpu")
expect(n).to_equal("CPU Software (fallback)")
```

</details>

#### backend_display_name: unknown

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n = backend_display_name("unknown_xyz")
expect(n).to_start_with("Unknown")
```

</details>

#### backend_priority: metal is highest priority (0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(backend_priority("metal")).to_equal(0)
expect(backend_priority("cuda")).to_equal(1)
expect(backend_priority("rocm")).to_equal(2)
```

</details>

#### backend_priority: cpu is lowest priority (12)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(backend_priority("cpu")).to_equal(12)
```

</details>

#### backend_priority: vulkan < software < cpu

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = backend_priority("vulkan")
val s = backend_priority("software")
val c = backend_priority("cpu")
expect(v).to_be_less_than(s)
expect(s).to_be_less_than(c)
```

</details>

#### backend_default_priority_order starts at Metal then CUDA HIP then Vulkan

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val order = backend_default_priority_order()
expect(order[0]).to_equal("metal")
expect(order[1]).to_equal("cuda")
expect(order[2]).to_equal("rocm")
expect(order[4]).to_equal("vulkan")
expect(order[5]).to_equal("directx")
expect(order[6]).to_equal("opencl")
expect(order[order.len() - 1]).to_equal("cpu")
```

</details>

#### backend_full_preference_order keeps native surfaces before auto GPU order

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val order = backend_full_preference_order()
expect(order[0]).to_equal("baremetal")
expect(order[1]).to_equal("virtio_gpu")
expect(order[2]).to_equal("metal")
expect(order[3]).to_equal("cuda")
expect(order[4]).to_equal("rocm")
```

</details>

#### backend_is_hardware: cuda is hardware

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(backend_is_hardware("cuda")).to_be(true)
```

</details>

#### backend_is_hardware: cpu is not hardware

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(backend_is_hardware("cpu")).to_be(false)
```

</details>

#### backend_is_hardware: software is not hardware

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(backend_is_hardware("software")).to_be(false)
```

</details>

#### backend_requires_gpu: cuda requires GPU

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(backend_requires_gpu("cuda")).to_be(true)
```

</details>

#### backend_requires_gpu: vulkan does not require (can software fallback)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(backend_requires_gpu("vulkan")).to_be(false)
```

</details>

#### backend_requires_gpu: cpu does not require GPU

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(backend_requires_gpu("cpu")).to_be(false)
```

</details>

#### feature_gate_description: returns non-empty text for all known backends

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = ["cuda", "rocm", "metal", "qualcomm", "vulkan", "opengl", "intel", "webgpu", "software", "cpu"]
var all_ok = true
var ni = 0
while ni < 10:
    val desc = feature_gate_description(names[ni])
    if desc.len() == 0:
        all_ok = false
    ni = ni + 1
expect(all_ok).to_be(true)
```

</details>

### helpers_availability — numeric conversions

#### backend_i64: converts i32 to i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(backend_i64(42)).to_equal(42)
```

</details>

#### backend_i64: handles negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(backend_i64(-1)).to_equal(-1)
```

</details>

#### backend_bool_to_i32: true -> 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(backend_bool_to_i32(true)).to_equal(1)
```

</details>

#### backend_bool_to_i32: false -> 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(backend_bool_to_i32(false)).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/helpers_parity_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- helpers_clip — bounds checking
- helpers_clip — mask
- helpers_pixel — buffer access
- helpers_pixel — alpha compositing
- helpers_text — dimensions
- helpers_text — render_to_buf
- helpers_availability — backend names
- helpers_availability — numeric conversions

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 67 |
| Active scenarios | 67 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
