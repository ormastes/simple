# helpers_parity_spec

> Purpose: This spec proves helpers_clip — bounds checking.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 65 | 65 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# helpers_parity_spec

Purpose: This spec proves helpers_clip — bounds checking.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/rendering/helpers_parity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves helpers_clip — bounds checking.
Audience: Maintainers of the Simple integration suite reviewing this behavior.

## Scenarios

### helpers_clip — bounds checking

#### clip_point_in_bounds: interior point is in bounds

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- clip_point_in_bounds: interior point is in bounds


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-HELPERSPARITY-001
step("clip_point_in_bounds: interior point is in bounds")
expect(clip_point_in_bounds(5, 5, 10, 10)).to_be_true()
```

</details>

#### clip_point_in_bounds: (0,0) is in bounds

- clip_point_in_bounds: (0,0) is in bounds
- clip_point_in_bounds: (0,0) is in bounds


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("clip_point_in_bounds: (0,0) is in bounds")
step("clip_point_in_bounds: (0,0) is in bounds")
expect(clip_point_in_bounds(0, 0, 10, 10)).to_be_true()
```

</details>

#### clip_point_in_bounds: right edge (exclusive) is out of bounds

- clip_point_in_bounds: right edge (exclusive) is out of bounds
- clip_point_in_bounds: right edge (exclusive) is out of bounds


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("clip_point_in_bounds: right edge (exclusive) is out of bounds")
step("clip_point_in_bounds: right edge (exclusive) is out of bounds")
expect(clip_point_in_bounds(10, 5, 10, 10)).to_be_false()
```

</details>

#### clip_point_in_bounds: bottom edge (exclusive) is out of bounds

- clip_point_in_bounds: bottom edge (exclusive) is out of bounds
- clip_point_in_bounds: bottom edge (exclusive) is out of bounds


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("clip_point_in_bounds: bottom edge (exclusive) is out of bounds")
step("clip_point_in_bounds: bottom edge (exclusive) is out of bounds")
expect(clip_point_in_bounds(5, 10, 10, 10)).to_be_false()
```

</details>

#### clip_point_in_bounds: negative x is out of bounds

- clip_point_in_bounds: negative x is out of bounds
- clip_point_in_bounds: negative x is out of bounds


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("clip_point_in_bounds: negative x is out of bounds")
step("clip_point_in_bounds: negative x is out of bounds")
expect(clip_point_in_bounds(-1, 5, 10, 10)).to_be_false()
```

</details>

#### clip_point_in_rect: point inside clip rect

- clip_point_in_rect: point inside clip rect
- clip_point_in_rect: point inside clip rect


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("clip_point_in_rect: point inside clip rect")
step("clip_point_in_rect: point inside clip rect")
expect(clip_point_in_rect(6, 6, 5, 5, 5, 5)).to_be_true()
```

</details>

#### clip_point_in_rect: point outside clip rect

- clip_point_in_rect: point outside clip rect
- clip_point_in_rect: point outside clip rect


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("clip_point_in_rect: point outside clip rect")
step("clip_point_in_rect: point outside clip rect")
expect(clip_point_in_rect(3, 3, 5, 5, 5, 5)).to_be_false()
```

</details>

#### clip_pixel_allowed: no clip — passes bounds check

- clip_pixel_allowed: no clip — passes bounds check
- clip_pixel_allowed: no clip — passes bounds check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("clip_pixel_allowed: no clip — passes bounds check")
step("clip_pixel_allowed: no clip — passes bounds check")
expect(clip_pixel_allowed(3, 3, 10, 10, false, 0, 0, 10, 10)).to_be_true()
```

</details>

#### clip_pixel_allowed: clip enabled, point inside — allowed

- clip_pixel_allowed: clip enabled, point inside — allowed
- clip_pixel_allowed: clip enabled, point inside — allowed


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("clip_pixel_allowed: clip enabled, point inside — allowed")
step("clip_pixel_allowed: clip enabled, point inside — allowed")
expect(clip_pixel_allowed(6, 6, 10, 10, true, 5, 5, 5, 5)).to_be_true()
```

</details>

#### clip_pixel_allowed: clip enabled, point outside — blocked

- clip_pixel_allowed: clip enabled, point outside — blocked
- clip_pixel_allowed: clip enabled, point outside — blocked


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("clip_pixel_allowed: clip enabled, point outside — blocked")
step("clip_pixel_allowed: clip enabled, point outside — blocked")
expect(clip_pixel_allowed(3, 3, 10, 10, true, 5, 5, 5, 5)).to_be_false()
```

</details>

#### clip_pixel_allowed: out of framebuffer — blocked regardless of clip

- clip_pixel_allowed: out of framebuffer — blocked regardless of clip
- clip_pixel_allowed: out of framebuffer — blocked regardless of clip


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("clip_pixel_allowed: out of framebuffer — blocked regardless of clip")
step("clip_pixel_allowed: out of framebuffer — blocked regardless of clip")
expect(clip_pixel_allowed(-1, 5, 10, 10, false, 0, 0, 10, 10)).to_be_false()
```

</details>

#### rect_intersect_w: overlapping rects

- rect_intersect_w: overlapping rects
- rect_intersect_w: overlapping rects
   - Expected: w equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rect_intersect_w: overlapping rects")
step("rect_intersect_w: overlapping rects")
val w = rect_intersect_w(0, 8, 4, 8)
expect(w).to_equal(4)
```

</details>

#### rect_intersect_w: disjoint rects yields non-positive width

- rect_intersect_w: disjoint rects yields non-positive width
- rect_intersect_w: disjoint rects yields non-positive width


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rect_intersect_w: disjoint rects yields non-positive width")
step("rect_intersect_w: disjoint rects yields non-positive width")
val w = rect_intersect_w(0, 5, 10, 5)
expect(w <= 0).to_be_true()
```

</details>

#### rect_intersect_h: overlapping rects

- rect_intersect_h: overlapping rects
- rect_intersect_h: overlapping rects
   - Expected: h equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rect_intersect_h: overlapping rects")
step("rect_intersect_h: overlapping rects")
val h = rect_intersect_h(0, 8, 4, 8)
expect(h).to_equal(4)
```

</details>

#### clip_rect_to_viewport: rect fully inside

- clip_rect_to_viewport: rect fully inside
- clip_rect_to_viewport: rect fully inside


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("clip_rect_to_viewport: rect fully inside")
step("clip_rect_to_viewport: rect fully inside")
expect(clip_rect_to_viewport(1, 1, 5, 5, 10, 10)).to_be_true()
```

</details>

#### clip_rect_to_viewport: rect fully outside right

- clip_rect_to_viewport: rect fully outside right
- clip_rect_to_viewport: rect fully outside right


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("clip_rect_to_viewport: rect fully outside right")
step("clip_rect_to_viewport: rect fully outside right")
expect(clip_rect_to_viewport(15, 0, 5, 5, 10, 10)).to_be_false()
```

</details>

#### clip_rect_to_viewport: rect fully outside top

- clip_rect_to_viewport: rect fully outside top
- clip_rect_to_viewport: rect fully outside top


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("clip_rect_to_viewport: rect fully outside top")
step("clip_rect_to_viewport: rect fully outside top")
expect(clip_rect_to_viewport(0, -10, 5, 5, 10, 10)).to_be_false()
```

</details>

#### pixel_index: correct flat index

- pixel_index: correct flat index
- pixel_index: correct flat index
   - Expected: pixel_index(3, 2, 10) equals `23`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("pixel_index: correct flat index")
step("pixel_index: correct flat index")
expect(pixel_index(3, 2, 10)).to_equal(23)
```

</details>

### helpers_clip — mask

#### mask_blocks_at: empty mask never blocks

- mask_blocks_at: empty mask never blocks
- mask_blocks_at: empty mask never blocks


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("mask_blocks_at: empty mask never blocks")
step("mask_blocks_at: empty mask never blocks")
var empty_mask: [u8] = []
expect(mask_blocks_at(empty_mask, 10, 5, 5)).to_be_false()
```

</details>

#### mask_blocks_at: mask byte 0 blocks

- mask_blocks_at: mask byte 0 blocks
- mask_blocks_at: mask byte 0 blocks


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("mask_blocks_at: mask byte 0 blocks")
step("mask_blocks_at: mask byte 0 blocks")
var mask: [u8] = [1u8, 0u8, 1u8]
expect(mask_blocks_at(mask, 3, 1, 0)).to_be_true()
```

</details>

#### mask_blocks_at: mask byte 1 does not block

- mask_blocks_at: mask byte 1 does not block
- mask_blocks_at: mask byte 1 does not block


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("mask_blocks_at: mask byte 1 does not block")
step("mask_blocks_at: mask byte 1 does not block")
var mask: [u8] = [1u8, 0u8, 1u8]
expect(mask_blocks_at(mask, 3, 0, 0)).to_be_false()
```

</details>

#### mask_blocks_at: out-of-range coordinate does not block

- mask_blocks_at: out-of-range coordinate does not block
- mask_blocks_at: out-of-range coordinate does not block


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("mask_blocks_at: out-of-range coordinate does not block")
step("mask_blocks_at: out-of-range coordinate does not block")
var mask: [u8] = [0u8]
expect(mask_blocks_at(mask, 1, 5, 5)).to_be_false()
```

</details>

### helpers_pixel — buffer access

#### buf_get_pixel: returns 0 for out-of-bounds

- buf_get_pixel: returns 0 for out-of-bounds
- buf_get_pixel: returns 0 for out-of-bounds
   - Expected: buf_get_pixel(buf, 1, 0, 1, 1) equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("buf_get_pixel: returns 0 for out-of-bounds")
step("buf_get_pixel: returns 0 for out-of-bounds")
var buf: [u32] = [0xFFFF0000u32]
expect(buf_get_pixel(buf, 1, 0, 1, 1)).to_equal(0u32)
```

</details>

#### buf_get_pixel: reads in-bounds pixel

- buf_get_pixel: reads in-bounds pixel
- buf_get_pixel: reads in-bounds pixel
   - Expected: got equals `0xAABBCCDDu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("buf_get_pixel: reads in-bounds pixel")
step("buf_get_pixel: reads in-bounds pixel")
var buf: [u32] = [0u32, 0u32, 0xAABBCCDDu32, 0u32]
val got = buf_get_pixel(buf, 2, 0, 4, 1)
expect(got).to_equal(0xAABBCCDDu32)
```

</details>

#### buf_set_pixel: writes in-bounds pixel

- buf_set_pixel: writes in-bounds pixel
- buf_set_pixel: writes in-bounds pixel
   - Expected: buf[2] equals `0xDEADBEEFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("buf_set_pixel: writes in-bounds pixel")
step("buf_set_pixel: writes in-bounds pixel")
var buf: [u32] = [0u32, 0u32, 0u32, 0u32]
buf_set_pixel(buf, 2, 0, 4, 1, 0xDEADBEEFu32)
expect(buf[2]).to_equal(0xDEADBEEFu32)
```

</details>

#### buf_set_pixel: out-of-bounds write is ignored

- buf_set_pixel: out-of-bounds write is ignored
- buf_set_pixel: out-of-bounds write is ignored
   - Expected: buf[0] equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("buf_set_pixel: out-of-bounds write is ignored")
step("buf_set_pixel: out-of-bounds write is ignored")
var buf: [u32] = [0u32]
buf_set_pixel(buf, 5, 5, 1, 1, 0xFFFFFFFFu32)
expect(buf[0]).to_equal(0u32)
```

</details>

#### buf_set_pixel_blend: opaque src replaces dst

- buf_set_pixel_blend: opaque src replaces dst
- buf_set_pixel_blend: opaque src replaces dst
   - Expected: color_r(buf[0]) equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("buf_set_pixel_blend: opaque src replaces dst")
step("buf_set_pixel_blend: opaque src replaces dst")
var buf: [u32] = [rgb(0, 0, 0)]
val src = rgb(255, 0, 0)
buf_set_pixel_blend(buf, 0, 0, 1, 1, src)
expect(color_r(buf[0])).to_equal(255)
```

</details>

#### buf_set_pixel_blend: transparent src leaves dst unchanged

- buf_set_pixel_blend: transparent src leaves dst unchanged
- buf_set_pixel_blend: transparent src leaves dst unchanged
   - Expected: color_g(buf[0]) equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("buf_set_pixel_blend: transparent src leaves dst unchanged")
step("buf_set_pixel_blend: transparent src leaves dst unchanged")
var buf: [u32] = [rgb(0, 255, 0)]
val src = rgba(255, 0, 0, 0)
buf_set_pixel_blend(buf, 0, 0, 1, 1, src)
expect(color_g(buf[0])).to_equal(255)
```

</details>

### helpers_pixel — alpha compositing

#### alpha_premultiply: opaque color is unchanged

- alpha_premultiply: opaque color is unchanged
- alpha_premultiply: opaque color is unchanged
   - Expected: alpha_premultiply(c) equals `c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("alpha_premultiply: opaque color is unchanged")
step("alpha_premultiply: opaque color is unchanged")
val c = rgb(100, 150, 200)
expect(alpha_premultiply(c)).to_equal(c)
```

</details>

#### alpha_premultiply: transparent returns 0

- alpha_premultiply: transparent returns 0
- alpha_premultiply: transparent returns 0
   - Expected: alpha_premultiply(c) equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("alpha_premultiply: transparent returns 0")
step("alpha_premultiply: transparent returns 0")
val c = rgba(255, 255, 255, 0)
expect(alpha_premultiply(c)).to_equal(0u32)
```

</details>

#### alpha_premultiply: 50% alpha halves RGB

- alpha_premultiply: 50% alpha halves RGB
- alpha_premultiply: 50% alpha halves RGB


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("alpha_premultiply: 50% alpha halves RGB")
step("alpha_premultiply: 50% alpha halves RGB")
val c = rgba(200, 200, 200, 128)
val pm = alpha_premultiply(c)
val r = color_r(pm)
expect(r >= 98 and r <= 102).to_be_true()
```

</details>

#### alpha_unpremultiply: zero alpha returns 0

- alpha_unpremultiply: zero alpha returns 0
- alpha_unpremultiply: zero alpha returns 0
   - Expected: alpha_unpremultiply(0u32) equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("alpha_unpremultiply: zero alpha returns 0")
step("alpha_unpremultiply: zero alpha returns 0")
expect(alpha_unpremultiply(0u32)).to_equal(0u32)
```

</details>

#### alpha_unpremultiply: opaque color is unchanged

- alpha_unpremultiply: opaque color is unchanged
- alpha_unpremultiply: opaque color is unchanged
   - Expected: alpha_unpremultiply(c) equals `c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("alpha_unpremultiply: opaque color is unchanged")
step("alpha_unpremultiply: opaque color is unchanged")
val c = rgb(80, 160, 240)
expect(alpha_unpremultiply(c)).to_equal(c)
```

</details>

#### pixels_to_bytes: 4 bytes per pixel

- pixels_to_bytes: 4 bytes per pixel
- pixels_to_bytes: 4 bytes per pixel
   - Expected: pixels_to_bytes(10) equals `40`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("pixels_to_bytes: 4 bytes per pixel")
step("pixels_to_bytes: 4 bytes per pixel")
expect(pixels_to_bytes(10)).to_equal(40)
```

</details>

#### bytes_to_pixels: inverse of pixels_to_bytes

- bytes_to_pixels: inverse of pixels_to_bytes
- bytes_to_pixels: inverse of pixels_to_bytes
   - Expected: bytes_to_pixels(pixels_to_bytes(7)) equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("bytes_to_pixels: inverse of pixels_to_bytes")
step("bytes_to_pixels: inverse of pixels_to_bytes")
expect(bytes_to_pixels(pixels_to_bytes(7))).to_equal(7)
```

</details>

### helpers_text — dimensions

#### text_buf_height equals glyph_height at font_size 7

- text_buf_height equals glyph_height at font_size 7
- text_buf_height equals glyph_height at font_size 7
   - Expected: h equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("text_buf_height equals glyph_height at font_size 7")
step("text_buf_height equals glyph_height at font_size 7")
val h = text_buf_height(7)
expect(h).to_equal(7)
```

</details>

#### text_buf_height scales with font_size

- text_buf_height scales with font_size
- text_buf_height scales with font_size
   - Expected: h equals `14`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("text_buf_height scales with font_size")
step("text_buf_height scales with font_size")
val h = text_buf_height(14)
expect(h).to_equal(14)
```

</details>

#### text_buf_width: empty string returns 0

- text_buf_width: empty string returns 0
- text_buf_width: empty string returns 0
   - Expected: text_buf_width("", 7) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("text_buf_width: empty string returns 0")
step("text_buf_width: empty string returns 0")
expect(text_buf_width("", 7)).to_equal(0)
```

</details>

#### text_buf_width: single char at scale 1

- text_buf_width: single char at scale 1
- text_buf_width: single char at scale 1
   - Expected: text_buf_width("A", 7) equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("text_buf_width: single char at scale 1")
step("text_buf_width: single char at scale 1")
# advance = 5 * scale (unified with browser paint); scale = 7/7 = 1
expect(text_buf_width("A", 7)).to_equal(5)
```

</details>

#### text_buf_width: 3 chars at scale 1

- text_buf_width: 3 chars at scale 1
- text_buf_width: 3 chars at scale 1
   - Expected: text_buf_width("ABC", 7) equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("text_buf_width: 3 chars at scale 1")
step("text_buf_width: 3 chars at scale 1")
expect(text_buf_width("ABC", 7)).to_equal(15)
```

</details>

#### text_scale: font_size 7 gives scale 1

- text_scale: font_size 7 gives scale 1
- text_scale: font_size 7 gives scale 1
   - Expected: text_scale(7) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("text_scale: font_size 7 gives scale 1")
step("text_scale: font_size 7 gives scale 1")
expect(text_scale(7)).to_equal(1)
```

</details>

#### text_scale: font_size 14 gives scale 2

- text_scale: font_size 14 gives scale 2
- text_scale: font_size 14 gives scale 2
   - Expected: text_scale(14) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("text_scale: font_size 14 gives scale 2")
step("text_scale: font_size 14 gives scale 2")
expect(text_scale(14)).to_equal(2)
```

</details>

#### text_scale: font_size < 7 is clamped to 1

- text_scale: font_size < 7 is clamped to 1
- text_scale: font_size < 7 is clamped to 1
   - Expected: text_scale(1) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("text_scale: font_size < 7 is clamped to 1")
step("text_scale: font_size < 7 is clamped to 1")
expect(text_scale(1)).to_equal(1)
```

</details>

### helpers_text — render_to_buf

#### text_render_to_buf: empty text returns empty buffer

- text_render_to_buf: empty text returns empty buffer
- text_render_to_buf: empty text returns empty buffer
   - Expected: buf.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("text_render_to_buf: empty text returns empty buffer")
step("text_render_to_buf: empty text returns empty buffer")
val buf = text_render_to_buf("", 0xFFFFFFFFu32, 0xFF000000u32, 7)
expect(buf.len()).to_equal(0)
```

</details>

#### text_render_to_buf: buffer size matches dimensions

- text_render_to_buf: buffer size matches dimensions
- text_render_to_buf: buffer size matches dimensions
   - Expected: buf.len() equals `expected_len`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("text_render_to_buf: buffer size matches dimensions")
step("text_render_to_buf: buffer size matches dimensions")
val buf = text_render_to_buf("Hi", 0xFFFFFFFFu32, 0xFF000000u32, 7)
val expected_len = text_buf_width("Hi", 7) * text_buf_height(7)
expect(buf.len()).to_equal(expected_len)
```

</details>

#### text_render_to_buf: background color fills non-glyph pixels

- text_render_to_buf: background color fills non-glyph pixels
- text_render_to_buf: background color fills non-glyph pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("text_render_to_buf: background color fills non-glyph pixels")
step("text_render_to_buf: background color fills non-glyph pixels")
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
expect(all_bg).to_be_true()
```

</details>

#### text_render_to_buf: parity with inline draw_text_bg pattern

- text_render_to_buf: parity with inline draw_text_bg pattern
- text_render_to_buf: parity with inline draw_text_bg pattern
   - Expected: helper_buf.len() equals `inline_buf.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("text_render_to_buf: parity with inline draw_text_bg pattern")
step("text_render_to_buf: parity with inline draw_text_bg pattern")
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
render_text_to_buffer(inline_buf, text_w, text_h, 0, 0, text_val, fg, font_size)
val helper_buf = text_render_to_buf(text_val, fg, bg, font_size)
expect(helper_buf.len()).to_equal(inline_buf.len())
var match_ok = true
var ci = 0
while ci < inline_buf.len():
    if inline_buf[ci] != helper_buf[ci]:
        match_ok = false
    ci = ci + 1
expect(match_ok).to_be_true()
```

</details>

### helpers_availability — backend names

#### backend_display_name: cuda

- backend_display_name: cuda
- backend_display_name: cuda
   - Expected: n equals `NVIDIA CUDA`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("backend_display_name: cuda")
step("backend_display_name: cuda")
val n = backend_display_name("cuda")
expect(n).to_equal("NVIDIA CUDA")
```

</details>

#### backend_display_name: vulkan

- backend_display_name: vulkan
- backend_display_name: vulkan
   - Expected: n equals `Vulkan Compute`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("backend_display_name: vulkan")
step("backend_display_name: vulkan")
val n = backend_display_name("vulkan")
expect(n).to_equal("Vulkan Compute")
```

</details>

#### backend_display_name: cpu

- backend_display_name: cpu
- backend_display_name: cpu
   - Expected: n equals `CPU Software (fallback)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("backend_display_name: cpu")
step("backend_display_name: cpu")
val n = backend_display_name("cpu")
expect(n).to_equal("CPU Software (fallback)")
```

</details>

#### backend_display_name: unknown

- backend_display_name: unknown
- backend_display_name: unknown


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("backend_display_name: unknown")
step("backend_display_name: unknown")
val n = backend_display_name("unknown_xyz")
expect(n.starts_with("Unknown")).to_be_true()
```

</details>

#### backend_priority: cuda is highest priority (0)

- backend_priority: cuda is highest priority (0)
- backend_priority: cuda is highest priority (0)
   - Expected: backend_priority("cuda") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("backend_priority: cuda is highest priority (0)")
step("backend_priority: cuda is highest priority (0)")
expect(backend_priority("cuda")).to_equal(0)
```

</details>

#### backend_priority: cpu is lowest priority (9)

- backend_priority: cpu is lowest priority (9)
- backend_priority: cpu is lowest priority (9)
   - Expected: backend_priority("cpu") equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("backend_priority: cpu is lowest priority (9)")
step("backend_priority: cpu is lowest priority (9)")
expect(backend_priority("cpu")).to_equal(9)
```

</details>

#### backend_priority: vulkan < software < cpu

- backend_priority: vulkan < software < cpu
- backend_priority: vulkan < software < cpu


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("backend_priority: vulkan < software < cpu")
step("backend_priority: vulkan < software < cpu")
val v = backend_priority("vulkan")
val s = backend_priority("software")
val c = backend_priority("cpu")
expect(v < s).to_be_true()
expect(s < c).to_be_true()
```

</details>

#### backend_is_hardware: cuda is hardware

- backend_is_hardware: cuda is hardware
- backend_is_hardware: cuda is hardware


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("backend_is_hardware: cuda is hardware")
step("backend_is_hardware: cuda is hardware")
expect(backend_is_hardware("cuda")).to_be_true()
```

</details>

#### backend_is_hardware: cpu is not hardware

- backend_is_hardware: cpu is not hardware
- backend_is_hardware: cpu is not hardware


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("backend_is_hardware: cpu is not hardware")
step("backend_is_hardware: cpu is not hardware")
expect(backend_is_hardware("cpu")).to_be_false()
```

</details>

#### backend_is_hardware: software is not hardware

- backend_is_hardware: software is not hardware
- backend_is_hardware: software is not hardware


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("backend_is_hardware: software is not hardware")
step("backend_is_hardware: software is not hardware")
expect(backend_is_hardware("software")).to_be_false()
```

</details>

#### backend_requires_gpu: cuda requires GPU

- backend_requires_gpu: cuda requires GPU
- backend_requires_gpu: cuda requires GPU


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("backend_requires_gpu: cuda requires GPU")
step("backend_requires_gpu: cuda requires GPU")
expect(backend_requires_gpu("cuda")).to_be_true()
```

</details>

#### backend_requires_gpu: vulkan does not require (can software fallback)

- backend_requires_gpu: vulkan does not require (can software fallback)
- backend_requires_gpu: vulkan does not require (can software fallback)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("backend_requires_gpu: vulkan does not require (can software fallback)")
step("backend_requires_gpu: vulkan does not require (can software fallback)")
expect(backend_requires_gpu("vulkan")).to_be_false()
```

</details>

#### backend_requires_gpu: cpu does not require GPU

- backend_requires_gpu: cpu does not require GPU
- backend_requires_gpu: cpu does not require GPU


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("backend_requires_gpu: cpu does not require GPU")
step("backend_requires_gpu: cpu does not require GPU")
expect(backend_requires_gpu("cpu")).to_be_false()
```

</details>

#### feature_gate_description: returns non-empty text for all known backends

- feature_gate_description: returns non-empty text for all known backends
- feature_gate_description: returns non-empty text for all known backends


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("feature_gate_description: returns non-empty text for all known backends")
step("feature_gate_description: returns non-empty text for all known backends")
val names = ["cuda", "rocm", "metal", "qualcomm", "vulkan", "opengl", "intel", "webgpu", "software", "cpu"]
var all_ok = true
var ni = 0
while ni < 10:
    val desc = feature_gate_description(names[ni])
    if desc.len() == 0:
        all_ok = false
    ni = ni + 1
expect(all_ok).to_be_true()
```

</details>

### helpers_availability — numeric conversions

#### backend_i64: converts i32 to i64

- backend_i64: converts i32 to i64
- backend_i64: converts i32 to i64
   - Expected: backend_i64(42) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("backend_i64: converts i32 to i64")
step("backend_i64: converts i32 to i64")
expect(backend_i64(42)).to_equal(42)
```

</details>

#### backend_i64: handles negative

- backend_i64: handles negative
- backend_i64: handles negative
   - Expected: backend_i64(-1) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("backend_i64: handles negative")
step("backend_i64: handles negative")
expect(backend_i64(-1)).to_equal(-1)
```

</details>

#### backend_bool_to_i32: true -> 1

- backend_bool_to_i32: true -> 1
- backend_bool_to_i32: true -> 1
   - Expected: backend_bool_to_i32(true) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("backend_bool_to_i32: true -> 1")
step("backend_bool_to_i32: true -> 1")
expect(backend_bool_to_i32(true)).to_equal(1)
```

</details>

#### backend_bool_to_i32: false -> 0

- backend_bool_to_i32: false -> 0
- backend_bool_to_i32: false -> 0
   - Expected: backend_bool_to_i32(false) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("backend_bool_to_i32: false -> 0")
step("backend_bool_to_i32: false -> 0")
expect(backend_bool_to_i32(false)).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 65 |
| Active scenarios | 65 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
- `REQ-HELPERSPARITY-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `cf42b09993954e648a58b41394df301c4bd6baf96397de74f62bc4796811beda`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cf42b09993954e648a58b41394df301c4bd6baf96397de74f62bc4796811beda`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cf42b09993954e648a58b41394df301c4bd6baf96397de74f62bc4796811beda`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/integration/rendering/helpers_parity_spec.spl
mirror: doc/06_spec/integration/rendering/helpers_parity_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/rendering/helpers_parity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/rendering/helpers_parity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/rendering/helpers_parity_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 22 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/rendering/helpers_parity_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'clip_point_in_bounds: interior point is in bounds' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/rendering/helpers_parity_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'clip_point_in_bounds: (0,0) is in bounds' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/rendering/helpers_parity_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'clip_point_in_bounds: right edge (exclusive) is out of bounds' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
