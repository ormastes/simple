# Engine2d Primitives Specification

> Tests covering Engine2D Primitive Rendering.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine2d Primitives Specification

## Scenarios

### Engine2D Primitive Rendering

#### clear

#### fills entire buffer with color

- fills entire buffer with color
   - Expected: pixel_at(pixels, 0, 0, 100) equals `red`
   - Expected: pixel_at(pixels, 99, 0, 100) equals `red`
   - Expected: pixel_at(pixels, 0, 99, 100) equals `red`
   - Expected: pixel_at(pixels, 99, 99, 100) equals `red`
   - Expected: pixel_at(pixels, 50, 50, 100) equals `red`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fills entire buffer with color")
var engine = make_engine()
val red = rgb(255, 0, 0)
engine.clear(red)
engine.present()
val pixels = engine.read_pixels()
# Check corners and center
expect(pixel_at(pixels, 0, 0, 100)).to_equal(red)
expect(pixel_at(pixels, 99, 0, 100)).to_equal(red)
expect(pixel_at(pixels, 0, 99, 100)).to_equal(red)
expect(pixel_at(pixels, 99, 99, 100)).to_equal(red)
expect(pixel_at(pixels, 50, 50, 100)).to_equal(red)
engine.shutdown()
```

</details>

#### overwrites previous content

- overwrites previous content
   - Expected: pixel_at(pixels, 50, 50, 100) equals `blue`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("overwrites previous content")
var engine = make_engine()
engine.clear(rgb(255, 0, 0))
engine.clear(rgb(0, 0, 255))
engine.present()
val pixels = engine.read_pixels()
val blue = rgb(0, 0, 255)
expect(pixel_at(pixels, 50, 50, 100)).to_equal(blue)
engine.shutdown()
```

</details>

#### draw_rect_filled

#### produces colored region at target coordinates

- produces colored region at target coordinates
   - Expected: pixel_at(pixels, 15, 15, 100) equals `green`
   - Expected: pixel_at(pixels, 10, 10, 100) equals `green`
   - Expected: pixel_at(pixels, 29, 29, 100) equals `green`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("produces colored region at target coordinates")
var engine = make_engine()
val green = rgb(0, 255, 0)
engine.draw_rect_filled(10, 10, 20, 20, green)
engine.present()
val pixels = engine.read_pixels()
# Center of the rectangle
expect(pixel_at(pixels, 15, 15, 100)).to_equal(green)
# Top-left corner of the rectangle
expect(pixel_at(pixels, 10, 10, 100)).to_equal(green)
# Bottom-right just inside
expect(pixel_at(pixels, 29, 29, 100)).to_equal(green)
engine.shutdown()
```

</details>

#### does not affect pixels outside the rectangle

- does not affect pixels outside the rectangle
   - Expected: pixel_at(pixels, 5, 5, 100) equals `bg`
   - Expected: pixel_at(pixels, 50, 50, 100) equals `bg`
   - Expected: pixel_at(pixels, 9, 15, 100) equals `bg`
   - Expected: pixel_at(pixels, 15, 9, 100) equals `bg`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("does not affect pixels outside the rectangle")
var engine = make_engine()
val bg = rgb(0, 0, 0)
val green = rgb(0, 255, 0)
engine.draw_rect_filled(10, 10, 20, 20, green)
engine.present()
val pixels = engine.read_pixels()
# Pixels clearly outside the rect should remain background
expect(pixel_at(pixels, 5, 5, 100)).to_equal(bg)
expect(pixel_at(pixels, 50, 50, 100)).to_equal(bg)
expect(pixel_at(pixels, 9, 15, 100)).to_equal(bg)
expect(pixel_at(pixels, 15, 9, 100)).to_equal(bg)
engine.shutdown()
```

</details>

#### handles rectangle at origin

- handles rectangle at origin
   - Expected: pixel_at(pixels, 0, 0, 100) equals `white`
   - Expected: pixel_at(pixels, 4, 4, 100) equals `white`
   - Expected: pixel_at(pixels, 5, 5, 100) equals `rgb(0, 0, 0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles rectangle at origin")
var engine = make_engine()
val white = rgb(255, 255, 255)
engine.draw_rect_filled(0, 0, 5, 5, white)
engine.present()
val pixels = engine.read_pixels()
expect(pixel_at(pixels, 0, 0, 100)).to_equal(white)
expect(pixel_at(pixels, 4, 4, 100)).to_equal(white)
expect(pixel_at(pixels, 5, 5, 100)).to_equal(rgb(0, 0, 0))
engine.shutdown()
```

</details>

#### draw_circle_filled

#### center pixel has the drawn color

- center pixel has the drawn color
   - Expected: pixel_at(pixels, 50, 50, 100) equals `yellow`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("center pixel has the drawn color")
var engine = make_engine()
val yellow = rgb(255, 255, 0)
engine.draw_circle_filled(50, 50, 10, yellow)
engine.present()
val pixels = engine.read_pixels()
# Center of the circle
expect(pixel_at(pixels, 50, 50, 100)).to_equal(yellow)
engine.shutdown()
```

</details>

#### pixels near center are filled

- pixels near center are filled
   - Expected: pixel_at(pixels, 50, 50, 100) equals `cyan`
   - Expected: pixel_at(pixels, 45, 50, 100) equals `cyan`
   - Expected: pixel_at(pixels, 55, 50, 100) equals `cyan`
   - Expected: pixel_at(pixels, 50, 45, 100) equals `cyan`
   - Expected: pixel_at(pixels, 50, 55, 100) equals `cyan`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("pixels near center are filled")
var engine = make_engine()
val cyan = rgb(0, 255, 255)
engine.draw_circle_filled(50, 50, 15, cyan)
engine.present()
val pixels = engine.read_pixels()
# Several points well inside the radius
expect(pixel_at(pixels, 50, 50, 100)).to_equal(cyan)
expect(pixel_at(pixels, 45, 50, 100)).to_equal(cyan)
expect(pixel_at(pixels, 55, 50, 100)).to_equal(cyan)
expect(pixel_at(pixels, 50, 45, 100)).to_equal(cyan)
expect(pixel_at(pixels, 50, 55, 100)).to_equal(cyan)
engine.shutdown()
```

</details>

#### pixels far outside circle are background

- pixels far outside circle are background
   - Expected: pixel_at(pixels, 5, 5, 100) equals `bg`
   - Expected: pixel_at(pixels, 95, 95, 100) equals `bg`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("pixels far outside circle are background")
var engine = make_engine()
val bg = rgb(0, 0, 0)
engine.draw_circle_filled(50, 50, 10, rgb(255, 0, 0))
engine.present()
val pixels = engine.read_pixels()
# Well outside the circle
expect(pixel_at(pixels, 5, 5, 100)).to_equal(bg)
expect(pixel_at(pixels, 95, 95, 100)).to_equal(bg)
engine.shutdown()
```

</details>

#### draw_line

#### produces pixels along a horizontal path

- produces pixels along a horizontal path
   - Expected: pixel_at(pixels, 0, 0, 100) equals `white`
   - Expected: pixel_at(pixels, 50, 0, 100) equals `white`
   - Expected: pixel_at(pixels, 99, 0, 100) equals `white`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("produces pixels along a horizontal path")
var engine = make_engine()
val white = rgb(255, 255, 255)
engine.draw_line(0, 0, 99, 0, white, 1)
engine.present()
val pixels = engine.read_pixels()
# Sample several points along row 0
expect(pixel_at(pixels, 0, 0, 100)).to_equal(white)
expect(pixel_at(pixels, 50, 0, 100)).to_equal(white)
expect(pixel_at(pixels, 99, 0, 100)).to_equal(white)
engine.shutdown()
```

</details>

#### does not draw on unrelated rows

- does not draw on unrelated rows
   - Expected: pixel_at(pixels, 50, 1, 100) equals `bg`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("does not draw on unrelated rows")
var engine = make_engine()
val bg = rgb(0, 0, 0)
engine.draw_line(0, 0, 99, 0, rgb(255, 255, 255), 1)
engine.present()
val pixels = engine.read_pixels()
# Row 1 should be untouched
expect(pixel_at(pixels, 50, 1, 100)).to_equal(bg)
engine.shutdown()
```

</details>

#### draws a vertical line

- draws a vertical line
   - Expected: pixel_at(pixels, 10, 0, 100) equals `magenta`
   - Expected: pixel_at(pixels, 10, 50, 100) equals `magenta`
   - Expected: pixel_at(pixels, 10, 99, 100) equals `magenta`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("draws a vertical line")
var engine = make_engine()
val magenta = rgb(255, 0, 255)
engine.draw_line(10, 0, 10, 99, magenta, 1)
engine.present()
val pixels = engine.read_pixels()
expect(pixel_at(pixels, 10, 0, 100)).to_equal(magenta)
expect(pixel_at(pixels, 10, 50, 100)).to_equal(magenta)
expect(pixel_at(pixels, 10, 99, 100)).to_equal(magenta)
engine.shutdown()
```

</details>

#### draw_gradient_rect

#### top pixel differs from bottom pixel

- top pixel differs from bottom pixel
   - Expected: top_px equals `top_color`
   - Expected: bottom_px equals `bottom_color`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("top pixel differs from bottom pixel")
var engine = make_engine()
val top_color = rgb(255, 0, 0)
val bottom_color = rgb(0, 0, 255)
engine.draw_gradient_rect(0, 0, 100, 100, top_color, bottom_color)
engine.present()
val pixels = engine.read_pixels()
val top_px = pixel_at(pixels, 50, 0, 100)
val bottom_px = pixel_at(pixels, 50, 99, 100)
# Top row should be pure red, bottom row pure blue
expect(top_px).to_equal(top_color)
expect(bottom_px).to_equal(bottom_color)
# They must differ
val top_r = color_r(top_px)
val bottom_r = color_r(bottom_px)
expect(top_r).to_be_greater_than(bottom_r)
engine.shutdown()
```

</details>

#### middle row is an interpolated color

- middle row is an interpolated color


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("middle row is an interpolated color")
var engine = make_engine()
engine.draw_gradient_rect(0, 0, 100, 100, rgb(255, 0, 0), rgb(0, 0, 255))
engine.present()
val pixels = engine.read_pixels()
val mid_px = pixel_at(pixels, 50, 50, 100)
val mid_r = color_r(mid_px)
val mid_b = color_b(mid_px)
# At the middle row, red and blue should both be present (neither 0 nor 255)
expect(mid_r).to_be_greater_than(0)
expect(mid_r).to_be_less_than(255)
expect(mid_b).to_be_greater_than(0)
expect(mid_b).to_be_less_than(255)
engine.shutdown()
```

</details>

#### draw_text

#### produces non-background pixels

- produces non-background pixels
   - Expected: found_text_pixel is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("produces non-background pixels")
var engine = make_engine()
val bg = rgb(0, 0, 0)
val text_color = rgb(255, 255, 255)
engine.draw_text(10, 10, "A", text_color, 2)
engine.present()
val pixels = engine.read_pixels()
# Scan a region around the text location for any non-background pixel
var found_text_pixel = false
var sy = 10
while sy < 30:
    var sx = 10
    while sx < 30:
        if pixel_at(pixels, sx, sy, 100) != bg:
            found_text_pixel = true
        sx = sx + 1
    sy = sy + 1
expect(found_text_pixel).to_equal(true)
engine.shutdown()
```

</details>

#### draw_rounded_rect

#### center region has the drawn color

- center region has the drawn color
   - Expected: pixel_at(pixels, 50, 10, 100) equals `color`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("center region has the drawn color")
var engine = make_engine()
val color = rgb(128, 64, 200)
# draw_rounded_rect is outline-only, so check a point on the edge
# Draw a large rounded rect and check the top-center point on the edge
engine.draw_rounded_rect(10, 10, 80, 80, 5, color)
engine.present()
val pixels = engine.read_pixels()
# Top edge center (between corners) should have the color
expect(pixel_at(pixels, 50, 10, 100)).to_equal(color)
engine.shutdown()
```

</details>

#### draw_triangle_filled

#### interior pixel has the drawn color

- interior pixel has the drawn color
   - Expected: pixel_at(pixels, 50, 60, 100) equals `orange`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("interior pixel has the drawn color")
var engine = make_engine()
val orange = rgb(255, 128, 0)
# Triangle covering a region around (50, 50)
engine.draw_triangle_filled(50, 20, 20, 80, 80, 80, orange)
engine.present()
val pixels = engine.read_pixels()
# Centroid is roughly at (50, 60) — well inside
expect(pixel_at(pixels, 50, 60, 100)).to_equal(orange)
engine.shutdown()
```

</details>

#### set_clip and clear_clip

#### clip limits drawing to clip region

- clip limits drawing to clip region
   - Expected: pixel_at(pixels, 70, 70, 100) equals `bg`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("clip limits drawing to clip region")
var engine = make_engine()
val bg = rgb(0, 0, 0)
val red = rgb(255, 0, 0)
# Set clip to upper-left quadrant
engine.set_clip(0, 0, 50, 50)
# Draw a rect entirely outside the clip region
engine.draw_rect_filled(60, 60, 20, 20, red)
engine.present()
val pixels = engine.read_pixels()
# The rect at (60,60) should NOT appear because it is outside the clip
expect(pixel_at(pixels, 70, 70, 100)).to_equal(bg)
engine.shutdown()
```

</details>

#### clip allows drawing inside clip region

- clip allows drawing inside clip region
   - Expected: pixel_at(pixels, 15, 15, 100) equals `blue`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("clip allows drawing inside clip region")
var engine = make_engine()
val blue = rgb(0, 0, 255)
engine.set_clip(0, 0, 50, 50)
# Draw a rect inside the clip region
engine.draw_rect_filled(10, 10, 20, 20, blue)
engine.present()
val pixels = engine.read_pixels()
expect(pixel_at(pixels, 15, 15, 100)).to_equal(blue)
engine.shutdown()
```

</details>

#### clear_clip allows full drawing

- clear_clip allows full drawing
   - Expected: pixel_at(pixels, 70, 70, 100) equals `green`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("clear_clip allows full drawing")
var engine = make_engine()
val bg = rgb(0, 0, 0)
val green = rgb(0, 255, 0)
# Set clip to upper-left, then clear it
engine.set_clip(0, 0, 50, 50)
engine.clear_clip()
# Now drawing outside the original clip should work
engine.draw_rect_filled(60, 60, 20, 20, green)
engine.present()
val pixels = engine.read_pixels()
expect(pixel_at(pixels, 70, 70, 100)).to_equal(green)
engine.shutdown()
```

</details>

#### draw_image

#### blits pixel data onto framebuffer

- blits pixel data onto framebuffer
   - Expected: pixel_at(pixels, 10, 10, 100) equals `red`
   - Expected: pixel_at(pixels, 11, 10, 100) equals `green`
   - Expected: pixel_at(pixels, 10, 11, 100) equals `green`
   - Expected: pixel_at(pixels, 11, 11, 100) equals `red`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("blits pixel data onto framebuffer")
var engine = make_engine()
val red = rgb(255, 0, 0)
val green = rgb(0, 255, 0)
# Create a 2x2 image: red, green, green, red
var img: [u32] = [red, green, green, red]
engine.draw_image(10, 10, 2, 2, img)
engine.present()
val pixels = engine.read_pixels()
expect(pixel_at(pixels, 10, 10, 100)).to_equal(red)
expect(pixel_at(pixels, 11, 10, 100)).to_equal(green)
expect(pixel_at(pixels, 10, 11, 100)).to_equal(green)
expect(pixel_at(pixels, 11, 11, 100)).to_equal(red)
engine.shutdown()
```

</details>

#### does not affect pixels outside image bounds

- does not affect pixels outside image bounds
   - Expected: pixel_at(pixels, 19, 20, 100) equals `bg`
   - Expected: pixel_at(pixels, 22, 20, 100) equals `bg`
   - Expected: pixel_at(pixels, 20, 19, 100) equals `bg`
   - Expected: pixel_at(pixels, 20, 22, 100) equals `bg`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("does not affect pixels outside image bounds")
var engine = make_engine()
val bg = rgb(0, 0, 0)
val white = rgb(255, 255, 255)
var img: [u32] = [white, white, white, white]
engine.draw_image(20, 20, 2, 2, img)
engine.present()
val pixels = engine.read_pixels()
# Adjacent pixels remain background
expect(pixel_at(pixels, 19, 20, 100)).to_equal(bg)
expect(pixel_at(pixels, 22, 20, 100)).to_equal(bg)
expect(pixel_at(pixels, 20, 19, 100)).to_equal(bg)
expect(pixel_at(pixels, 20, 22, 100)).to_equal(bg)
engine.shutdown()
```

</details>

#### read_pixels

#### returns correct buffer size

- returns correct buffer size
   - Expected: pixels.len() equals `10000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("returns correct buffer size")
var engine = make_engine()
val pixels = engine.read_pixels()
expect(pixels.len()).to_equal(10000)
engine.shutdown()
```

</details>

#### returns a copy that does not change after further drawing

- returns a copy that does not change after further drawing
   - Expected: pixel_at(snapshot, 0, 0, 100) equals `red`
   - Expected: pixel_at(snapshot, 0, 0, 100) equals `red`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("returns a copy that does not change after further drawing")
var engine = make_engine()
engine.clear(rgb(255, 0, 0))
engine.present()
val snapshot = engine.read_pixels()
val red = rgb(255, 0, 0)
expect(pixel_at(snapshot, 0, 0, 100)).to_equal(red)
# Draw something else
engine.clear(rgb(0, 0, 255))
engine.present()
# The snapshot should still be red
expect(pixel_at(snapshot, 0, 0, 100)).to_equal(red)
engine.shutdown()
```

</details>

#### software and cpu parity

#### renders the core primitive scene bit-exactly

- renders the core primitive scene bit-exactly
   - Expected: pixels_equal(software, cpu) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("renders the core primitive scene bit-exactly")
val software = render_parity_scene("software")
val cpu = render_parity_scene("cpu")
expect(pixels_equal(software, cpu)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/rendering/engine2d_primitives_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Engine2D Primitive Rendering.
- Engine2D Primitive Rendering

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
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

- Canonical SPipe generation for source `47dc9cc9f89a0c9940d036033de25c3b3d9d659a95e19d4a6c1093f9dc59078f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `47dc9cc9f89a0c9940d036033de25c3b3d9d659a95e19d4a6c1093f9dc59078f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `47dc9cc9f89a0c9940d036033de25c3b3d9d659a95e19d4a6c1093f9dc59078f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/integration/rendering/engine2d_primitives_spec.spl
mirror: doc/06_spec/integration/rendering/engine2d_primitives_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/rendering/engine2d_primitives_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/rendering/engine2d_primitives_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/rendering/engine2d_primitives_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/rendering/engine2d_primitives_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fills entire buffer with color' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/rendering/engine2d_primitives_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'overwrites previous content' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/rendering/engine2d_primitives_spec.spl:108:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces colored region at target coordinates' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
