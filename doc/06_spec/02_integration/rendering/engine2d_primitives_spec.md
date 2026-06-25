# Engine2d Primitives Specification

> 1. var engine = make engine

<!-- sdn-diagram:id=engine2d_primitives_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=engine2d_primitives_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

engine2d_primitives_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=engine2d_primitives_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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

1. var engine = make engine

2. engine clear

3. engine present
   - Expected: pixel_at(pixels, 0, 0, 100) equals `red`
   - Expected: pixel_at(pixels, 99, 0, 100) equals `red`
   - Expected: pixel_at(pixels, 0, 99, 100) equals `red`
   - Expected: pixel_at(pixels, 99, 99, 100) equals `red`
   - Expected: pixel_at(pixels, 50, 50, 100) equals `red`

4. engine shutdown


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var engine = make engine

2. engine clear

3. engine clear

4. engine present
   - Expected: pixel_at(pixels, 50, 50, 100) equals `blue`

5. engine shutdown


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var engine = make engine

2. engine draw rect filled

3. engine present
   - Expected: pixel_at(pixels, 15, 15, 100) equals `green`
   - Expected: pixel_at(pixels, 10, 10, 100) equals `green`
   - Expected: pixel_at(pixels, 29, 29, 100) equals `green`

4. engine shutdown


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var engine = make engine

2. engine draw rect filled

3. engine present
   - Expected: pixel_at(pixels, 5, 5, 100) equals `bg`
   - Expected: pixel_at(pixels, 50, 50, 100) equals `bg`
   - Expected: pixel_at(pixels, 9, 15, 100) equals `bg`
   - Expected: pixel_at(pixels, 15, 9, 100) equals `bg`

4. engine shutdown


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var engine = make engine

2. engine draw rect filled

3. engine present
   - Expected: pixel_at(pixels, 0, 0, 100) equals `white`
   - Expected: pixel_at(pixels, 4, 4, 100) equals `white`
   - Expected: pixel_at(pixels, 5, 5, 100) equals `rgb(0, 0, 0)`

4. engine shutdown


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var engine = make engine

2. engine draw circle filled

3. engine present
   - Expected: pixel_at(pixels, 50, 50, 100) equals `yellow`

4. engine shutdown


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var engine = make engine

2. engine draw circle filled

3. engine present
   - Expected: pixel_at(pixels, 50, 50, 100) equals `cyan`
   - Expected: pixel_at(pixels, 45, 50, 100) equals `cyan`
   - Expected: pixel_at(pixels, 55, 50, 100) equals `cyan`
   - Expected: pixel_at(pixels, 50, 45, 100) equals `cyan`
   - Expected: pixel_at(pixels, 50, 55, 100) equals `cyan`

4. engine shutdown


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var engine = make engine

2. engine draw circle filled

3. engine present
   - Expected: pixel_at(pixels, 5, 5, 100) equals `bg`
   - Expected: pixel_at(pixels, 95, 95, 100) equals `bg`

4. engine shutdown


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var engine = make engine

2. engine draw line

3. engine present
   - Expected: pixel_at(pixels, 0, 0, 100) equals `white`
   - Expected: pixel_at(pixels, 50, 0, 100) equals `white`
   - Expected: pixel_at(pixels, 99, 0, 100) equals `white`

4. engine shutdown


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var engine = make engine

2. engine draw line

3. engine present
   - Expected: pixel_at(pixels, 50, 1, 100) equals `bg`

4. engine shutdown


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var engine = make engine

2. engine draw line

3. engine present
   - Expected: pixel_at(pixels, 10, 0, 100) equals `magenta`
   - Expected: pixel_at(pixels, 10, 50, 100) equals `magenta`
   - Expected: pixel_at(pixels, 10, 99, 100) equals `magenta`

4. engine shutdown


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var engine = make engine

2. engine draw gradient rect

3. engine present
   - Expected: top_px equals `top_color`
   - Expected: bottom_px equals `bottom_color`

4. engine shutdown


<details>
<summary>Executable SPipe</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var engine = make engine

2. engine draw gradient rect

3. engine present

4. engine shutdown


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var engine = make engine

2. engine draw text

3. engine present
   - Expected: found_text_pixel is true

4. engine shutdown


<details>
<summary>Executable SPipe</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var engine = make engine

2. engine draw rounded rect

3. engine present
   - Expected: pixel_at(pixels, 50, 10, 100) equals `color`

4. engine shutdown


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var engine = make engine

2. engine draw triangle filled

3. engine present
   - Expected: pixel_at(pixels, 50, 60, 100) equals `orange`

4. engine shutdown


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var engine = make engine

2. engine set clip

3. engine draw rect filled

4. engine present
   - Expected: pixel_at(pixels, 70, 70, 100) equals `bg`

5. engine shutdown


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var engine = make engine

2. engine set clip

3. engine draw rect filled

4. engine present
   - Expected: pixel_at(pixels, 15, 15, 100) equals `blue`

5. engine shutdown


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var engine = make engine

2. engine set clip

3. engine clear clip

4. engine draw rect filled

5. engine present
   - Expected: pixel_at(pixels, 70, 70, 100) equals `green`

6. engine shutdown


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var engine = make engine

2. engine draw image

3. engine present
   - Expected: pixel_at(pixels, 10, 10, 100) equals `red`
   - Expected: pixel_at(pixels, 11, 10, 100) equals `green`
   - Expected: pixel_at(pixels, 10, 11, 100) equals `green`
   - Expected: pixel_at(pixels, 11, 11, 100) equals `red`

4. engine shutdown


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var engine = make engine

2. engine draw image

3. engine present
   - Expected: pixel_at(pixels, 19, 20, 100) equals `bg`
   - Expected: pixel_at(pixels, 22, 20, 100) equals `bg`
   - Expected: pixel_at(pixels, 20, 19, 100) equals `bg`
   - Expected: pixel_at(pixels, 20, 22, 100) equals `bg`

4. engine shutdown


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var engine = make engine
   - Expected: pixels.len() equals `10000`

2. engine shutdown


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = make_engine()
val pixels = engine.read_pixels()
expect(pixels.len()).to_equal(10000)
engine.shutdown()
```

</details>

#### returns a copy that does not change after further drawing

1. var engine = make engine

2. engine clear

3. engine present
   - Expected: pixel_at(snapshot, 0, 0, 100) equals `red`

4. engine clear

5. engine present
   - Expected: pixel_at(snapshot, 0, 0, 100) equals `red`

6. engine shutdown


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/02_integration/rendering/engine2d_primitives_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
