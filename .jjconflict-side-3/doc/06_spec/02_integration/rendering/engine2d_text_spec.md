# Engine2d Text Specification

> 1. var engine = Engine2D create with backend

<!-- sdn-diagram:id=engine2d_text_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=engine2d_text_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

engine2d_text_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=engine2d_text_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine2d Text Specification

## Scenarios

### Engine2D Text Rendering

#### cpu backend

#### draw_text renders non-zero pixels in the glyph area

1. var engine = Engine2D create with backend
2. engine clear
3. engine draw text
4. engine present
   - Expected: found is true
5. engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# draw_text uses FontRenderer (8x16 bitmap + bearing offsets), so
# we scan the first 20x20 region for any non-black pixel rather
# than asserting a specific coordinate.
var engine = Engine2D.create_with_backend(50, 20, "cpu")
engine.clear(rgb(0, 0, 0))
engine.draw_text(0, 0, "A", rgb(255, 255, 255), 14)
engine.present()
val pixels = engine.read_pixels()
val found = any_nonblack_in_region(pixels, 0, 0, 20, 20, 50)
expect(found).to_equal(true)
engine.shutdown()
```

</details>

#### draw_text leaves pixels outside the glyph area unchanged

1. var engine = Engine2D create with backend
2. engine clear
3. engine draw text
4. engine present
   - Expected: color_r(p) equals `0`
   - Expected: color_g(p) equals `0`
   - Expected: color_b(p) equals `0`
5. engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Draw "A" at (0,0) with font_size=14.  The glyph fits in roughly
# 8x14 px.  A pixel at (45, 18) is well outside that — must remain
# the black background.
var engine = Engine2D.create_with_backend(50, 20, "cpu")
engine.clear(rgb(0, 0, 0))
engine.draw_text(0, 0, "A", rgb(255, 255, 255), 14)
engine.present()
val pixels = engine.read_pixels()
val p = text_pixel_at(pixels, 45, 18, 50)
expect(color_r(p)).to_equal(0)
expect(color_g(p)).to_equal(0)
expect(color_b(p)).to_equal(0)
engine.shutdown()
```

</details>

#### draw_text_bg fills background color where the glyph bit is OFF

1. var engine = Engine2D create with backend
2. engine clear
3. engine draw text bg
4. engine present
5. engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# "A" row 0: 0b01110 — x=0 (col 0) is OFF, so that pixel should
# take the background color (green = rgb(0,255,0)), not the fg.
# At scale=1, font_size=7, the cell is 6px wide x 7px tall.
# draw_text_bg uses bilinear AA so the pure-bg pixel is at
# the leftmost column of the first row (x=0, y=0), which maps
# to font col 0 with coverage 0 → pure bg.
var engine = Engine2D.create_with_backend(50, 20, "cpu")
engine.clear(rgb(0, 0, 0))
engine.draw_text_bg(0, 0, "A", rgb(255, 255, 255), rgb(0, 255, 0), 7)
engine.present()
val pixels = engine.read_pixels()
# x=0, y=0 → font col 0 row 0 → coverage 0 (OFF) → pure bg green
val p = text_pixel_at(pixels, 0, 0, 50)
expect(color_g(p)).to_be_greater_than(0)
# Red component should be much less than green (bg is green, fg is white)
expect(color_r(p)).to_be_less_than(color_g(p))
engine.shutdown()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/engine2d_text_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Engine2D Text Rendering

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
