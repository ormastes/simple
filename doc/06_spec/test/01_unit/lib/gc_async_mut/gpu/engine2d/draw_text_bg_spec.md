# Draw Text Bg Specification

> <details>

<!-- sdn-diagram:id=draw_text_bg_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=draw_text_bg_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

draw_text_bg_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=draw_text_bg_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Draw Text Bg Specification

## Scenarios

### Engine2DExtended.draw_text_bg (CPU backend)

#### glyph cell vs outside

#### paints the text cell and preserves clear outside

- var engine = Engine2D create with backend
- engine clear
- engine draw text bg
- engine present
   - Expected: pixels[outside_idx] equals `GREEN`
   - Expected: _has_not_color_in_region(pixels, 32, 0, 0, 16, 16, GREEN) is true
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val GREEN: u32 = 0xFF00FF00
val BLACK: u32 = 0xFF000000
val WHITE: u32 = 0xFFFFFFFF

var engine = Engine2D.create_with_backend(32, 16, "cpu")
engine.clear(GREEN)

# Paint a single 'A' glyph at the origin with 16pt font. Pixels
# outside the text cell must stay GREEN.
engine.draw_text_bg(0, 0, "A", WHITE, BLACK, 16)
engine.present()

val pixels = engine.read_pixels()

# Cell-outside pixel (far right of the 32-wide scene) must
# remain GREEN — draw_text_bg must not scribble on the whole
# framebuffer.
val outside_idx = 8 * 32 + 30
expect(pixels[outside_idx]).to_equal(GREEN)

expect(_has_not_color_in_region(pixels, 32, 0, 0, 16, 16, GREEN)).to_equal(true)

engine.shutdown()
```

</details>

#### renders both background and foreground pixels in the text cell

- var engine = Engine2D create with backend
- engine clear
- engine draw text bg
- engine present
   - Expected: _has_color_in_region(pixels, 32, 0, 0, 16, 16, GREEN) is true
   - Expected: _has_not_color_in_region(pixels, 32, 0, 0, 16, 16, GREEN) is true
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val BLACK: u32 = 0xFF000000
val GREEN: u32 = 0xFF00FF00
val WHITE: u32 = 0xFFFFFFFF

var engine = Engine2D.create_with_backend(32, 16, "cpu")
engine.clear(BLACK)
engine.draw_text_bg(0, 0, "A", WHITE, GREEN, 16)
engine.present()

val pixels = engine.read_pixels()
expect(_has_color_in_region(pixels, 32, 0, 0, 16, 16, GREEN)).to_equal(true)
expect(_has_not_color_in_region(pixels, 32, 0, 0, 16, 16, GREEN)).to_equal(true)

engine.shutdown()
```

</details>

#### returns without panic on an empty string

- var engine = Engine2D create with backend
- engine clear
- engine draw text bg
- engine present
   - Expected: pixels[0] equals `GREEN`
- engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val GREEN: u32 = 0xFF00FF00
var engine = Engine2D.create_with_backend(16, 16, "cpu")
engine.clear(GREEN)
engine.draw_text_bg(2, 2, "", 0xFFFFFFFF, 0xFF000000, 16)
engine.present()
val pixels = engine.read_pixels()
# Empty string must touch no pixels — whole scene still GREEN.
expect(pixels[0]).to_equal(GREEN)
engine.shutdown()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_text_bg_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Engine2DExtended.draw_text_bg (CPU backend)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
