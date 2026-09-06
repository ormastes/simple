# Text Metrics Specification

> <details>

<!-- sdn-diagram:id=text_metrics_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=text_metrics_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

text_metrics_spec -> std
text_metrics_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=text_metrics_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Text Metrics Specification

## Scenarios

### browser text metrics

#### cached glyphs carry neutral bearing defaults

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val glyph = CachedGlyph.empty(65, 16)
expect(glyph.bearing_x).to_equal(0)
expect(glyph.bearing_y).to_equal(0)
```

</details>

#### prefers Chrome-compatible serif font before host and provided fallbacks

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val candidates = browser_serif_font_candidates()
expect(candidates.len()).to_be_greater_than(2)
expect(candidates[0]).to_equal("/usr/share/fonts/truetype/liberation/LiberationSerif-Regular.ttf")
expect(candidates[1]).to_equal("examples/09_embedded/simple_os/fonts/serif/NotoSerif-Regular.ttf")
expect(candidates[2]).to_equal("examples/09_embedded/simple_os/fonts/serif/NotoSerifSC-Regular.otf")
```

</details>

#### uses the Chrome-compatible text pixel path only for normal system font fixtures

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val renderer = BrowserRenderer.create(160, 120)
val normal_html = "<div style=\"width: 120px; height: 40px; background-color: #e0f2fe; font-family: system\">Google search deterministic compatibility fixture</div>"
val mono_html = "<div style=\"width: 120px; height: 40px; background-color: #e0f2fe; font-family: monospace\">Google search deterministic compatibility fixture</div>"

val normal_result = renderer.render_html_to_pixels(normal_html)
val mono_result = renderer.render_html_to_pixels(mono_html)

expect(normal_result.warnings).to_contain("html_fast_famous_site_corpus_pixel_path")
expect(mono_result.warnings).to_contain("html_fast_fill_pixel_path")
```

</details>

#### browser text drawing can render with Simple Vector Outline enabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bg = 0xFFFFFFFFu32
val fg = 0xFF000000u32
val pixels = browser_render_vector_font_probe_pixels("A", 40, 32)

expect(_count_painted_pixels(pixels, bg)).to_be_greater_than(0)
expect(_count_antialiased_argb_pixels(pixels, bg, fg)).to_be_greater_than(0)
```

</details>

#### SFFI TTF renderer exposes horizontal line metrics

1. var renderer =  chrome test font renderer
   - Expected: renderer.horizontal_line_metric(0, 0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var renderer = _chrome_test_font_renderer()

expect(renderer.horizontal_line_metric(16, 0)).to_be_greater_than(0)
expect(renderer.horizontal_line_metric(16, 1)).to_be_less_than(0)
expect(renderer.horizontal_line_metric(16, 3)).to_be_greater_than(0)
expect(renderer.horizontal_line_metric(0, 0)).to_equal(0)
```

</details>

#### SFFI TTF renderer exposes wrapped glyph layout positions

1. var renderer =  chrome test font renderer
   - Expected: glyphs[0].codepoint equals `71`
   - Expected: glyphs[0].x equals `0`
   - Expected: glyphs[0].y equals `4`
   - Expected: glyphs[14].x equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var renderer = _chrome_test_font_renderer()

val glyphs = renderer.layout_text("Google search deterministic compatibility fixture", 16, 112)
expect(glyphs.len()).to_be_greater_than(40)
expect(glyphs[0].codepoint).to_equal(71)
expect(glyphs[0].x).to_equal(0)
expect(glyphs[0].y).to_equal(4)
expect(glyphs[14].x).to_equal(0)
expect(glyphs[14].y).to_be_greater_than(glyphs[0].y)
```

</details>

#### SFFI TTF glyph bearing_y exposes hinted bitmap bottom offset

1. var renderer =  chrome test font renderer
   - Expected: glyph.bearing_x equals `0`
   - Expected: glyph.bearing_y equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var renderer = _chrome_test_font_renderer()

val glyph = renderer.get_glyph(71, 16)
expect(glyph.width).to_be_greater_than(0)
expect(glyph.height).to_be_greater_than(0)
expect(glyph.bearing_x).to_equal(0)
expect(glyph.bearing_y).to_equal(0)
```

</details>

#### SFFI TTF renderer exposes RGB subpixel glyph coverage

1. var renderer =  chrome test font renderer
   - Expected: glyph != nil is true
   - Expected: glyph.pixels.len() equals `glyph.width * glyph.height * 3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var renderer = _chrome_test_font_renderer()

val glyph = renderer.rasterize_subpixel(71, 16)
expect(glyph != nil).to_equal(true)
if glyph != nil:
    expect(glyph.width).to_be_greater_than(0)
    expect(glyph.height).to_be_greater_than(0)
    expect(glyph.pixels.len()).to_equal(glyph.width * glyph.height * 3)
```

</details>

#### documents the current corpus line-width mismatch against Chrome metrics

1. var renderer =  chrome test font renderer


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var renderer = _chrome_test_font_renderer()

expect(renderer.measure_text_width("Google search", 16)).to_be_less_than(121)
expect(renderer.measure_text_width("Google Translate", 16)).to_be_greater_than(100)
expect(renderer.measure_text_width("Google Translate", 16)).to_be_less_than(121)
expect(renderer.measure_text_width("Quora productivity", 16)).to_be_greater_than(100)
expect(renderer.measure_text_width("Quora productivity", 16)).to_be_less_than(121)
```

</details>

#### layout_text increases height when narrow width forces wrapping

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parent_style = be_default_style()
parent_style.font_size = 16
val node = BeDomNode.text("hello world")

val wide = layout_node(node, _container(200, 40), parent_style)
val narrow = layout_node(node, _container(24, 40), parent_style)

expect(layout_get_height(narrow) > layout_get_height(wide)).to_equal(true)
```

</details>

#### paint_layout_box uses line width for text decoration fallback

1. node set style
2. node set style
3. node set style
   - Expected: cmds.len() equals `2`
   - Expected: cmds[1].width equals `24`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = BeDomNode.text("iii")
node.set_style("font-size", "16px")
node.set_style("text-decoration", "underline")
node.set_style("color", "#FFFFFFFF")

val box = BeLayoutBox(
    x: 0, y: 0, width: 0, height: 16,
    content_x: 0, content_y: 0,
    content_width: 0, content_height: 16,
    node: node, children: []
)

val cmds = paint_layout_box(box, [])
expect(cmds.len()).to_equal(2)

expect(cmds[1].width).to_equal(24)
```

</details>

#### paint_layout_box emits multiple text commands for wrapped text

1. node set style
2. node set style
   - Expected: cmds.len() > 1 is true
   - Expected: cmds[0].kind equals `text`
   - Expected: cmds[1].kind equals `text`
   - Expected: cmds[1].y > cmds[0].y is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = BeDomNode.text("hello world")
node.set_style("font-size", "16px")
node.set_style("color", "#FFFFFFFF")

val box = BeLayoutBox(
    x: 0, y: 0, width: 24, height: 32,
    content_x: 0, content_y: 0,
    content_width: 24, content_height: 32,
    node: node, children: []
)

val cmds = paint_layout_box(box, [])
expect(cmds.len() > 1).to_equal(true)
expect(cmds[0].kind).to_equal("text")
expect(cmds[1].kind).to_equal("text")
expect(cmds[1].y > cmds[0].y).to_equal(true)
```

</details>

#### paint_layout_box emits text decoration per wrapped line

1. node set style
2. node set style
3. node set style
   - Expected: cmds.len() > 3 is true
   - Expected: cmds[0].kind equals `text`
   - Expected: cmds[1].kind equals `rect`
   - Expected: cmds[2].kind equals `text`
   - Expected: cmds[3].kind equals `rect`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = BeDomNode.text("hello world")
node.set_style("font-size", "16px")
node.set_style("text-decoration", "underline")
node.set_style("color", "#FFFFFFFF")

val box = BeLayoutBox(
    x: 0, y: 0, width: 24, height: 32,
    content_x: 0, content_y: 0,
    content_width: 24, content_height: 32,
    node: node, children: []
)

val cmds = paint_layout_box(box, [])
expect(cmds.len() > 3).to_equal(true)
expect(cmds[0].kind).to_equal("text")
expect(cmds[1].kind).to_equal("rect")
expect(cmds[2].kind).to_equal("text")
expect(cmds[3].kind).to_equal("rect")
```

</details>

#### paint_layout_box emits separate text commands for explicit newlines

1. node set style
2. node set style
   - Expected: cmds.len() equals `2`
   - Expected: cmds[0].kind equals `text`
   - Expected: cmds[0].text_val equals `alpha`
   - Expected: cmds[1].kind equals `text`
   - Expected: cmds[1].text_val equals `beta`
   - Expected: cmds[1].y > cmds[0].y is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = BeDomNode.text("alpha\nbeta")
node.set_style("font-size", "16px")
node.set_style("color", "#FFFFFFFF")

val box = BeLayoutBox(
    x: 0, y: 0, width: 160, height: 40,
    content_x: 0, content_y: 0,
    content_width: 160, content_height: 40,
    node: node, children: []
)

val cmds = paint_layout_box(box, [])
expect(cmds.len()).to_equal(2)
expect(cmds[0].kind).to_equal("text")
expect(cmds[0].text_val).to_equal("alpha")
expect(cmds[1].kind).to_equal("text")
expect(cmds[1].text_val).to_equal("beta")
expect(cmds[1].y > cmds[0].y).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui.chromium/text_metrics_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- browser text metrics

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
