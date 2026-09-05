# Browser Renderer Specification

> Tests covering BrowserRenderer HTML/CSS expect-draw evidence.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Renderer Specification

## Scenarios

### BrowserRenderer HTML/CSS expect-draw evidence

#### bounds the direct-render node arena at its exact limit

- Render a small document with exact and roomy node limits
   - Expected: simple_web_layout_debug_capped_node_count(html, 3) equals `3`
   - Expected: simple_web_layout_debug_capped_node_count(html, 100) equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render a small document with exact and roomy node limits")
val html = "<div>one</div><p>two</p>"
expect(simple_web_layout_debug_capped_node_count(html, 3)).to_equal(3)
expect(simple_web_layout_debug_capped_node_count(html, 100)).to_equal(7)
```

</details>

#### rejects oversized direct-render HTML before parser allocation

- Render the same document at and below its input byte envelope
- html, html len
- html, html len


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render the same document at and below its input byte envelope")
val html = "<div>one</div><p>two</p>"
expect(simple_web_layout_debug_capped_input_node_count(
    html, html.len()
)).to_equal(7)
expect(simple_web_layout_debug_capped_input_node_count(
    html, html.len() - 1
)).to_equal(1)
```

</details>

#### keeps exact-envelope tag storms out of hosted Draw IR parsing

- Render tag storms at and beyond the hosted HTML envelope
- oversized layout composition batches len


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render tag storms at and beyond the hosted HTML envelope")
val exact_storm = "<".repeat(1048576)
val oversized = "<".repeat(1048577)
val exact_layout = simple_web_layout_render_html_draw_ir_result(
    exact_storm, 4, 4
)
val oversized_layout = simple_web_layout_render_html_draw_ir_result(
    oversized, 4, 4
)
expect(exact_layout.composition.batches.len()).to_be_greater_than(0)
expect(
    oversized_layout.composition.batches.len()
).to_be_greater_than(0)
```

</details>

#### caps CSS rules across style blocks and preserves the valid prefix

- Render bounded CSS rules and malformed brace storms
- "x" repeat
- "x" repeat
   - Expected: open_pixels[0] equals `0xFF123456u32`
   - Expected: close_pixels[0] equals `0xFF123456u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render bounded CSS rules and malformed brace storms")
val html = "<style>.a{color:red}.b{color:green}</style><style>.c{color:blue}</style>"
val open_storm = "<style>body{background-color:#123456}" +
    "x".repeat(20000) + "{".repeat(13000) + "</style><body></body>"
val close_storm = "<style>body{background-color:#123456}" +
    "x".repeat(20000) + "}".repeat(13000) + "</style><body></body>"

expect(simple_web_layout_debug_capped_css_rule_count(
    html, 2
)).to_equal(2)
val open_pixels = simple_web_layout_render_html_software_pixels(
    open_storm, 4, 4
)
val close_pixels = simple_web_layout_render_html_software_pixels(
    close_storm, 4, 4
)
val open_layout = simple_web_layout_render_html_draw_ir_result(
    open_storm, 4, 4
)
val close_layout = simple_web_layout_render_html_draw_ir_result(
    close_storm, 4, 4
)
expect(open_pixels[0]).to_equal(0xFF123456u32)
expect(close_pixels[0]).to_equal(0xFF123456u32)
expect(open_layout.composition.batches.len()).to_be_greater_than(0)
expect(close_layout.composition.batches.len()).to_be_greater_than(0)
expect(open_layout.composition.batches[0].commands[0].color).to_equal(
    0xFF123456u32
)
expect(close_layout.composition.batches[0].commands[0].color).to_equal(
    0xFF123456u32
)
```

</details>

#### bounds CSS variable expansion and selector lists

- Render variable, selector-list, and combinator storms
- " unused{content:var
- " never," repeat
-


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render variable, selector-list, and combinator storms")
val amplified = "<style>:root{--x:" + "a".repeat(4096) +
    ";}body{background-color:#123456}" +
    ".unused{content:var(--x)}".repeat(300) +
    "</style><body></body>"
val selector_storm = "<style>body{background-color:#123456}" +
    ".never,".repeat(1000) +
    "body{background-color:#abcdef}</style><body></body>"
val combinator_storm = "<style>body{background-color:#123456}" +
    ("x>".repeat(300)) +
    "body{background-color:#abcdef}</style><body></body>"

expect(simple_web_layout_render_html_software_pixels(
    amplified, 4, 4
)[0]).to_equal(0xFF123456u32)
expect(simple_web_layout_render_html_software_pixels(
    selector_storm, 4, 4
)[0]).to_equal(0xFF123456u32)
expect(simple_web_layout_render_html_software_pixels(
    combinator_storm, 4, 4
)[0]).to_equal(0xFF123456u32)
```

</details>

#### admits exactly 256 declarations and rejects the next

- Render styles at and beyond the declaration limit
- "unused:value;" repeat
- "unused:value;" repeat


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render styles at and beyond the declaration limit")
val base = "<style>body{background-color:#123456}body{"
val exact = base + "background-color:#abcdef;" +
    "unused:value;".repeat(255) + "}</style><body></body>"
val over = base + "background-color:#abcdef;" +
    "unused:value;".repeat(256) + "}</style><body></body>"

expect(simple_web_layout_render_html_software_pixels(
    exact, 4, 4
)[0]).to_equal(0xFFABCDEFu32)
expect(simple_web_layout_render_html_software_pixels(
    over, 4, 4
)[0]).to_equal(0xFF123456u32)
```

</details>

#### captures source HTML and visible text before pixel evidence

- Render the page and inspect its HTML capture before pixels
- var renderer = BrowserRenderer create
   - Expected: result.ok is true
   - Expected: result.has_html_capture() is true
   - Expected: result.title equals `Expect Draw Web`
   - Expected: result.pixel_data.len() equals `WEB_W * WEB_H`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render the page and inspect its HTML capture before pixels")
val html = _expect_draw_web_html()
var renderer = BrowserRenderer.create(WEB_W, WEB_H)
val result = renderer.render_html(html)

expect(result.ok).to_equal(true)
expect(result.has_html_capture()).to_equal(true)
expect(result.title).to_equal("Expect Draw Web")
expect(result.source_html).to_contain("<main class=\"expect-draw\">")
expect(result.source_html).to_contain("Render Ready")
expect(result.source_html).to_contain("Visible HTML text before pixels.")
expect(result.pixel_data.len()).to_equal(WEB_W * WEB_H)
```

</details>

#### exposes CSS-backed scene evidence after HTML assertions

- Render the styled page and inspect its scene commands
- var renderer = BrowserRenderer create
   - Expected: scene.width equals `WEB_W`
   - Expected: scene.height equals `WEB_H`
   - Expected: scene.commands.len() equals `1`
   - Expected: scene.commands[0].kind equals `fill_rect`
   - Expected: scene.commands[0].color equals `0xFF123456u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render the styled page and inspect its scene commands")
val html = _expect_draw_web_html()
var renderer = BrowserRenderer.create(WEB_W, WEB_H)
val result = renderer.render_html_to_pixels(html)
val scene = result.to_scene()

expect(result.source_html).to_contain("background-color: #123456")
expect(result.source_html).to_contain("color: #f8fafc")
expect(scene.width).to_equal(WEB_W)
expect(scene.height).to_equal(WEB_H)
expect(scene.commands.len()).to_equal(1)
expect(scene.commands[0].kind).to_equal("fill_rect")
expect(scene.commands[0].color).to_equal(0xFF123456u32)
```

</details>

#### keeps the viewport helper on the same HTML capture contract

- Render through the viewport helper and inspect its HTML capture
   - Expected: result.has_html_capture() is true
   - Expected: result.pixel_data.len() equals `WEB_W * WEB_H`
   - Expected: result.byte_count() equals `(WEB_W * WEB_H * 4).to_i64()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render through the viewport helper and inspect its HTML capture")
val html = _expect_draw_web_html()
val result = render_html_to_pixels_with_viewport(html, WEB_W, WEB_H)

expect(result.has_html_capture()).to_equal(true)
expect(result.source_html).to_contain("expect-draw")
expect(result.pixel_data.len()).to_equal(WEB_W * WEB_H)
expect(result.byte_count()).to_equal((WEB_W * WEB_H * 4).to_i64())
```

</details>

#### keeps widget class paint flags active through the pure Simple renderer

- Render focused widget classes through the pure Simple renderer
   - Expected: pixels.len() equals `WEB_W * WEB_H`
   - Expected: pixels[0] equals `0xFF0066CCu32`
   - Expected: pixels[(WEB_H - 1) * WEB_W] equals `0xFF0066CCu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render focused widget classes through the pure Simple renderer")
val html = "<html><body><SECTION class=\"widget-panel focused\"><BUTTON class=\"widget-button\">Go</BUTTON  ><IMG class=\"widget-image icon-image\" /></SECTION  ></body></html>"
val pixels = simple_web_layout_render_html_software_pixels(html, WEB_W, WEB_H)

expect(pixels.len()).to_equal(WEB_W * WEB_H)
expect(pixels[0]).to_equal(0xFF0066CCu32)
expect(pixels[(WEB_H - 1) * WEB_W]).to_equal(0xFF0066CCu32)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/browser_engine/browser_renderer_spec.spl` |
| Updated | 2026-07-29 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering BrowserRenderer HTML/CSS expect-draw evidence.
- BrowserRenderer HTML/CSS expect-draw evidence

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
