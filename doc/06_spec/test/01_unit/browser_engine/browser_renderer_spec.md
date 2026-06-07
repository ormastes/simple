# Browser Renderer Specification

> 1. var renderer = BrowserRenderer create

<!-- sdn-diagram:id=browser_renderer_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_renderer_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_renderer_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_renderer_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Renderer Specification

## Scenarios

### BrowserRenderer HTML/CSS expect-draw evidence

#### captures source HTML and visible text before pixel evidence

1. var renderer = BrowserRenderer create
   - Expected: result.ok is true
   - Expected: result.has_html_capture() is true
   - Expected: result.title equals `Expect Draw Web`
   - Expected: result.pixel_data.len() equals `WEB_W * WEB_H`


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var renderer = BrowserRenderer create
   - Expected: scene.width equals `WEB_W`
   - Expected: scene.height equals `WEB_H`
   - Expected: scene.commands.len() equals `1`
   - Expected: scene.commands[0].kind equals `fill_rect`
   - Expected: scene.commands[0].color equals `0xFF123456u32`


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = _expect_draw_web_html()
val result = render_html_to_pixels_with_viewport(html, WEB_W, WEB_H)

expect(result.has_html_capture()).to_equal(true)
expect(result.source_html).to_contain("expect-draw")
expect(result.pixel_data.len()).to_equal(WEB_W * WEB_H)
expect(result.byte_count()).to_equal((WEB_W * WEB_H * 4).to_i64())
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/browser_engine/browser_renderer_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BrowserRenderer HTML/CSS expect-draw evidence

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
