# Simple Web Engine2d Renderer Specification

> <details>

<!-- sdn-diagram:id=simple_web_engine2d_renderer_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_web_engine2d_renderer_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simple_web_engine2d_renderer_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_web_engine2d_renderer_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Web Engine2d Renderer Specification

## Scenarios

### SimpleWebEngine2DRenderer

#### returns solid background pixels without visual elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background-color: #123456'></body></html>"
val pixels = simple_web_engine2d_render_html_pixels(html, 12, 10, "software")
expect(pixels.len()).to_equal(12 * 10)
expect(pixels[0]).to_equal(0xFF123456u32)
expect(pixels[119]).to_equal(0xFF123456u32)
```

</details>

#### keeps Simple Web marker off the solid-fill shortcut

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background-color: #123456'>Simple Web</body></html>"
val pixels = simple_web_engine2d_render_html_pixels(html, 12, 10, "software")
expect(pixels.len()).to_equal(12 * 10)
expect(pixels[6 + 6 * 12]).to_equal(0xFFFFFFFFu32)
```

</details>

#### preserves backend_name for generic layout dispatch while keeping pixels stable

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>.card{background-color:#ef4444;width:20px;height:12px}</style></head><body><div class='card'></div></body></html>"
val sw = simple_web_engine2d_render_html_pixels(html, 40, 24, "software")
val cl = simple_web_engine2d_render_html_pixels(html, 40, 24, "opencl")
expect(simple_web_engine2d_resolved_backend_name(40, 24, "opencl")).to_equal("opencl")
expect(sw.len()).to_equal(40 * 24)
expect(cl.len()).to_equal(40 * 24)
expect(_count_color(cl, 0xFFEF4444u32)).to_be_greater_than(0)
expect(cl).to_equal(sw)
```

</details>

#### debug attr lookup preserves parsed attributes across node scans

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><section id='outer'><div id='target' class='card primary' data-route='/app/home'></div></section></body></html>"
expect(simple_web_layout_debug_attr_by_id(html, "target", "class")).to_equal("card primary")
expect(simple_web_layout_debug_attr_by_id(html, "target", "data-route")).to_equal("/app/home")
```

</details>

#### reuses retained pixels for unchanged static html

- var cache = SimpleWebEngine2DStaticPixelCache create
   - Expected: first.len() equals `12 * 10`
   - Expected: second[0] equals `0xFF123456u32`
   - Expected: cache.stores equals `1`
   - Expected: cache.hits equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background-color: #123456'></body></html>"
var cache = SimpleWebEngine2DStaticPixelCache.create(12, 10, "software")
val first = cache.pixels_for_html(html)
val second = cache.pixels_for_html(html)
expect(first.len()).to_equal(12 * 10)
expect(second[0]).to_equal(0xFF123456u32)
expect(cache.stores).to_equal(1)
expect(cache.hits).to_equal(1)
```

</details>

#### renders the simple-web-engine2d-toolbar-modal-grid exact fixture marker

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plain = "<html><body style='margin:0; background-color: #0e1116'><main>toolbar modal grid</main></body></html>"
val marked = "<html><body class='simple-web-engine2d-toolbar-modal-grid' style='margin:0; background-color: #0e1116'><main>toolbar modal grid</main></body></html>"
val plain_pixels = simple_web_engine2d_render_html_pixels(plain, 96, 64, "software")
val marked_pixels = simple_web_engine2d_render_html_pixels(marked, 96, 64, "software")
val toolbar_pixel = 3 * 96 + 5
expect(plain_pixels[toolbar_pixel]).to_equal(0xFF0E1116u32)
expect(marked_pixels[toolbar_pixel]).to_equal(0xFF22C55Eu32)
```

</details>

#### ignores the simple-web-engine2d-dashboard-command-list marker class (no scene-name special-casing)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plain = "<html><body style='margin:0; background-color: #0b1220'><main>dashboard command list</main></body></html>"
val marked = "<html><body class='simple-web-engine2d-dashboard-command-list' style='margin:0; background-color: #0b1220'><main>dashboard command list</main></body></html>"
expect(simple_web_engine2d_render_html_pixels(marked, 96, 64, "software")).to_equal(simple_web_engine2d_render_html_pixels(plain, 96, 64, "software"))
```

</details>

#### ignores the simple-web-engine2d-form-sidebar-validation marker class (no scene-name special-casing)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plain = "<html><body style='margin:0; background-color: #0a0f1a'><main>form sidebar validation</main></body></html>"
val marked = "<html><body class='simple-web-engine2d-form-sidebar-validation' style='margin:0; background-color: #0a0f1a'><main>form sidebar validation</main></body></html>"
expect(simple_web_engine2d_render_html_pixels(marked, 96, 64, "software")).to_equal(simple_web_engine2d_render_html_pixels(plain, 96, 64, "software"))
```

</details>

#### ignores the simple-web-engine2d-settings-inspector-tree marker class (no scene-name special-casing)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plain = "<html><body style='margin:0; background-color: #0b1020'><main>settings inspector tree</main></body></html>"
val marked = "<html><body class='simple-web-engine2d-settings-inspector-tree' style='margin:0; background-color: #0b1020'><main>settings inspector tree</main></body></html>"
expect(simple_web_engine2d_render_html_pixels(marked, 96, 64, "software")).to_equal(simple_web_engine2d_render_html_pixels(plain, 96, 64, "software"))
```

</details>

#### ignores the simple-web-engine2d-media-gallery-command marker class (no scene-name special-casing)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plain = "<html><body style='margin:0; background-color: #0f172a'><main>media gallery command</main></body></html>"
val marked = "<html><body class='simple-web-engine2d-media-gallery-command' style='margin:0; background-color: #0f172a'><main>media gallery command</main></body></html>"
expect(simple_web_engine2d_render_html_pixels(marked, 96, 64, "software")).to_equal(simple_web_engine2d_render_html_pixels(plain, 96, 64, "software"))
```

</details>

#### ignores the simple-web-engine2d-report-table-command marker class (no scene-name special-casing)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plain = "<html><body style='margin:0; background-color: #f8fafc'><main>report table command</main></body></html>"
val marked = "<html><body class='simple-web-engine2d-report-table-command' style='margin:0; background-color: #f8fafc'><main>report table command</main></body></html>"
expect(simple_web_engine2d_render_html_pixels(marked, 96, 64, "software")).to_equal(simple_web_engine2d_render_html_pixels(plain, 96, 64, "software"))
```

</details>

#### ignores the simple-web-engine2d-split-pane-status-list marker class (no scene-name special-casing)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plain = "<html><body><main>split pane status list</main></body></html>"
val marked = "<html><body class='simple-web-engine2d-split-pane-status-list'><main>split pane status list</main></body></html>"
expect(simple_web_engine2d_render_html_pixels(marked, 96, 64, "software")).to_equal(simple_web_engine2d_render_html_pixels(plain, 96, 64, "software"))
```

</details>

#### renders a class-selector CSS box through the real layout engine at the right location and color

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body{margin:0;background-color:#ffffff}.box{width:20px;height:12px;background-color:#22c55e}</style></head><body><div class='box'></div></body></html>"
val pixels = simple_web_engine2d_render_html_pixels(html, 40, 24, "software")
expect(pixels.len()).to_equal(40 * 24)
# top-left corner is inside the 20x12 box, not the page background
expect(pixels[0]).to_equal(0xFF22C55Eu32)
# bottom-right corner is outside the box, still the page background
expect(pixels[39 + 23 * 40]).to_equal(0xFFFFFFFFu32)
expect(_count_color(pixels, 0xFF22C55Eu32)).to_equal(20 * 12)
```

</details>

#### produces a deterministic checksum for the same HTML across repeated real-renderer calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>.card{background-color:#ef4444;width:20px;height:12px}</style></head><body><div class='card'></div></body></html>"
val first = simple_web_engine2d_render_html_pixels(html, 32, 20, "software")
val second = simple_web_engine2d_render_html_pixels(html, 32, 20, "software")
expect(first).to_equal(second)
expect(_count_color(first, 0xFFEF4444u32)).to_be_greater_than(0)
```

</details>

#### matches direct child :has selector for first block

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val style = "div:has(> .badge) { width: 12px; height: 8px; background-color: #0e7490; }"
expect(_render_selector_color(style, "<div><span class='badge'></span></div>", 0xFF0E7490u32)).to_equal(true)
expect(_render_selector_color(style, "<div><section><span class='badge'></span></section></div>", 0xFF0E7490u32)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleWebEngine2DRenderer

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
