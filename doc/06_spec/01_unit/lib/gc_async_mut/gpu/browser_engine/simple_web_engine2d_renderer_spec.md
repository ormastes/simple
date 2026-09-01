# Simple Web Engine2d Renderer Specification

> Tests covering SimpleWebEngine2DRenderer.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Web Engine2d Renderer Specification

## Scenarios

### SimpleWebEngine2DRenderer

#### returns solid background pixels without visual elements

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns solid background pixels without visual elements
   - Expected: pixels.len() equals `12 * 10`
   - Expected: pixels[0] equals `0xFF123456u32`
   - Expected: pixels[119] equals `0xFF123456u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns solid background pixels without visual elements")
val html = "<html><body style='background-color: #123456'></body></html>"
val pixels = simple_web_engine2d_render_html_pixels(html, 12, 10, "software")
expect(pixels.len()).to_equal(12 * 10)
expect(pixels[0]).to_equal(0xFF123456u32)
expect(pixels[119]).to_equal(0xFF123456u32)
```

</details>

#### keeps Simple Web marker off the solid-fill shortcut

- keeps Simple Web marker off the solid-fill shortcut
   - Expected: pixels.len() equals `12 * 10`
   - Expected: pixels[6 + 6 * 12] equals `0xFFFFFFFFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps Simple Web marker off the solid-fill shortcut")
val html = "<html><body style='background-color: #123456'>Simple Web</body></html>"
val pixels = simple_web_engine2d_render_html_pixels(html, 12, 10, "software")
expect(pixels.len()).to_equal(12 * 10)
expect(pixels[6 + 6 * 12]).to_equal(0xFFFFFFFFu32)
```

</details>

#### preserves generic layout dispatch through resolved backend while keeping pixels stable

- preserves generic layout dispatch through resolved backend while keeping pixels stable
   - Expected: sw.len() equals `40 * 24`
   - Expected: resolved.len() equals `40 * 24`
   - Expected: resolved equals `sw`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("preserves generic layout dispatch through resolved backend while keeping pixels stable")
val html = "<html><head><style>.card{background-color:#ef4444;width:20px;height:12px}</style></head><body><div class='card'></div></body></html>"
val sw = simple_web_engine2d_render_html_pixels(html, 40, 24, "software")
val resolved_backend = simple_web_engine2d_resolved_backend_name(40, 24, "opencl")
val resolved = simple_web_engine2d_render_html_pixels(html, 40, 24, resolved_backend)
expect(sw.len()).to_equal(40 * 24)
expect(resolved.len()).to_equal(40 * 24)
expect(_count_color(resolved, 0xFFEF4444u32)).to_be_greater_than(0)
expect(resolved).to_equal(sw)
```

</details>

#### resolves auto before rendering pixels so output matches the resolved backend

- resolves auto before rendering pixels so output matches the resolved backend
   - Expected: px_auto equals `px_resolved`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("resolves auto before rendering pixels so output matches the resolved backend")
val html = "<html><body><main>Simple Web</main></body></html>"
val resolved = simple_web_engine2d_resolved_backend_name(48, 32, "auto")
val px_auto = simple_web_engine2d_render_html_pixels(html, 48, 32, "auto")
val px_resolved = simple_web_engine2d_render_html_pixels(html, 48, 32, resolved)
expect(px_auto).to_equal(px_resolved)
```

</details>

#### resolves auto for readback paths that bypass layout readback heuristics

- resolves auto for readback paths that bypass layout readback heuristics
   - Expected: rb_auto.pixels equals `rb_resolved.pixels`
   - Expected: rb_auto.pixels.len() equals `48 * 32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("resolves auto for readback paths that bypass layout readback heuristics")
val html = "<html><body><div style='display:contents;width:10px;height:10px;background-color:#ffcc00'></div><main>Simple Web</main></body></html>"
val resolved = simple_web_engine2d_resolved_backend_name(48, 32, "auto")
val rb_auto = simple_web_engine2d_render_html_readback(html, 48, 32, "auto")
val rb_resolved = simple_web_engine2d_render_html_readback(html, 48, 32, resolved)
expect(rb_auto.pixels).to_equal(rb_resolved.pixels)
expect(rb_auto.pixels.len()).to_equal(48 * 32)
```

</details>

#### debug attr lookup preserves parsed attributes across node scans

- debug attr lookup preserves parsed attributes across node scans
   - Expected: simple_web_layout_debug_attr_by_id(html, "target", "class") equals `card primary`
   - Expected: simple_web_layout_debug_attr_by_id(html, "target", "data-route") equals `/app/home`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("debug attr lookup preserves parsed attributes across node scans")
val html = "<html><body><section id='outer'><div id='target' class='card primary' data-route='/app/home'></div></section></body></html>"
expect(simple_web_layout_debug_attr_by_id(html, "target", "class")).to_equal("card primary")
expect(simple_web_layout_debug_attr_by_id(html, "target", "data-route")).to_equal("/app/home")
```

</details>

#### reuses retained pixels for unchanged static html

- reuses retained pixels for unchanged static html
   - Expected: first.len() equals `12 * 10`
   - Expected: second[0] equals `0xFF123456u32`
   - Expected: cache.stores equals `1`
   - Expected: cache.hits equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reuses retained pixels for unchanged static html")
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

- renders the simple-web-engine2d-toolbar-modal-grid exact fixture marker
   - Expected: plain_pixels[toolbar_pixel] equals `0xFF0E1116u32`
   - Expected: marked_pixels[toolbar_pixel] equals `0xFF22C55Eu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders the simple-web-engine2d-toolbar-modal-grid exact fixture marker")
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

- ignores the simple-web-engine2d-dashboard-command-list marker class (no scene-name special-casing)
   - Expected: simple_web_engine2d_render_html_pixels(marked, 96, 64, "software") equals `simple_web_engine2d_render_html_pixels(plain, 96, 64, "software")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("ignores the simple-web-engine2d-dashboard-command-list marker class (no scene-name special-casing)")
val plain = "<html><body style='margin:0; background-color: #0b1220'><main>dashboard command list</main></body></html>"
val marked = "<html><body class='simple-web-engine2d-dashboard-command-list' style='margin:0; background-color: #0b1220'><main>dashboard command list</main></body></html>"
expect(simple_web_engine2d_render_html_pixels(marked, 96, 64, "software")).to_equal(simple_web_engine2d_render_html_pixels(plain, 96, 64, "software"))
```

</details>

#### ignores the simple-web-engine2d-form-sidebar-validation marker class (no scene-name special-casing)

- ignores the simple-web-engine2d-form-sidebar-validation marker class (no scene-name special-casing)
   - Expected: simple_web_engine2d_render_html_pixels(marked, 96, 64, "software") equals `simple_web_engine2d_render_html_pixels(plain, 96, 64, "software")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("ignores the simple-web-engine2d-form-sidebar-validation marker class (no scene-name special-casing)")
val plain = "<html><body style='margin:0; background-color: #0a0f1a'><main>form sidebar validation</main></body></html>"
val marked = "<html><body class='simple-web-engine2d-form-sidebar-validation' style='margin:0; background-color: #0a0f1a'><main>form sidebar validation</main></body></html>"
expect(simple_web_engine2d_render_html_pixels(marked, 96, 64, "software")).to_equal(simple_web_engine2d_render_html_pixels(plain, 96, 64, "software"))
```

</details>

#### ignores the simple-web-engine2d-settings-inspector-tree marker class (no scene-name special-casing)

- ignores the simple-web-engine2d-settings-inspector-tree marker class (no scene-name special-casing)
   - Expected: simple_web_engine2d_render_html_pixels(marked, 96, 64, "software") equals `simple_web_engine2d_render_html_pixels(plain, 96, 64, "software")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("ignores the simple-web-engine2d-settings-inspector-tree marker class (no scene-name special-casing)")
val plain = "<html><body style='margin:0; background-color: #0b1020'><main>settings inspector tree</main></body></html>"
val marked = "<html><body class='simple-web-engine2d-settings-inspector-tree' style='margin:0; background-color: #0b1020'><main>settings inspector tree</main></body></html>"
expect(simple_web_engine2d_render_html_pixels(marked, 96, 64, "software")).to_equal(simple_web_engine2d_render_html_pixels(plain, 96, 64, "software"))
```

</details>

#### ignores the simple-web-engine2d-media-gallery-command marker class (no scene-name special-casing)

- ignores the simple-web-engine2d-media-gallery-command marker class (no scene-name special-casing)
   - Expected: simple_web_engine2d_render_html_pixels(marked, 96, 64, "software") equals `simple_web_engine2d_render_html_pixels(plain, 96, 64, "software")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("ignores the simple-web-engine2d-media-gallery-command marker class (no scene-name special-casing)")
val plain = "<html><body style='margin:0; background-color: #0f172a'><main>media gallery command</main></body></html>"
val marked = "<html><body class='simple-web-engine2d-media-gallery-command' style='margin:0; background-color: #0f172a'><main>media gallery command</main></body></html>"
expect(simple_web_engine2d_render_html_pixels(marked, 96, 64, "software")).to_equal(simple_web_engine2d_render_html_pixels(plain, 96, 64, "software"))
```

</details>

#### ignores the simple-web-engine2d-report-table-command marker class (no scene-name special-casing)

- ignores the simple-web-engine2d-report-table-command marker class (no scene-name special-casing)
   - Expected: simple_web_engine2d_render_html_pixels(marked, 96, 64, "software") equals `simple_web_engine2d_render_html_pixels(plain, 96, 64, "software")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("ignores the simple-web-engine2d-report-table-command marker class (no scene-name special-casing)")
val plain = "<html><body style='margin:0; background-color: #f8fafc'><main>report table command</main></body></html>"
val marked = "<html><body class='simple-web-engine2d-report-table-command' style='margin:0; background-color: #f8fafc'><main>report table command</main></body></html>"
expect(simple_web_engine2d_render_html_pixels(marked, 96, 64, "software")).to_equal(simple_web_engine2d_render_html_pixels(plain, 96, 64, "software"))
```

</details>

#### ignores the simple-web-engine2d-split-pane-status-list marker class (no scene-name special-casing)

- ignores the simple-web-engine2d-split-pane-status-list marker class (no scene-name special-casing)
   - Expected: simple_web_engine2d_render_html_pixels(marked, 96, 64, "software") equals `simple_web_engine2d_render_html_pixels(plain, 96, 64, "software")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("ignores the simple-web-engine2d-split-pane-status-list marker class (no scene-name special-casing)")
val plain = "<html><body><main>split pane status list</main></body></html>"
val marked = "<html><body class='simple-web-engine2d-split-pane-status-list'><main>split pane status list</main></body></html>"
expect(simple_web_engine2d_render_html_pixels(marked, 96, 64, "software")).to_equal(simple_web_engine2d_render_html_pixels(plain, 96, 64, "software"))
```

</details>

#### renders a class-selector CSS box through the real layout engine at the right location and color

- renders a class-selector CSS box through the real layout engine at the right location and color
   - Expected: pixels.len() equals `40 * 24`
   - Expected: pixels[0] equals `0xFF22C55Eu32`
   - Expected: pixels[39 + 23 * 40] equals `0xFFFFFFFFu32`
   - Expected: _count_color(pixels, 0xFF22C55Eu32) equals `20 * 12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders a class-selector CSS box through the real layout engine at the right location and color")
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

- produces a deterministic checksum for the same HTML across repeated real-renderer calls
   - Expected: first equals `second`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("produces a deterministic checksum for the same HTML across repeated real-renderer calls")
val html = "<html><head><style>.card{background-color:#ef4444;width:20px;height:12px}</style></head><body><div class='card'></div></body></html>"
val first = simple_web_engine2d_render_html_pixels(html, 32, 20, "software")
val second = simple_web_engine2d_render_html_pixels(html, 32, 20, "software")
expect(first).to_equal(second)
expect(_count_color(first, 0xFFEF4444u32)).to_be_greater_than(0)
```

</details>

#### extracts the document background from a body rule in a style block

- extracts the document background from a body rule in a style block
   - Expected: simple_web_html_background_color(html) equals `0xFF1A1A2Eu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("extracts the document background from a body rule in a style block")
# Regression (2026-08-02): the extractor only read inline body style=
# and leaked the first block's class-rule color (or white) for the
# standard `<style>body { background-color: ... }</style>` shape.
val html = "<html><head><style>" +
    "body { background-color: #1a1a2e; color: #e0e0ff; }" +
    ".card { background-color: #0f3460; padding: 8px; }" +
    "</style></head><body><div class='card'>x</div></body></html>"
expect(simple_web_html_background_color(html)).to_equal(0xFF1A1A2Eu32)
```

</details>

#### extracts the compact fallback-page body background shorthand

- extracts the compact fallback-page body background shorthand
   - Expected: simple_web_html_background_color(html) equals `0xFF202833u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("extracts the compact fallback-page body background shorthand")
# build/tmp missing-file fallback-page shape: body{background:#hex}
val html = "<html><head><style>body{background:#202833;color:#e6e6e6}" +
    ".err{background:#3b1d1d;padding:4px}</style></head>" +
    "<body><div class='err'>file missing</div></body></html>"
expect(simple_web_html_background_color(html)).to_equal(0xFF202833u32)
```

</details>

#### extracts a body rule background when no block rules exist

- extracts a body rule background when no block rules exist
   - Expected: simple_web_html_background_color(html) equals `0xFF204060u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("extracts a body rule background when no block rules exist")
val html = "<html><head><style>body { background-color: #204060; }</style></head>" +
    "<body><div>plain</div></body></html>"
expect(simple_web_html_background_color(html)).to_equal(0xFF204060u32)
```

</details>

#### resolves a grouped html, body selector background

- resolves a grouped html, body selector background
   - Expected: simple_web_html_background_color(html) equals `0xFF0B1220u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("resolves a grouped html, body selector background")
val html = "<html><head><style>html, body { margin: 0; background-color: #0b1220; }</style></head>" +
    "<body><div>x</div></body></html>"
expect(simple_web_html_background_color(html)).to_equal(0xFF0B1220u32)
```

</details>

#### does not mistake a tbody rule for the document background

- does not mistake a tbody rule for the document background
   - Expected: simple_web_html_background_color(html) equals `0xFFFFFFFFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("does not mistake a tbody rule for the document background")
val html = "<html><head><style>tbody { background-color: #ff0000; }</style></head>" +
    "<body><table><tbody><tr><td>x</td></tr></tbody></table></body></html>"
expect(simple_web_html_background_color(html)).to_equal(0xFFFFFFFFu32)
```

</details>

#### keeps inline body style precedence over a style-block body rule

- keeps inline body style precedence over a style-block body rule
   - Expected: simple_web_html_background_color(html) equals `0xFF123456u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps inline body style precedence over a style-block body rule")
val html = "<html><head><style>body { background-color: #111111; }</style></head>" +
    "<body style='background-color: #123456'></body></html>"
expect(simple_web_html_background_color(html)).to_equal(0xFF123456u32)
```

</details>

#### matches direct child :has selector for first block

- matches direct child :has selector for first block
   - Expected: _render_selector_color(style, "<div><span class='badge'></span></div>", 0xFF0E7490u32) is true
   - Expected: _render_selector_color(style, "<div><section><span class='badge'></span></section></div>", 0xFF0E7490u32) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches direct child :has selector for first block")
val style = "div:has(> .badge) { width: 12px; height: 8px; background-color: #0e7490; }"
expect(_render_selector_color(style, "<div><span class='badge'></span></div>", 0xFF0E7490u32)).to_equal(true)
expect(_render_selector_color(style, "<div><section><span class='badge'></span></section></div>", 0xFF0E7490u32)).to_equal(false)
```

</details>

#### paints class-selector boxes on the readback path instead of a budget-truncated near-empty frame

- paints class-selector boxes on the readback path instead of a budget-truncated near-empty frame
   - Expected: result.readback.pixels.len() equals `64 * 48`
   - Expected: _count_color(vk_pixels, 0xFF2563EBu32) equals `_count_color(pixels, 0xFF2563EBu32)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("paints class-selector boxes on the readback path instead of a budget-truncated near-empty frame")
# Regression (2026-08-02): under the interpreter a wall-clock budget
# break mid-cascade left class-styled nodes on default styles, so the
# engine2d readback entry published a frame where element selectors
# (body/h1) painted but class-selector boxes dropped to 0 pixels —
# while the pure_simple path (budget-floor armed) painted them all.
# The layout now retries ONCE with a bounded floor on a degraded
# cascade (simple_web_layout_engine2d_fast) and propagates
# render_degraded honestly if even the retry trips.
val html = "<html><head><style>" +
    "body{margin:0;background-color:#1a1a2e} " +
    ".box{width:28px;height:18px;background-color:#2563eb}" +
    "</style></head><body><div class='box'></div></body></html>"
val result = simple_web_render_html_to_readback_result_with_engine2d_backend(
    html, 64, 48, "software")
assert_false result.render_degraded
expect(result.readback.pixels.len()).to_equal(64 * 48)
expect(_count_color(result.readback.pixels, 0xFF2563EBu32)).to_be_greater_than(0)
expect(_count_color(result.readback.pixels, 0xFF1A1A2Eu32)).to_be_greater_than(0)
# Same document through the pixels entry must agree (parity with the
# route the showcase spec proves green).
val pixels = simple_web_engine2d_render_html_pixels(html, 64, 48, "software")
expect(_count_color(pixels, 0xFF2563EBu32)).to_be_greater_than(0)
# Explicit-GPU-backend branch parity (coordinator capture evidence
# 2026-08-02): an explicit "vulkan" backend name must not reroute the
# document away from the real cascade — same styled box pixels as
# "software" (provenance may differ; pixels must not).
val vk_pixels = simple_web_engine2d_render_html_pixels(html, 64, 48, "vulkan")
expect(_count_color(vk_pixels, 0xFF2563EBu32)).to_equal(_count_color(pixels, 0xFF2563EBu32))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleWebEngine2DRenderer.
- SimpleWebEngine2DRenderer

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ba6d79a5db8bf2d5903cab64e514c714c00cbb0d58e52eaabe9ca9de339a7fe0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ba6d79a5db8bf2d5903cab64e514c714c00cbb0d58e52eaabe9ca9de339a7fe0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ba6d79a5db8bf2d5903cab64e514c714c00cbb0d58e52eaabe9ca9de339a7fe0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns solid background pixels without visual elements' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps Simple Web marker off the solid-fill shortcut' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves generic layout dispatch through resolved backend while keeping pixels stable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
