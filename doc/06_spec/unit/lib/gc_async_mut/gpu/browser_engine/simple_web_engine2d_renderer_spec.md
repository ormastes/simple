# Simple Web Engine2d Renderer Specification

## Scenarios

### SimpleWebEngine2DRenderer

#### returns solid background pixels without visual elements

<details>
<summary>Executable SPipe</summary>

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
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background-color: #123456'>Simple Web</body></html>"
val pixels = simple_web_engine2d_render_html_pixels(html, 12, 10, "software")
expect(pixels.len()).to_equal(12 * 10)
expect(pixels[6 + 6 * 12]).to_equal(0xFFFFFFFFu32)
```

</details>

#### reuses retained pixels for unchanged static html

1. var cache = SimpleWebEngine2DStaticPixelCache create
   - Expected: first.len() equals `12 * 10`
   - Expected: second[0] equals `0xFF123456u32`
   - Expected: cache.stores equals `1`
   - Expected: cache.hits equals `1`


<details>
<summary>Executable SPipe</summary>

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

#### renders toolbar modal grid fixture with exact taskbar and image colors

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body class='simple-web-engine2d-toolbar-modal-grid' style='margin:0; background-color: #0e1116'><main>toolbar modal grid</main></body></html>"
val pixels = simple_web_engine2d_render_html_pixels(html, 96, 64, "software")
expect(pixels.len()).to_equal(96 * 64)
expect(pixels[0]).to_equal(0xFF243447u32)
expect(pixels[4 + 2 * 96]).to_equal(0xFF22C55Eu32)
expect(pixels[20 + 18 * 96]).to_equal(0xFFEF4444u32)
expect(pixels[54 + 26 * 96]).to_equal(0xFFCBD5E1u32)
expect(pixels[6 + 58 * 96]).to_equal(0xFF8B5CF6u32)
```

</details>

#### renders dashboard command list fixture with exact chart and list colors

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body class='simple-web-engine2d-dashboard-command-list' style='margin:0; background-color: #0b1220'><main>dashboard command list</main></body></html>"
val pixels = simple_web_engine2d_render_html_pixels(html, 96, 64, "software")
expect(pixels.len()).to_equal(96 * 64)
expect(pixels[0]).to_equal(0xFF111827u32)
expect(pixels[4 + 2 * 96]).to_equal(0xFF22C55Eu32)
expect(pixels[24 + 18 * 96]).to_equal(0xFF22C55Eu32)
expect(pixels[58 + 18 * 96]).to_equal(0xFFCBD5E1u32)
expect(pixels[68 + 58 * 96]).to_equal(0xFF10B981u32)
```

</details>

#### renders form sidebar validation fixture with exact navigation and validation colors

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body class='simple-web-engine2d-form-sidebar-validation' style='margin:0; background-color: #0a0f1a'><main>form sidebar validation</main></body></html>"
val pixels = simple_web_engine2d_render_html_pixels(html, 96, 64, "software")
expect(pixels.len()).to_equal(96 * 64)
expect(pixels[0]).to_equal(0xFF111827u32)
expect(pixels[4 + 6 * 96]).to_equal(0xFF2563EBu32)
expect(pixels[26 + 30 * 96]).to_equal(0xFFEF4444u32)
expect(pixels[26 + 42 * 96]).to_equal(0xFF22C55Eu32)
expect(pixels[74 + 18 * 96]).to_equal(0xFFF59E0Bu32)
expect(pixels[54 + 58 * 96]).to_equal(0xFF8B5CF6u32)
```

</details>

#### renders settings inspector tree fixture with exact tree and inspector colors

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body class='simple-web-engine2d-settings-inspector-tree' style='margin:0; background-color: #0b1020'><main>settings inspector tree</main></body></html>"
val pixels = simple_web_engine2d_render_html_pixels(html, 96, 64, "software")
expect(pixels.len()).to_equal(96 * 64)
expect(pixels[0]).to_equal(0xFF111827u32)
expect(pixels[4 + 2 * 96]).to_equal(0xFF38BDF8u32)
expect(pixels[4 + 15 * 96]).to_equal(0xFFE2E8F0u32)
expect(pixels[30 + 28 * 96]).to_equal(0xFFBFDBFEu32)
expect(pixels[68 + 18 * 96]).to_equal(0xFFF59E0Bu32)
expect(pixels[76 + 58 * 96]).to_equal(0xFFEF4444u32)
```

</details>

#### renders media gallery command fixture with exact image grid and taskbar colors

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body class='simple-web-engine2d-media-gallery-command' style='margin:0; background-color: #0f172a'><main>media gallery command</main></body></html>"
val pixels = simple_web_engine2d_render_html_pixels(html, 96, 64, "software")
expect(pixels.len()).to_equal(96 * 64)
expect(pixels[0]).to_equal(0xFF1F2937u32)
expect(pixels[4 + 2 * 96]).to_equal(0xFF14B8A6u32)
expect(pixels[7 + 17 * 96]).to_equal(0xFF38BDF8u32)
expect(pixels[37 + 17 * 96]).to_equal(0xFFFACC15u32)
expect(pixels[67 + 17 * 96]).to_equal(0xFF22C55Eu32)
expect(pixels[54 + 40 * 96]).to_equal(0xFFA78BFAu32)
expect(pixels[70 + 58 * 96]).to_equal(0xFFEF4444u32)
```

</details>

#### matches direct child :has selector for first block

<details>
<summary>Executable SPipe</summary>

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
| Source | `test/unit/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleWebEngine2DRenderer

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

