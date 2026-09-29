# Simple Web Window Renderer Specification

> <details>

<!-- sdn-diagram:id=simple_web_window_renderer_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_web_window_renderer_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simple_web_window_renderer_spec -> std
simple_web_window_renderer_spec -> common
simple_web_window_renderer_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_web_window_renderer_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Web Window Renderer Specification

## Scenarios

### Simple Web compositor adapter

#### provides app HTML for the SimpleOS browser window

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = simple_web_app_html("Simple Browser", "")
expect(html.contains("about:network")).to_equal(true)
expect(html.contains("Simple Web")).to_equal(true)
```

</details>

#### exposes SimpleOS app content through the common web render request

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = simple_web_app_render_request_with_theme("glass_dark", "Terminal", "ready", 80, 40)
expect(req.target).to_equal(WEB_RENDER_TARGET_SIMPLE_WEB)
expect(req.viewport_w).to_equal(80)
expect(req.viewport_h).to_equal(40)
expect(req.body_html.contains("wm-app-container")).to_equal(true)
expect(req.css.contains("simple-web-line")).to_equal(true)
```

</details>

#### exposes SimpleOS app pixels through the common web render artifact

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val artifact = simple_web_app_pixel_artifact_with_theme("glass_dark", "Terminal", 32, 20, "ready")
expect(artifact.target).to_equal(WEB_RENDER_TARGET_SIMPLE_WEB)
expect(artifact.viewport_w).to_equal(32)
expect(artifact.viewport_h).to_equal(20)
expect(artifact.pixels.len()).to_equal(32 * 20)
expect(_count_changed(artifact.pixels, 0xFFFFFFFFu32)).to_be_greater_than(0)
```

</details>

#### blits Simple Web rendered pixels into a compositor backend

1. var backend = BrowserCompositorBackend with color
2. render simple web app content
   - Expected: pixels.len() equals `96 * 64`
   - Expected: pixels[0] equals `0xFF000000`
   - Expected: pixels[6 * 96 + 8] equals `artifact.pixels[0]`
   - Expected: pixels[15 * 96 + 23] equals `artifact.pixels[9 * 32 + 15]`
   - Expected: pixels[25 * 96 + 39] equals `artifact.pixels[19 * 32 + 31]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = BrowserCompositorBackend.with_color(96, 64, 0xFF000000)
val artifact = simple_web_app_pixel_artifact_with_theme("glass_dark", "Terminal", 32, 20, "ready")
render_simple_web_app_content(backend, "Terminal", 8, 6, 32, 20, "ready")
val pixels = backend.get_pixel_buffer()

expect(pixels.len()).to_equal(96 * 64)
expect(_count_changed(pixels, 0xFF000000)).to_be_greater_than(0)
expect(pixels[0]).to_equal(0xFF000000)
expect(pixels[6 * 96 + 8]).to_equal(artifact.pixels[0])
expect(pixels[15 * 96 + 23]).to_equal(artifact.pixels[9 * 32 + 15])
expect(pixels[25 * 96 + 39]).to_equal(artifact.pixels[19 * 32 + 31])
```

</details>

#### uses the configured Engine2D backend through the renderer facade

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = simple_web_app_html("Simple Browser", "")
val req = WebRenderRequest.html(WEB_RENDER_TARGET_SIMPLE_WEB, "Simple Browser", html, "", "", 40, 24).with_pixel_output()
val pixels = compositor_render_html_pixels_with_backend(req, html, "software")

expect(pixels.len()).to_equal(40 * 24)
expect(_count_changed(pixels, 0xFFFFFFFFu32)).to_be_greater_than(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/compositor/simple_web_window_renderer_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Simple Web compositor adapter

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
