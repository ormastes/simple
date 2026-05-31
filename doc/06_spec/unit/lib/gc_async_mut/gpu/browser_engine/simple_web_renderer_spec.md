# Simple Web Renderer Specification

## Scenarios

### SimpleWebRenderer

#### renders HTML through the canonical browser engine to RenderScene

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><div style='width: 80px; height: 40px; background-color: #2050a0'></div></body></html>"
val scene = simple_web_render_html_to_scene(html, 120, 80)
expect(scene.width).to_equal(120)
expect(scene.height).to_equal(80)
expect(scene.commands.len()).to_be_greater_than(0)
```

</details>

#### renders inline url background shorthand fallback colors through RenderScene

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><div style='width: 80px; height: 40px; background: url(hero.png) #0f8 no-repeat'></div></body></html>"
expect(_simple_scene_has_fill_color(html, 0xFF00FF88u32)).to_equal(true)
```

</details>

#### renders style block url background shorthand fallback colors through RenderScene

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>.card { width: 80px; height: 40px; background: url(hero.png) #0f8 no-repeat; }</style></head><body><div class='card'></div></body></html>"
expect(_simple_scene_has_fill_color(html, 0xFF00FF88u32)).to_equal(true)
```

</details>

#### renders HTML to pixels for framebuffer and host adapters

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><div style='width: 80px; height: 40px; background-color: #2050a0'></div></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 120, 80)
expect(pixels.len()).to_equal(120 * 80)
expect(_count_non_bg(pixels, 0xFFFFFFFF)).to_be_greater_than(0)
```

</details>

#### applies style block colors in the generic layout renderer

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>header { background-color:#1d4ed8; color:#ffffff; font-size:8px; padding:1px; }</style></head><body><header>CMD</header></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 96, 64)
expect(pixels.len()).to_equal(96 * 64)
expect(_count_color(pixels, 0xFF1D4ED8u32)).to_be_greater_than(0)
expect(_count_color(pixels, 0xFF141418u32)).to_equal(0)
```

</details>

#### applies class selector colors and inline overrides in generic layout

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>.status{background-color:#22c55e;color:#052e16;font-size:8px;padding:1px}#override{background-color:#f59e0b;color:#111827;font-size:8px;padding:1px}</style></head><body><div class='status'>CLASS</div><button id='override' style='background-color:#ef4444;color:#ffffff;font-size:8px;padding:1px'>INLINE</button></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 96, 64)
expect(pixels.len()).to_equal(96 * 64)
expect(_count_color(pixels, 0xFF22C55Eu32)).to_be_greater_than(0)
expect(_count_color(pixels, 0xFFEF4444u32)).to_be_greater_than(0)
expect(_count_color(pixels, 0xFFF59E0Bu32)).to_equal(0)
```

</details>

#### scopes descendant selector colors to matching ancestors

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>.status{background-color:#334155;color:#ffffff;font-size:8px;padding:1px}.panel .status{background-color:#22c55e;color:#052e16;font-size:8px;padding:1px}</style></head><body><section class='panel'><div class='status'>IN</div></section><div class='status'>OUT</div></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 96, 64)
expect(pixels.len()).to_equal(96 * 64)
expect(_count_color(pixels, 0xFF22C55Eu32)).to_be_greater_than(0)
expect(_count_color(pixels, 0xFF334155u32)).to_be_greater_than(0)
```

</details>

#### paints famous-site corpus block geometry with Chrome default body margin

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><div data-font-corpus=\"known-site-fonts\" style='width: 120px; height: 40px; background-color: #7c3aed; font-family: \"IBM Plex Sans\", Arial, sans-serif'>Twitch commerce deterministic compatibility fixture</div></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 160, 120)
expect(pixels.len()).to_equal(160 * 120)
expect(pixels[7 + 7 * 160]).to_equal(0xFFFFFFFFu32)
expect(pixels[8 + 8 * 160]).to_equal(0xFF7C3AEDu32)
expect(pixels[127 + 47 * 160]).to_equal(0xFF7C3AEDu32)
expect(pixels[128 + 48 * 160]).to_equal(0xFFFFFFFFu32)
expect(pixels[9 + 10 * 160]).to_equal(0xFF7C3AEDu32)
expect(pixels[32 + 93 * 160]).to_equal(0xFFFFFFFFu32)
```

</details>

#### keeps exact Twitch corpus pixels in the fixture renderer

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><div data-font-corpus=\"known-site-fonts\" style='width: 120px; height: 40px; background-color: #7c3aed; font-family: \"IBM Plex Sans\", Arial, sans-serif'>Twitch commerce deterministic compatibility fixture</div></body></html>"
val pixels = simple_web_render_html_to_pixels_with_corpus_fixtures(html, 160, 120)
expect(pixels.len()).to_equal(160 * 120)
expect(pixels[9 + 10 * 160]).to_equal(0xFF000000u32)
expect(pixels[52 + 14 * 160]).to_equal(0xFF4930E5u32)
expect(pixels[32 + 93 * 160]).to_equal(0xFF000000u32)
```

</details>

#### returns an RGBA byte frame from the URL facade

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = simple_web_render_url_to_pixels("about:network", 120, 80)
expect(pixels.len()).to_equal(120 * 80 * 4)
```

</details>

#### keeps backend choice wrapped behind the renderer interface

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val renderer = SimpleWebRenderer.create_with_backend(96, 64, "software")
val pixels = renderer.render_url_to_pixels("about:blank")
expect(renderer.backend_name).to_equal("software")
expect(pixels.len()).to_equal(96 * 64)
```

</details>

#### reports the actual backend after invalid backend fallback

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val renderer = SimpleWebRenderer.create_with_backend(96, 64, "not-a-backend")
val pixels = renderer.render_url_to_pixels("about:blank")
expect(renderer.backend_name).to_equal("software")
expect(pixels.len()).to_equal(96 * 64)
```

</details>

#### keeps BrowserRenderer.render_html_to_pixels on the non-empty software path

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val renderer = BrowserRenderer.create(48, 32)
val html = "<html><body><div style='width:24px; height:16px; background-color:#2563eb'>Ready</div></body></html>"
val result = renderer.render_html_to_pixels(html)
expect(result.pixel_data.len()).to_equal(48 * 32)
expect(_count_non_bg(result.pixel_data, 0xFFFFFFFF)).to_be_greater_than(0)
expect(result.source_html).to_equal(html)
expect(result.has_html_capture()).to_equal(true)
```

</details>

#### default renderer uses the BrowserRenderer Engine2D software pixel path

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><div style='width: 72px; height: 32px; background-color: #44aa22'></div><span style='color:#ffffff'>Simple</span></body></html>"
val simple = SimpleWebRenderer.create(120, 80)
val browser = BrowserRenderer.create_with_backend(120, 80, "software")
val simple_pixels = simple.render_html_to_pixels(html)
val browser_pixels = browser.render_html_to_pixels(html).pixel_data
expect(simple.backend_name).to_equal("software")
expect(_pixels_equal(simple_pixels, browser_pixels)).to_equal(true)
```

</details>

#### fallback facade parses rgb() background-color with the shared CSS parser

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background-color: rgb(5, 150, 105)'>Simple Web Renderer</body></html>"
val pixels = simple_web_render_html_to_pixels(html, 8, 220)
expect(pixels.len()).to_equal(8 * 220)
expect(pixels[7 + 210 * 8]).to_equal(0xFF059669u32)
```

</details>

#### fallback facade composites rgba() background-color over the white page

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background-color: rgba(0, 0, 0, 0.5)'>Simple Web Renderer</body></html>"
val pixels = simple_web_render_html_to_pixels(html, 8, 220)
expect(pixels.len()).to_equal(8 * 220)
expect(pixels[7 + 210 * 8]).to_equal(0xFF808080u32)
```

</details>

#### fallback facade parses shorthand hex background-color

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background-color: #0f8'>Simple Web Renderer</body></html>"
val pixels = simple_web_render_html_to_pixels(html, 8, 220)
expect(pixels.len()).to_equal(8 * 220)
expect(pixels[7 + 210 * 8]).to_equal(0xFF00FF88u32)
```

</details>

#### fallback facade composites shorthand hex alpha background-color to the white page

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background-color: #0008'>Simple Web Renderer</body></html>"
val pixels = simple_web_render_html_to_pixels(html, 8, 220)
expect(pixels.len()).to_equal(8 * 220)
expect(pixels[7 + 210 * 8]).to_equal(0xFF777777u32)
```

</details>

#### fallback facade parses named CSS background-color

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background-color: rebeccapurple'>Simple Web Renderer</body></html>"
val pixels = simple_web_render_html_to_pixels(html, 8, 220)
expect(pixels.len()).to_equal(8 * 220)
expect(pixels[7 + 210 * 8]).to_equal(0xFF663399u32)
```

</details>

#### fallback facade composites transparent background-color to the white page

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background-color: transparent'>Simple Web Renderer</body></html>"
val pixels = simple_web_render_html_to_pixels(html, 8, 220)
expect(pixels.len()).to_equal(8 * 220)
expect(pixels[7 + 210 * 8]).to_equal(0xFFFFFFFFu32)
```

</details>

#### fallback facade parses hsl() background-color

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background-color: hsl(120, 100%, 25%)'>Simple Web Renderer</body></html>"
val pixels = simple_web_render_html_to_pixels(html, 8, 220)
expect(pixels.len()).to_equal(8 * 220)
expect(pixels[7 + 210 * 8]).to_equal(0xFF008000u32)
```

</details>

#### fallback facade resolves background-color currentColor from text color

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background-color: currentColor; color: #456789'>Simple Web Renderer</body></html>"
val pixels = simple_web_render_html_to_pixels(html, 8, 220)
expect(pixels.len()).to_equal(8 * 220)
expect(pixels[7 + 210 * 8]).to_equal(0xFF456789u32)
```

</details>

#### fallback facade parses color-first background shorthand

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background: rebeccapurple no-repeat'>Simple Web Renderer</body></html>"
val pixels = simple_web_render_html_to_pixels(html, 8, 220)
expect(pixels.len()).to_equal(8 * 220)
expect(pixels[7 + 210 * 8]).to_equal(0xFF663399u32)
```

</details>

#### fallback facade parses function color background shorthand before trailing tokens

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background: rgb(5, 150, 105) no-repeat'>Simple Web Renderer</body></html>"
val pixels = simple_web_render_html_to_pixels(html, 8, 220)
expect(pixels.len()).to_equal(8 * 220)
expect(pixels[7 + 210 * 8]).to_equal(0xFF059669u32)
```

</details>

#### fallback facade parses fallback color after url() in background shorthand

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background: url(hero.png) #0f8 no-repeat'>Simple Web Renderer</body></html>"
val pixels = simple_web_render_html_to_pixels(html, 8, 220)
expect(pixels.len()).to_equal(8 * 220)
expect(pixels[7 + 210 * 8]).to_equal(0xFF00FF88u32)
```

</details>

#### fallback facade resolves background shorthand currentColor from text color

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background: currentColor no-repeat; color: #345678'>Simple Web Renderer</body></html>"
val pixels = simple_web_render_html_to_pixels(html, 8, 220)
expect(pixels.len()).to_equal(8 * 220)
expect(pixels[7 + 210 * 8]).to_equal(0xFF345678u32)
```

</details>

#### fallback facade lets later background shorthand override earlier background-color

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background-color: rebeccapurple; background: #0f8'>Simple Web Renderer</body></html>"
val pixels = simple_web_render_html_to_pixels(html, 8, 220)
expect(pixels.len()).to_equal(8 * 220)
expect(pixels[7 + 210 * 8]).to_equal(0xFF00FF88u32)
```

</details>

#### fallback facade lets later background-color override earlier background shorthand

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background: #0f8; background-color: rebeccapurple'>Simple Web Renderer</body></html>"
val pixels = simple_web_render_html_to_pixels(html, 8, 220)
expect(pixels.len()).to_equal(8 * 220)
expect(pixels[7 + 210 * 8]).to_equal(0xFF663399u32)
```

</details>

#### fallback facade applies attribute presence selectors to the first visual block

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } [data-card] { width: 12px; height: 8px; background-color: #0e7490; }</style></head><body><div data-card='true'></div></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 64, 64)
expect(_count_color(pixels, 0xFF0E7490u32)).to_equal(96)
```

</details>

#### fallback facade rejects non matching exact attribute selectors

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div[data-state='active'] { width: 12px; height: 8px; background-color: #4d7c0f; }</style></head><body><div data-state='inactive'></div></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 64, 64)
expect(_count_color(pixels, 0xFF4D7C0Fu32)).to_equal(0)
```

</details>

#### fallback facade applies attribute prefix selectors to the first visual block

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div[data-route^='/app'] { width: 12px; height: 8px; background-color: #0f5e9c; }</style></head><body><div data-route='/app/home'></div></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 64, 64)
expect(_count_color(pixels, 0xFF0F5E9Cu32)).to_equal(96)
```

</details>

#### fallback facade rejects non matching attribute suffix selectors

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div[data-route$='/settings'] { width: 12px; height: 8px; background-color: #065f46; }</style></head><body><div data-route='/app/settings/profile'></div></body></html>"
val pixels = simple_web_render_html_to_pixels(html, 64, 64)
expect(_count_color(pixels, 0xFF065F46u32)).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/gc_async_mut/gpu/browser_engine/simple_web_renderer_spec.spl` |
| Updated | 2026-05-31 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleWebRenderer

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 32 |
| Active scenarios | 32 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

