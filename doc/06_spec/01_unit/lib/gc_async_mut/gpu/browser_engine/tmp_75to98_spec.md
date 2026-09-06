# Tmp 75to98 Specification

> Tests covering BrowserRenderer HTML rendering.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tmp 75to98 Specification

## Scenarios

### BrowserRenderer HTML rendering

#### uses the same pixels as an explicit Engine2D software renderer

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- uses the same pixels as an explicit Engine2D software renderer
   - Expected: default_renderer.engine == nil is true
   - Expected: software_renderer.engine == nil is false
   - Expected: default_renderer.backend_name() equals `software`
   - Expected: software_renderer.backend_name() equals `software`
   - Expected: _pixels_equal(default_pixels, software_pixels) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("uses the same pixels as an explicit Engine2D software renderer")
val html = "<html><body><div style='width: 90px; height: 40px; background-color: #2050a0'></div><span style='color:#ffffff'>Hi</span></body></html>"
val default_renderer = BrowserRenderer.create(TEST_WIDTH, TEST_HEIGHT)
val software_renderer = BrowserRenderer.create_with_backend(TEST_WIDTH, TEST_HEIGHT, "software")
val default_pixels = default_renderer.render_html_to_pixels(html).pixel_data
val software_pixels = software_renderer.render_html_to_pixels(html).pixel_data
expect(default_renderer.engine == nil).to_equal(true)
expect(software_renderer.engine == nil).to_equal(false)
expect(default_renderer.backend_name()).to_equal("software")
expect(software_renderer.backend_name()).to_equal("software")
expect(_pixels_equal(default_pixels, software_pixels)).to_equal(true)
```

</details>

#### reports deterministic software for unknown backend fallback

- reports deterministic software for unknown backend fallback
   - Expected: renderer.engine == nil is true
   - Expected: renderer.backend_name() equals `software`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports deterministic software for unknown backend fallback")
val renderer = BrowserRenderer.create_with_backend(TEST_WIDTH, TEST_HEIGHT, "not-a-backend")
expect(renderer.engine == nil).to_equal(true)
expect(renderer.backend_name()).to_equal("software")
```

</details>

#### module pixel helper matches explicit Engine2D software rendering

- module pixel helper matches explicit Engine2D software rendering
   - Expected: _pixels_equal(helper_pixels, renderer_pixels) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("module pixel helper matches explicit Engine2D software rendering")
val html = "<html><body><div style='width: 110px; height: 30px; background-color: #aa2244'></div></body></html>"
val helper_pixels = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT).pixel_data
val renderer = BrowserRenderer.create_with_backend(TEST_WIDTH, TEST_HEIGHT, "software")
val renderer_pixels = renderer.render_html_to_pixels(html).pixel_data
expect(_pixels_equal(helper_pixels, renderer_pixels)).to_equal(true)
```

</details>

#### renders famous-site corpus block at Chrome default body margin

- renders famous-site corpus block at Chrome default body margin
   - Expected: pixels.len() equals `160 * 120`
   - Expected: pixels[0] equals `0xFFFFFFFFu32`
   - Expected: pixels[7 + 7 * 160] equals `0xFFFFFFFFu32`
   - Expected: pixels[8 + 8 * 160] equals `0xFF2563EBu32`
   - Expected: pixels[127 + 47 * 160] equals `0xFF2563EBu32`
   - Expected: pixels[128 + 48 * 160] equals `0xFFFFFFFFu32`
   - Expected: _count_region_changed(pixels, 160, 128, 8, 32, 40, 0xFFFFFFFFu32) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders famous-site corpus block at Chrome default body margin")
val html = "<html><body><div style='width: 120px; height: 40px; background-color: #2563eb'>Google search deterministic compatibility fixture</div></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, 160, 120).pixel_data
expect(pixels.len()).to_equal(160 * 120)
expect(pixels[0]).to_equal(0xFFFFFFFFu32)
expect(pixels[7 + 7 * 160]).to_equal(0xFFFFFFFFu32)
expect(pixels[8 + 8 * 160]).to_equal(0xFF2563EBu32)
expect(pixels[127 + 47 * 160]).to_equal(0xFF2563EBu32)
expect(pixels[128 + 48 * 160]).to_equal(0xFFFFFFFFu32)
expect(_count_region_changed(pixels, 160, 20, 19, 92, 18, 0xFF2563EBu32)).to_be_greater_than(0)
expect(_count_region_changed(pixels, 160, 8, 48, 120, 36, 0xFFFFFFFFu32)).to_be_greater_than(0)
expect(_count_region_changed(pixels, 160, 128, 8, 32, 40, 0xFFFFFFFFu32)).to_equal(0)
```

</details>

#### Engine2D bridge keeps explicit backend rendering available

- Engine2D bridge keeps explicit backend rendering available
   - Expected: bridge_renderer.engine == nil is false
   - Expected: explicit_renderer.engine == nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("Engine2D bridge keeps explicit backend rendering available")
val html = "<html><body><div style='width: 70px; height: 24px; background-color: #4488cc'></div></body></html>"
val bridge_renderer = create_software_browser_renderer(TEST_WIDTH, TEST_HEIGHT)
val explicit_renderer = create_gpu_browser_renderer_with_backend(TEST_WIDTH, TEST_HEIGHT, "software")
expect(bridge_renderer.engine == nil).to_equal(false)
expect(explicit_renderer.engine == nil).to_equal(false)
expect(_pixels_equal(
    bridge_renderer.render_html_to_pixels(html).pixel_data,
    explicit_renderer.render_html_to_pixels(html).pixel_data
)).to_equal(true)
```

</details>

#### Engine2D GPU bridge requests Metal while preserving CPU parity fallback

- Engine2D GPU bridge requests Metal while preserving CPU parity fallback
   - Expected: gpu_renderer.backend_name() equals `metal`
   - Expected: cpu_renderer.backend_name() equals `cpu`
   - Expected: _pixels_equal(gpu_pixels, cpu_pixels) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("Engine2D GPU bridge requests Metal while preserving CPU parity fallback")
val html = "<html><body><div style='width: 12px; height: 8px; background-color: #2563eb'></div></body></html>"
val gpu_renderer = create_gpu_browser_renderer(TEST_WIDTH, TEST_HEIGHT)
val cpu_renderer = create_gpu_browser_renderer_with_backend(TEST_WIDTH, TEST_HEIGHT, "cpu")
val gpu_pixels = gpu_renderer.render_html_to_pixels(html).pixel_data
val cpu_pixels = cpu_renderer.render_html_to_pixels(html).pixel_data
expect(gpu_renderer.backend_name()).to_equal("metal")
expect(cpu_renderer.backend_name()).to_equal("cpu")
expect(_count_color(gpu_pixels, 0xFF2563EBu32)).to_be_greater_than(0)
expect(_pixels_equal(gpu_pixels, cpu_pixels)).to_equal(true)
```

</details>

#### renders CSS background fixture pixels through BrowserRenderer

- renders CSS background fixture pixels through BrowserRenderer
   - Expected: pixels.len() equals `40 * 70`
   - Expected: pixels[0] equals `0xFFF0F0F8u32`
   - Expected: pixels[8 + 8 * 40] equals `0xFFD0D8E8u32`
   - Expected: pixels[27 + 61 * 40] equals `0xFFBFDBFEu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders CSS background fixture pixels through BrowserRenderer")
val pixels = render_html_to_pixels_with_viewport(_html_compat_fixture("15_background"), 40, 70).pixel_data
expect(pixels.len()).to_equal(40 * 70)
expect(pixels[0]).to_equal(0xFFF0F0F8u32)
expect(pixels[8 + 8 * 40]).to_equal(0xFFD0D8E8u32)
expect(pixels[27 + 61 * 40]).to_equal(0xFFBFDBFEu32)
```

</details>

#### renders CSS color fixture pixels through BrowserRenderer

- renders CSS color fixture pixels through BrowserRenderer
   - Expected: pixels.len() equals `40 * 70`
   - Expected: pixels[8 + 8 * 40] equals `0xFFDBEAFEu32`
   - Expected: pixels[8 + 28 * 40] equals `0xFFBFDBFEu32`
   - Expected: pixels[8 + 48 * 40] equals `0xFF93C5FDu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders CSS color fixture pixels through BrowserRenderer")
val pixels = render_html_to_pixels_with_viewport(_html_compat_fixture("10_colors"), 40, 70).pixel_data
expect(pixels.len()).to_equal(40 * 70)
expect(pixels[8 + 8 * 40]).to_equal(0xFFDBEAFEu32)
expect(pixels[8 + 28 * 40]).to_equal(0xFFBFDBFEu32)
expect(pixels[8 + 48 * 40]).to_equal(0xFF93C5FDu32)
```

</details>

#### renders CSS padding fixture pixels through BrowserRenderer

- renders CSS padding fixture pixels through BrowserRenderer
   - Expected: pixels.len() equals `40 * 90`
   - Expected: pixels[16 + 16 * 40] equals `0xFFDBEAFEu32`
   - Expected: pixels[22 + 50 * 40] equals `0xFFBFDBFEu32`
   - Expected: pixels[22 + 78 * 40] equals `0xFF93C5FDu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders CSS padding fixture pixels through BrowserRenderer")
val pixels = render_html_to_pixels_with_viewport(_html_compat_fixture("12_padding"), 40, 90).pixel_data
expect(pixels.len()).to_equal(40 * 90)
expect(pixels[16 + 16 * 40]).to_equal(0xFFDBEAFEu32)
expect(pixels[22 + 50 * 40]).to_equal(0xFFBFDBFEu32)
expect(pixels[22 + 78 * 40]).to_equal(0xFF93C5FDu32)
```

</details>

#### renders CSS margin fixture pixels through BrowserRenderer

- renders CSS margin fixture pixels through BrowserRenderer
   - Expected: pixels.len() equals `40 * 95`
   - Expected: pixels[14 + 14 * 40] equals `0xFFDBEAFEu32`
   - Expected: pixels[22 + 52 * 40] equals `0xFFBFDBFEu32`
   - Expected: pixels[22 + 82 * 40] equals `0xFF93C5FDu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders CSS margin fixture pixels through BrowserRenderer")
val pixels = render_html_to_pixels_with_viewport(_html_compat_fixture("13_margin"), 40, 95).pixel_data
expect(pixels.len()).to_equal(40 * 95)
expect(pixels[14 + 14 * 40]).to_equal(0xFFDBEAFEu32)
expect(pixels[22 + 52 * 40]).to_equal(0xFFBFDBFEu32)
expect(pixels[22 + 82 * 40]).to_equal(0xFF93C5FDu32)
```

</details>

#### renders CSS border fixture pixels through BrowserRenderer

- renders CSS border fixture pixels through BrowserRenderer
   - Expected: pixels.len() equals `40 * 70`
   - Expected: pixels[4 + 4 * 40] equals `0xFF1A1A1Au32`
   - Expected: pixels[18 + 18 * 40] equals `0xFF003366u32`
   - Expected: pixels[27 + 61 * 40] equals `0xFF006600u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders CSS border fixture pixels through BrowserRenderer")
val pixels = render_html_to_pixels_with_viewport(_html_compat_fixture("14_border"), 40, 70).pixel_data
expect(pixels.len()).to_equal(40 * 70)
expect(pixels[4 + 4 * 40]).to_equal(0xFF1A1A1Au32)
expect(pixels[18 + 18 * 40]).to_equal(0xFF003366u32)
expect(pixels[27 + 61 * 40]).to_equal(0xFF006600u32)
```

</details>

#### renders CSS flex row fixture pixels through BrowserRenderer

- renders CSS flex row fixture pixels through BrowserRenderer
   - Expected: pixels.len() equals `125 * 70`
   - Expected: pixels[121 + 61 * 125] equals `0xFF93C5FDu32`
   - Expected: pixels[27 + 61 * 125] equals `0xFFBFDBFEu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders CSS flex row fixture pixels through BrowserRenderer")
val pixels = render_html_to_pixels_with_viewport(_html_compat_fixture("16_flex_row"), 125, 70).pixel_data
expect(pixels.len()).to_equal(125 * 70)
expect(pixels[121 + 61 * 125]).to_equal(0xFF93C5FDu32)
expect(pixels[27 + 61 * 125]).to_equal(0xFFBFDBFEu32)
```

</details>

#### renders CSS flex column fixture pixels through BrowserRenderer

- renders CSS flex column fixture pixels through BrowserRenderer
   - Expected: pixels.len() equals `40 * 100`
   - Expected: pixels[27 + 61 * 40] equals `0xFFBFDBFEu32`
   - Expected: pixels[27 + 95 * 40] equals `0xFF93C5FDu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders CSS flex column fixture pixels through BrowserRenderer")
val pixels = render_html_to_pixels_with_viewport(_html_compat_fixture("17_flex_col"), 40, 100).pixel_data
expect(pixels.len()).to_equal(40 * 100)
expect(pixels[27 + 61 * 40]).to_equal(0xFFBFDBFEu32)
expect(pixels[27 + 95 * 40]).to_equal(0xFF93C5FDu32)
```

</details>

#### parses rgb() background-color in the fallback pixel path

- parses rgb() background-color in the fallback pixel path
   - Expected: pixels.len() equals `8 * 6`
   - Expected: pixels[0] equals `0xFF2563EBu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses rgb() background-color in the fallback pixel path")
val html = "<html><body style='background-color: rgb(37, 99, 235)'></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, 8, 6).pixel_data
expect(pixels.len()).to_equal(8 * 6)
expect(pixels[0]).to_equal(0xFF2563EBu32)
```

</details>

#### parses modern space-separated rgb() background-color in the fallback pixel path

- parses modern space-separated rgb() background-color in the fallback pixel path
   - Expected: pixels.len() equals `8 * 6`
   - Expected: pixels[0] equals `0xFF059669u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses modern space-separated rgb() background-color in the fallback pixel path")
val html = "<html><body style='background-color: rgb(5 150 105)'></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, 8, 6).pixel_data
expect(pixels.len()).to_equal(8 * 6)
expect(pixels[0]).to_equal(0xFF059669u32)
```

</details>

#### composites rgba() background-color over the white page in the fallback pixel path

- composites rgba() background-color over the white page in the fallback pixel path
   - Expected: pixels.len() equals `8 * 6`
   - Expected: pixels[0] equals `0xFF808080u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("composites rgba() background-color over the white page in the fallback pixel path")
val html = "<html><body style='background-color: rgba(0, 0, 0, 0.5)'></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, 8, 6).pixel_data
expect(pixels.len()).to_equal(8 * 6)
expect(pixels[0]).to_equal(0xFF808080u32)
```

</details>

#### parses shorthand hex background-color in the fallback pixel path

- parses shorthand hex background-color in the fallback pixel path
   - Expected: pixels.len() equals `8 * 6`
   - Expected: pixels[0] equals `0xFF00FF88u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses shorthand hex background-color in the fallback pixel path")
val html = "<html><body style='background-color: #0f8'></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, 8, 6).pixel_data
expect(pixels.len()).to_equal(8 * 6)
expect(pixels[0]).to_equal(0xFF00FF88u32)
```

</details>

#### composites shorthand hex alpha background-color over the white page in the fallback pixel path

- composites shorthand hex alpha background-color over the white page in the fallback pixel path
   - Expected: pixels.len() equals `8 * 6`
   - Expected: pixels[0] equals `0xFF777777u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("composites shorthand hex alpha background-color over the white page in the fallback pixel path")
val html = "<html><body style='background-color: #0008'></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, 8, 6).pixel_data
expect(pixels.len()).to_equal(8 * 6)
expect(pixels[0]).to_equal(0xFF777777u32)
```

</details>

#### parses named CSS background-color in the fallback pixel path

- parses named CSS background-color in the fallback pixel path
   - Expected: pixels.len() equals `8 * 6`
   - Expected: pixels[0] equals `0xFF663399u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses named CSS background-color in the fallback pixel path")
val html = "<html><body style='background-color: rebeccapurple'></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, 8, 6).pixel_data
expect(pixels.len()).to_equal(8 * 6)
expect(pixels[0]).to_equal(0xFF663399u32)
```

</details>

#### composites transparent background-color to the white page in the fallback pixel path

- composites transparent background-color to the white page in the fallback pixel path
   - Expected: pixels.len() equals `8 * 6`
   - Expected: pixels[0] equals `0xFFFFFFFFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("composites transparent background-color to the white page in the fallback pixel path")
val html = "<html><body style='background-color: transparent'></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, 8, 6).pixel_data
expect(pixels.len()).to_equal(8 * 6)
expect(pixels[0]).to_equal(0xFFFFFFFFu32)
```

</details>

#### parses hsl() background-color in the fallback pixel path

- parses hsl() background-color in the fallback pixel path
   - Expected: pixels.len() equals `8 * 6`
   - Expected: pixels[0] equals `0xFF008000u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses hsl() background-color in the fallback pixel path")
val html = "<html><body style='background-color: hsl(120, 100%, 25%)'></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, 8, 6).pixel_data
expect(pixels.len()).to_equal(8 * 6)
expect(pixels[0]).to_equal(0xFF008000u32)
```

</details>

#### parses color-first background shorthand in the fallback pixel path

- parses color-first background shorthand in the fallback pixel path
   - Expected: pixels.len() equals `8 * 6`
   - Expected: pixels[0] equals `0xFF663399u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses color-first background shorthand in the fallback pixel path")
val html = "<html><body style='background: rebeccapurple no-repeat'></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, 8, 6).pixel_data
expect(pixels.len()).to_equal(8 * 6)
expect(pixels[0]).to_equal(0xFF663399u32)
```

</details>

#### parses function color background shorthand before trailing tokens

- parses function color background shorthand before trailing tokens
   - Expected: pixels.len() equals `8 * 6`
   - Expected: pixels[0] equals `0xFF059669u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses function color background shorthand before trailing tokens")
val html = "<html><body style='background: rgb(5, 150, 105) no-repeat'></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, 8, 6).pixel_data
expect(pixels.len()).to_equal(8 * 6)
expect(pixels[0]).to_equal(0xFF059669u32)
```

</details>

#### parses fallback color after url() in background shorthand

- parses fallback color after url() in background shorthand
   - Expected: pixels.len() equals `8 * 6`
   - Expected: pixels[0] equals `0xFF00FF88u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses fallback color after url() in background shorthand")
val html = "<html><body style='background: url(hero.png) #0f8 no-repeat'></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, 8, 6).pixel_data
expect(pixels.len()).to_equal(8 * 6)
expect(pixels[0]).to_equal(0xFF00FF88u32)
```

</details>

#### lets later background shorthand override earlier background-color in fallback pixels

- lets later background shorthand override earlier background-color in fallback pixels
   - Expected: pixels.len() equals `8 * 6`
   - Expected: pixels[0] equals `0xFF00FF88u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("lets later background shorthand override earlier background-color in fallback pixels")
val html = "<html><body style='background-color: rebeccapurple; background: #0f8'></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, 8, 6).pixel_data
expect(pixels.len()).to_equal(8 * 6)
expect(pixels[0]).to_equal(0xFF00FF88u32)
```

</details>

#### lets later background-color override earlier background shorthand in fallback pixels

- lets later background-color override earlier background shorthand in fallback pixels
   - Expected: pixels.len() equals `8 * 6`
   - Expected: pixels[0] equals `0xFF663399u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("lets later background-color override earlier background shorthand in fallback pixels")
val html = "<html><body style='background: #0f8; background-color: rebeccapurple'></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, 8, 6).pixel_data
expect(pixels.len()).to_equal(8 * 6)
expect(pixels[0]).to_equal(0xFF663399u32)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_75to98_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering BrowserRenderer HTML rendering.
- BrowserRenderer HTML rendering

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
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

- Canonical SPipe generation for source `59841d85e17fb7337e89c1871c83255f14503d76d13e2f7991256809229d60c7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `59841d85e17fb7337e89c1871c83255f14503d76d13e2f7991256809229d60c7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `59841d85e17fb7337e89c1871c83255f14503d76d13e2f7991256809229d60c7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_75to98_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_75to98_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_75to98_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_75to98_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_75to98_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_75to98_spec.spl:107:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses the same pixels as an explicit Engine2D software renderer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_75to98_spec.spl:121:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports deterministic software for unknown backend fallback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_75to98_spec.spl:128:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'module pixel helper matches explicit Engine2D software rendering' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
