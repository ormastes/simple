# Glass Render E2e Specification

> <details>

<!-- sdn-diagram:id=glass_render_e2e_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=glass_render_e2e_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

glass_render_e2e_spec -> std
glass_render_e2e_spec -> common
glass_render_e2e_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=glass_render_e2e_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Glass Render E2e Specification

## Scenarios

### Glass Theme End-to-End Rendering

#### glass_dark theme

#### generates non-empty HTML

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = generate_glass_test_html("glass_dark")
expect(html.len()).to_be_greater_than(100)
# Should contain key structural elements
expect(html).to_contain("glass-window")
expect(html).to_contain("glass-titlebar")
expect(html).to_contain("widget-button")
```

</details>

#### renders to non-empty pixel buffer

1. var renderer = BrowserRenderer create
   - Expected: result.pixel_data.len() equals `PIXEL_COUNT`
   - Expected: result.format equals `pixels`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = generate_glass_test_html("glass_dark")
var renderer = BrowserRenderer.create(W, H)
val result = renderer.render_html_to_pixels(html)
expect(result.pixel_data.len()).to_equal(PIXEL_COUNT)
expect(result.format).to_equal("pixels")
```

</details>

#### pixels contain dark background colors

1. var renderer = BrowserRenderer create
   - Expected: result.pixel_data.len() equals `PIXEL_COUNT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = generate_glass_test_html("glass_dark")
var renderer = BrowserRenderer.create(W, H)
val result = renderer.render_html_to_pixels(html)
expect(result.pixel_data.len()).to_equal(PIXEL_COUNT)
# Dark background is #0A0A0F -> 0xFF0A0A0F in ARGB
# Check first row for dark pixels (within tolerance of 30)
val dark_bg: u32 = 0xFF0A0A0F
val dark_count = count_pixels_near(result.pixel_data, 0, W, dark_bg, 30)
# At least some pixels in the first row should be near the bg color
expect(dark_count).to_be_greater_than(0)
```

</details>

#### pixels contain glass accent blue

1. var renderer = BrowserRenderer create
   - Expected: result.pixel_data.len() equals `PIXEL_COUNT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = generate_glass_test_html("glass_dark")
var renderer = BrowserRenderer.create(W, H)
val result = renderer.render_html_to_pixels(html)
expect(result.pixel_data.len()).to_equal(PIXEL_COUNT)
# iOS blue accent #007AFF -> 0xFF007AFF or #0A84FF -> 0xFF0A84FF
# Search full buffer for blue accent pixels (tolerance 40)
val blue1: u32 = 0xFF007AFF
val blue2: u32 = 0xFF0A84FF
val blue_count_1 = count_pixels_near(result.pixel_data, 0, PIXEL_COUNT, blue1, 40)
val blue_count_2 = count_pixels_near(result.pixel_data, 0, PIXEL_COUNT, blue2, 40)
val total_blue = blue_count_1 + blue_count_2
# At least some accent-blue pixels should be present (buttons, dock, etc.)
expect(total_blue).to_be_greater_than(0)
```

</details>

#### glass_light theme

#### renders to non-empty pixel buffer

1. var renderer = BrowserRenderer create
   - Expected: result.pixel_data.len() equals `PIXEL_COUNT`
   - Expected: result.format equals `pixels`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = generate_glass_test_html("glass_light")
var renderer = BrowserRenderer.create(W, H)
val result = renderer.render_html_to_pixels(html)
expect(result.pixel_data.len()).to_equal(PIXEL_COUNT)
expect(result.format).to_equal("pixels")
```

</details>

#### light theme differs from dark theme

1. var renderer d = BrowserRenderer create
2. var renderer l = BrowserRenderer create
   - Expected: dark_result.pixel_data.len() equals `PIXEL_COUNT`
   - Expected: light_result.pixel_data.len() equals `PIXEL_COUNT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dark_html = generate_glass_test_html("glass_dark")
val light_html = generate_glass_test_html("glass_light")
var renderer_d = BrowserRenderer.create(W, H)
var renderer_l = BrowserRenderer.create(W, H)
val dark_result = renderer_d.render_html_to_pixels(dark_html)
val light_result = renderer_l.render_html_to_pixels(light_html)
expect(dark_result.pixel_data.len()).to_equal(PIXEL_COUNT)
expect(light_result.pixel_data.len()).to_equal(PIXEL_COUNT)
# They should NOT be identical — different backgrounds and colors
val cmp = compare_pixel_buffers(
    dark_result.pixel_data, light_result.pixel_data, W, H, 0)
# Match should be below 50% (very different themes)
expect(cmp.match_percentage).to_be_less_than(5000)
```

</details>

#### rendering stress test

<details>
<summary>Advanced: stress test renders without crash</summary>

#### stress test renders without crash

1. var renderer = BrowserRenderer create
   - Expected: result.pixel_data.len() equals `PIXEL_COUNT`
   - Expected: result.format equals `pixels`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = build_rendering_stress_html()
expect(html.len()).to_be_greater_than(100)
var renderer = BrowserRenderer.create(W, H)
val result = renderer.render_html_to_pixels(html)
expect(result.pixel_data.len()).to_equal(PIXEL_COUNT)
expect(result.format).to_equal("pixels")
```

</details>


</details>

<details>
<summary>Advanced: stress test produces varied pixels</summary>

#### stress test produces varied pixels

1. var renderer = BrowserRenderer create
   - Expected: result.pixel_data.len() equals `PIXEL_COUNT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = build_rendering_stress_html()
var renderer = BrowserRenderer.create(W, H)
val result = renderer.render_html_to_pixels(html)
expect(result.pixel_data.len()).to_equal(PIXEL_COUNT)
# Should have multiple distinct colors (gradients, overlapping alpha, etc.)
val unique = count_unique_colors(result.pixel_data, 50)
# Stress test has gradients/alpha/text — should have many colors
expect(unique).to_be_greater_than(3)
```

</details>


</details>

#### float vs int effect engine rendering

#### both engines produce non-empty output for glass_dark

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = generate_glass_test_html("glass_dark")
val int_cap = capture_with_effect_engine(html, W, H, "int")
val float_cap = capture_with_effect_engine(html, W, H, "float")
expect(int_cap.success).to_equal(true)
expect(float_cap.success).to_equal(true)
expect(int_cap.pixels.len()).to_equal(PIXEL_COUNT)
expect(float_cap.pixels.len()).to_equal(PIXEL_COUNT)
```

</details>

#### float and int engines produce similar output

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = generate_glass_test_html("glass_dark")
val int_cap = capture_with_effect_engine(html, W, H, "int")
val float_cap = capture_with_effect_engine(html, W, H, "float")
expect(int_cap.success).to_equal(true)
expect(float_cap.success).to_equal(true)
# Compare with per-channel threshold of 3
val result = compare_pixel_buffers(
    int_cap.pixels, float_cap.pixels, W, H, 3)
# match_percentage is 0-10000 (100.00% * 100)
# 99.50% = 9950
expect(result.match_percentage).to_be_greater_than(9949)
```

</details>

#### deterministic rendering

#### same HTML renders identically twice

1. var renderer1 = BrowserRenderer create
2. var renderer2 = BrowserRenderer create
   - Expected: result1.pixel_data.len() equals `PIXEL_COUNT`
   - Expected: result2.pixel_data.len() equals `PIXEL_COUNT`
   - Expected: cmp.match_percentage equals `10000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = generate_glass_test_html("glass_dark")
var renderer1 = BrowserRenderer.create(W, H)
var renderer2 = BrowserRenderer.create(W, H)
val result1 = renderer1.render_html_to_pixels(html)
val result2 = renderer2.render_html_to_pixels(html)
expect(result1.pixel_data.len()).to_equal(PIXEL_COUNT)
expect(result2.pixel_data.len()).to_equal(PIXEL_COUNT)
# Exact match — deterministic software rendering
val cmp = compare_exact(result1.pixel_data, result2.pixel_data, W, H)
expect(cmp.match_percentage).to_equal(10000)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/glass_render_e2e_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Glass Theme End-to-End Rendering

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
