# Tmp Rgb Specification

> <details>

<!-- sdn-diagram:id=tmp_rgb_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tmp_rgb_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tmp_rgb_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tmp_rgb_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tmp Rgb Specification

## Scenarios

### rgb and color fallback tests

#### parses rgb() background-color in the fallback pixel path

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background-color: rgb(37, 99, 235)'></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, 8, 6).pixel_data
expect(pixels.len()).to_equal(8 * 6)
expect(pixels[0]).to_equal(0xFF2563EBu32)
```

</details>

#### parses modern space-separated rgb()

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background-color: rgb(5 150 105)'></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, 8, 6).pixel_data
expect(pixels[0]).to_equal(0xFF059669u32)
```

</details>

#### composites rgba() over white

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background-color: rgba(0, 0, 0, 0.5)'></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, 8, 6).pixel_data
expect(pixels[0]).to_equal(0xFF808080u32)
```

</details>

#### parses shorthand hex background-color

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background-color: #0f8'></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, 8, 6).pixel_data
expect(pixels[0]).to_equal(0xFF00FF88u32)
```

</details>

#### composites shorthand hex alpha over white

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background-color: #0008'></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, 8, 6).pixel_data
expect(pixels[0]).to_equal(0xFF777777u32)
```

</details>

#### parses named CSS background-color

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background-color: rebeccapurple'></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, 8, 6).pixel_data
expect(pixels[0]).to_equal(0xFF663399u32)
```

</details>

#### composites transparent to white

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background-color: transparent'></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, 8, 6).pixel_data
expect(pixels[0]).to_equal(0xFFFFFFFFu32)
```

</details>

#### parses hsl() background-color

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background-color: hsl(120, 100%, 25%)'></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, 8, 6).pixel_data
expect(pixels[0]).to_equal(0xFF008000u32)
```

</details>

#### parses color-first background shorthand

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background: rebeccapurple no-repeat'></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, 8, 6).pixel_data
expect(pixels[0]).to_equal(0xFF663399u32)
```

</details>

#### parses function color background shorthand before trailing tokens

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background: rgb(5, 150, 105) no-repeat'></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, 8, 6).pixel_data
expect(pixels[0]).to_equal(0xFF059669u32)
```

</details>

#### parses fallback color after url()

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background: url(hero.png) #0f8 no-repeat'></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, 8, 6).pixel_data
expect(pixels[0]).to_equal(0xFF00FF88u32)
```

</details>

#### lets later background shorthand override earlier background-color

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background-color: rebeccapurple; background: #0f8'></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, 8, 6).pixel_data
expect(pixels[0]).to_equal(0xFF00FF88u32)
```

</details>

#### lets later background-color override earlier background shorthand

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='background: #0f8; background-color: rebeccapurple'></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, 8, 6).pixel_data
expect(pixels[0]).to_equal(0xFF663399u32)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_rgb_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- rgb and color fallback tests

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
