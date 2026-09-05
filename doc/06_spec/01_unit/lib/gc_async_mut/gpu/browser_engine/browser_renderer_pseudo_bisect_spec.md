# Browser Renderer Pseudo Bisect Specification

> <details>

<!-- sdn-diagram:id=browser_renderer_pseudo_bisect_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_renderer_pseudo_bisect_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_renderer_pseudo_bisect_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_renderer_pseudo_bisect_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Renderer Pseudo Bisect Specification

## Scenarios

### pseudo-selector bisect

#### not: applies when no option matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div:not(.disabled, #archived) { width: 12px; height: 8px; background-color: #0891b2; }</style></head><body><div class='card'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)
expect(_count_color(result.pixel_data, 0xFF0891B2u32)).to_be_greater_than(0)
```

</details>

#### not: rejects when option matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div:not(.card, #archived) { width: 12px; height: 8px; background-color: #0891b2; }</style></head><body><div class='card'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)
expect(_count_color(result.pixel_data, 0xFF0891B2u32)).to_equal(0)
```

</details>

#### has-descendant: applies

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div:has(.badge) { width: 12px; height: 8px; background-color: #7c3aed; }</style></head><body><div><span class='badge'></span></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)
expect(_count_color(result.pixel_data, 0xFF7C3AEDu32)).to_be_greater_than(0)
```

</details>

#### has-direct-child: applies

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div:has(> .badge) { width: 12px; height: 8px; background-color: #0e7490; }</style></head><body><div><span class='badge'></span></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)
expect(_count_color(result.pixel_data, 0xFF0E7490u32)).to_be_greater_than(0)
```

</details>

#### has-direct-child: rejects nested descendant

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div:has(> .badge) { width: 12px; height: 8px; background-color: #0e7490; }</style></head><body><div><section><span class='badge'></span></section></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)
expect(_count_color(result.pixel_data, 0xFF0E7490u32)).to_equal(0)
```

</details>

#### first-child: applies

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div:first-child { width: 12px; height: 8px; background-color: #1d4ed8; }</style></head><body><div></div><div></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)
expect(_count_color(result.pixel_data, 0xFF1D4ED8u32)).to_be_greater_than(0)
```

</details>

#### first-child: rejects later divs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .target:first-child { width: 12px; height: 8px; background-color: #1d4ed8; }</style></head><body><div></div><div class='target'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)
expect(_count_color(result.pixel_data, 0xFF1D4ED8u32)).to_equal(0)
```

</details>

#### last-child: applies

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .target:last-child { width: 12px; height: 8px; background-color: #be123c; }</style></head><body><div></div><div class='target'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)
expect(_count_color(result.pixel_data, 0xFFBE123Cu32)).to_be_greater_than(0)
```

</details>

#### last-child: rejects non-last

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .target:last-child { width: 12px; height: 8px; background-color: #be123c; }</style></head><body><div class='target'></div><div></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)
expect(_count_color(result.pixel_data, 0xFFBE123Cu32)).to_equal(0)
```

</details>

#### only-child: applies

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .target:only-child { width: 12px; height: 8px; background-color: #9333ea; }</style></head><body><div class='target'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)
expect(_count_color(result.pixel_data, 0xFF9333EAu32)).to_be_greater_than(0)
```

</details>

#### only-child: rejects when sibling exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .target:only-child { width: 12px; height: 8px; background-color: #9333ea; }</style></head><body><div class='target'></div><div></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)
expect(_count_color(result.pixel_data, 0xFF9333EAu32)).to_equal(0)
```

</details>

#### nth-child even: applies

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div:nth-child(even) { width: 12px; height: 8px; background-color: #0e7490; }</style></head><body><div></div><div></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)
expect(_count_color(result.pixel_data, 0xFF0E7490u32)).to_be_greater_than(0)
```

</details>

#### nth-child odd: rejects even nodes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } .target:nth-child(odd) { width: 12px; height: 8px; background-color: #0e7490; }</style></head><body><div></div><div class='target'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)
expect(_count_color(result.pixel_data, 0xFF0E7490u32)).to_equal(0)
```

</details>

#### empty: applies

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div:empty { width: 12px; height: 8px; background-color: #0f766e; }</style></head><body><div></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)
expect(_count_color(result.pixel_data, 0xFF0F766Eu32)).to_be_greater_than(0)
```

</details>

#### empty: rejects when has content

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ffffff; } div:empty { width: 12px; height: 8px; background-color: #0f766e; }</style></head><body><div>content</div></body></html>"
val result = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT)
expect(_count_color(result.pixel_data, 0xFF0F766Eu32)).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_pseudo_bisect_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- pseudo-selector bisect

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
