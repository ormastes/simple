# Browser Renderer Has Bisect Specification

> <details>

<!-- sdn-diagram:id=browser_renderer_has_bisect_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_renderer_has_bisect_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_renderer_has_bisect_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_renderer_has_bisect_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Renderer Has Bisect Specification

## Scenarios

### has direct child bisect

#### has-direct: applies when badge is direct child

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

#### has-direct: rejects when badge is nested deeper

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

#### has-descendant: applies when badge is anywhere inside

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

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_has_bisect_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- has direct child bisect

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
