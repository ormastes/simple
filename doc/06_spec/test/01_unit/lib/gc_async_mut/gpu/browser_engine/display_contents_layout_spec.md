# Display Contents Layout Specification

> <details>

<!-- sdn-diagram:id=display_contents_layout_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=display_contents_layout_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

display_contents_layout_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=display_contents_layout_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Display Contents Layout Specification

## Scenarios

### display contents layout

#### flattens children without painting wrapper box

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='margin:0;background:#ffffff'><div style='display:contents;margin-top:20px;background:#ff0000'><div style='width:40px;height:10px;background:#0000ff'></div></div><div style='width:40px;height:10px;background:#00ff00'></div></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, WIDTH, HEIGHT).pixel_data
expect(pixels.len()).to_equal(WIDTH * HEIGHT)
expect(_count_color(pixels, 0xFFFF0000u32)).to_equal(0)
expect(_count_region_color(pixels, WIDTH, 0, 0, 40, 10, 0xFF0000FFu32)).to_be_greater_than(0)
expect(_count_region_color(pixels, WIDTH, 0, 10, 40, 10, 0xFF00FF00u32)).to_be_greater_than(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/display_contents_layout_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- display contents layout

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
