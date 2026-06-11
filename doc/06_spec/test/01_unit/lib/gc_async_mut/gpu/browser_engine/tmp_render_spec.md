# Tmp Render Specification

> <details>

<!-- sdn-diagram:id=tmp_render_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tmp_render_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tmp_render_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tmp_render_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tmp Render Specification

## Scenarios

### render pixel count

#### renders 32x24 pixels for div html

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><div style='width: 12px; height: 8px; background-color: #2563eb'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, 32, 24)
expect(result.pixel_data.len()).to_equal(32 * 24)
```

</details>

#### renders 160x120 pixels for div html

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><div style='width: 12px; height: 8px; background-color: #2563eb'></div></body></html>"
val result = render_html_to_pixels_with_viewport(html, 160, 120)
expect(result.pixel_data.len()).to_equal(160 * 120)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_render_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- render pixel count

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
