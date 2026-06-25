# Tmp Rgb Test Specification

> <details>

<!-- sdn-diagram:id=tmp_rgb_test_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tmp_rgb_test_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tmp_rgb_test_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tmp_rgb_test_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tmp Rgb Test Specification

## Scenarios

### rgb body background

#### rgb body background at pixel 0

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

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/tmp_rgb_test_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- rgb body background

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
