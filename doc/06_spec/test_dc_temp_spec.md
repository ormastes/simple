# Test Dc Temp Specification

> <details>

<!-- sdn-diagram:id=test_dc_temp_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_dc_temp_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_dc_temp_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_dc_temp_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Dc Temp Specification

## Scenarios

### len

#### test

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='margin:0;background:#ffffff'><div style='display:contents;margin-top:20px;background:#ff0000'><div style='width:40px;height:10px;background:#0000ff'></div></div><div style='width:40px;height:10px;background:#00ff00'></div></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, 40, 40).pixel_data
expect(pixels.len()).to_equal(1600)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/test_dc_temp_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- len

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
