# Background Gradient Wpt Specification

> <details>

<!-- sdn-diagram:id=background_gradient_wpt_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=background_gradient_wpt_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

background_gradient_wpt_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=background_gradient_wpt_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Background Gradient Wpt Specification

## Scenarios

### WPT-derived background gradient fallback rendering

#### renders vertical two-color linear gradients

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = _render("div { width: 8px; height: 6px; background: linear-gradient(180deg, #dc2626, #2563eb); }", "<div></div>")
expect(_pixel_at(pixels, 1, 0)).to_equal(0xFFDC2626u32)
expect(_pixel_at(pixels, 1, 5)).to_equal(0xFF2563EBu32)
```

</details>

#### renders horizontal two-color linear gradients

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = _render("div { width: 8px; height: 6px; background: linear-gradient(90deg, #dc2626, #2563eb); }", "<div></div>")
expect(_pixel_at(pixels, 0, 1)).to_equal(0xFFDC2626u32)
expect(_pixel_at(pixels, 7, 1)).to_equal(0xFF2563EBu32)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/css/background_gradient_wpt_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- WPT-derived background gradient fallback rendering

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
