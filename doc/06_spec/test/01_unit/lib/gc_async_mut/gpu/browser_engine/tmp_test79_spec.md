# Tmp Test79 Specification

> <details>

<!-- sdn-diagram:id=tmp_test79_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tmp_test79_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tmp_test79_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tmp_test79_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tmp Test79 Specification

## Scenarios

### BrowserRenderer HTML rendering

#### renders CSS background fixture pixels through BrowserRenderer

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = render_html_to_pixels_with_viewport(_html_compat_fixture("15_background"), 40, 70).pixel_data
expect(pixels.len()).to_equal(40 * 70)
expect(pixels[0]).to_equal(0xFFF0F0F8u32)
expect(pixels[8 + 8 * 40]).to_equal(0xFFD0D8E8u32)
expect(pixels[27 + 61 * 40]).to_equal(0xFFBFDBFEu32)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_test79_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BrowserRenderer HTML rendering

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
