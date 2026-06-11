# Tmp Fix Bg Specification

> <details>

<!-- sdn-diagram:id=tmp_fix_bg_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tmp_fix_bg_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tmp_fix_bg_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tmp_fix_bg_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tmp Fix Bg Specification

## Scenarios

### background fixture isolated

#### renders CSS background fixture pixel 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = render_html_to_pixels_with_viewport(_html_compat_fixture("15_background"), 40, 70).pixel_data
expect(pixels[0]).to_equal(0xFFF0F0F8u32)
```

</details>

#### renders CSS background fixture pixel 8_8

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = render_html_to_pixels_with_viewport(_html_compat_fixture("15_background"), 40, 70).pixel_data
expect(pixels[8 + 8 * 40]).to_equal(0xFFD0D8E8u32)
```

</details>

#### renders CSS background fixture pixel 27_61

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = render_html_to_pixels_with_viewport(_html_compat_fixture("15_background"), 40, 70).pixel_data
expect(pixels[27 + 61 * 40]).to_equal(0xFFBFDBFEu32)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_fix_bg_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- background fixture isolated

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
