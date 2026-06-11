# Tmp Test81 Specification

> <details>

<!-- sdn-diagram:id=tmp_test81_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tmp_test81_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tmp_test81_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tmp_test81_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tmp Test81 Specification

## Scenarios

### BrowserRenderer HTML rendering

#### renders CSS padding fixture pixels through BrowserRenderer

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = render_html_to_pixels_with_viewport(_html_compat_fixture("12_padding"), 40, 90).pixel_data
expect(pixels.len()).to_equal(40 * 90)
expect(pixels[16 + 16 * 40]).to_equal(0xFFDBEAFEu32)
expect(pixels[22 + 50 * 40]).to_equal(0xFFBFDBFEu32)
expect(pixels[22 + 78 * 40]).to_equal(0xFF93C5FDu32)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_test81_spec.spl` |
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
