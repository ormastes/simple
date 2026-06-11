# Tmp Test76 Specification

> <details>

<!-- sdn-diagram:id=tmp_test76_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tmp_test76_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tmp_test76_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tmp_test76_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tmp Test76 Specification

## Scenarios

### BrowserRenderer HTML rendering

#### renders famous-site corpus block at Chrome default body margin

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><div style='width: 120px; height: 40px; background-color: #2563eb'>Google search deterministic compatibility fixture</div></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, 160, 120).pixel_data
expect(pixels.len()).to_equal(160 * 120)
expect(pixels[0]).to_equal(0xFFFFFFFFu32)
expect(pixels[7 + 7 * 160]).to_equal(0xFFFFFFFFu32)
expect(pixels[8 + 8 * 160]).to_equal(0xFF2563EBu32)
expect(pixels[127 + 47 * 160]).to_equal(0xFF2563EBu32)
expect(pixels[128 + 48 * 160]).to_equal(0xFFFFFFFFu32)
expect(_count_region_changed(pixels, 160, 20, 19, 92, 18, 0xFF2563EBu32)).to_be_greater_than(0)
expect(_count_region_changed(pixels, 160, 8, 48, 120, 36, 0xFFFFFFFFu32)).to_be_greater_than(0)
expect(_count_region_changed(pixels, 160, 128, 8, 32, 40, 0xFFFFFFFFu32)).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_test76_spec.spl` |
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
