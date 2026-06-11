# Tmp Compare Specification

> <details>

<!-- sdn-diagram:id=tmp_compare_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tmp_compare_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tmp_compare_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tmp_compare_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tmp Compare Specification

## Scenarios

### compare two renders

#### same html renders equal pixels from two different BrowserRenderer instances

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><div style='width: 12px; height: 8px; background-color: #2563eb'></div></body></html>"
val r1 = BrowserRenderer.create_with_backend(32, 24, "metal")
val r2 = BrowserRenderer.create_with_backend(32, 24, "cpu")
val p1 = r1.render_html_to_pixels(html).pixel_data
val p2 = r2.render_html_to_pixels(html).pixel_data
expect(p1.len()).to_equal(32 * 24)
expect(p2.len()).to_equal(32 * 24)
expect(_pixels_equal(p1, p2)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_compare_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- compare two renders

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
