# Tmp Diff Backend Specification

> <details>

<!-- sdn-diagram:id=tmp_diff_backend_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tmp_diff_backend_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tmp_diff_backend_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tmp_diff_backend_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tmp Diff Backend Specification

## Scenarios

### diff backend render

#### metal then cpu pixel counts

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><div style='width: 12px; height: 8px; background-color: #2563eb'></div></body></html>"
val metal = BrowserRenderer.create_with_backend(32, 24, "metal")
val cpu = BrowserRenderer.create_with_backend(32, 24, "cpu")
val mp = metal.render_html_to_pixels(html).pixel_data
val cp = cpu.render_html_to_pixels(html).pixel_data
expect(mp.len()).to_equal(32 * 24)
expect(cp.len()).to_equal(32 * 24)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_diff_backend_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- diff backend render

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
