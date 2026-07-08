# Web Renderer Cpu Simd Paint Specification

> <details>

<!-- sdn-diagram:id=web_renderer_cpu_simd_paint_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=web_renderer_cpu_simd_paint_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

web_renderer_cpu_simd_paint_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=web_renderer_cpu_simd_paint_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Renderer Cpu Simd Paint Specification

## Scenarios

### web renderer CPU SIMD paint

#### keeps explicit gpu paint off the cpu_simd backend

- reset simd hits
   - Expected: readback.pixels.len() equals `1024`
   - Expected: readback.pixels[0] equals `0xFF336699u32`
   - Expected: readback.source equals `cpu_mirror`
   - Expected: hits.fill_hits equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_simd_hits()
val readback = simple_web_layout_render_html_readback_paint(solid_html(), 32, 32, "cpu_simd", true)
val hits = simd_hit_counts()
expect(readback.pixels.len()).to_equal(1024)
expect(readback.pixels[0]).to_equal(0xFF336699u32)
expect(readback.source).to_equal("cpu_mirror")
expect(hits.fill_hits).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_renderer_cpu_simd_paint_spec.spl` |
| Updated | 2026-07-08 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- web renderer CPU SIMD paint

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
