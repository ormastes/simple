# Web Gpu Paint Offload Matrix Specification

> <details>

<!-- sdn-diagram:id=web_gpu_paint_offload_matrix_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=web_gpu_paint_offload_matrix_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

web_gpu_paint_offload_matrix_spec -> std
web_gpu_paint_offload_matrix_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=web_gpu_paint_offload_matrix_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Gpu Paint Offload Matrix Specification

## Scenarios

### Simple Web GPU paint offload matrix

#### CPU paint and communication economics

#### offloads when solid fill paint avoids CPU paint and transfer wins

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = simple_web_layout_render_html_gpu_frame(solid_full_frame_html(), 64, 64)
val economics = web_gpu_paint_economics(frame, 0xFFFFFFFFu32)
expect(economics.cpu_paint_pixels).to_equal(0)
expect(economics.fill_pixels).to_be_greater_than(0)
expect(economics.gpu_paint_transfer_pixels).to_be_less_than(economics.upload_bound_transfer_pixels)
expect(economics.should_offload).to_equal(true)
```

</details>

#### does not claim offload when CPU ground truth is still required

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = simple_web_layout_render_html_gpu_frame(text_and_solid_html(), 64, 64)
val economics = web_gpu_paint_economics(frame, 0xFFFFFFFFu32)
expect(economics.cpu_paint_pixels).to_equal(64 * 64)
expect(economics.should_offload).to_equal(false)
expect(economics.reason).to_equal("cpu-ground-truth-required")
```

</details>

#### rejects command-heavy tiny fills when communication overhead loses

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = simple_web_layout_render_html_gpu_frame(many_tiny_solid_html(), 16, 16)
val economics = web_gpu_paint_economics(frame, 0xFFFFFFFFu32)
expect(economics.cpu_paint_pixels).to_equal(0)
expect(economics.fill_op_count).to_be_greater_than(7)
expect(economics.gpu_paint_transfer_pixels).to_be_greater_than(economics.upload_bound_transfer_pixels)
expect(economics.should_offload).to_equal(false)
expect(economics.reason).to_equal("communication-overhead")
```

</details>

#### does not treat skipped CPU work as offload when there are no fill commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = WebGpuPaintFrame(fb: [0xFFFFFFFFu32; 16 * 16], fill_ops: [], width: 16, height: 16, cpu_paint_pixels: 0)
val economics = web_gpu_paint_economics(frame, 0xFFFFFFFFu32)
expect(economics.cpu_paint_pixels).to_equal(0)
expect(economics.fill_op_count).to_equal(0)
expect(economics.should_offload).to_equal(false)
expect(economics.reason).to_equal("no-gpu-fill-ops")
```

</details>

#### rejects offscreen fill commands that do no clipped GPU work

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = direct_frame(16, 16, 0, 32, 32, 8, 8)
val economics = web_gpu_paint_economics(frame, 0xFFFFFFFFu32)
expect(economics.cpu_paint_pixels).to_equal(0)
expect(economics.fill_op_count).to_equal(1)
expect(economics.fill_pixels).to_equal(0)
expect(economics.should_offload).to_equal(false)
expect(economics.reason).to_equal("no-clipped-fill-pixels")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/05_perf/web_render_chrome/web_gpu_paint_offload_matrix_spec.spl` |
| Updated | 2026-07-08 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Simple Web GPU paint offload matrix

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
