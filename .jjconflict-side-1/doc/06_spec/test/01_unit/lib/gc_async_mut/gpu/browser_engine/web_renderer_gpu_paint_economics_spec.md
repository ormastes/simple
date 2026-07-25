# Web Renderer GPU Paint Economics Specification

> Verifies the Simple Web GPU-paint cost model with deterministic `WebGpuPaintFrame` fixtures. The unit scenarios avoid the full HTML layout renderer so this spec stays a cheap guard for the CPU-work and communication overhead calculations. HTML-backed route coverage lives in the broader `web_gpu_paint_offload_matrix_spec`.

<!-- sdn-diagram:id=web_renderer_gpu_paint_economics_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=web_renderer_gpu_paint_economics_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

web_renderer_gpu_paint_economics_spec -> std
web_renderer_gpu_paint_economics_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=web_renderer_gpu_paint_economics_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Renderer GPU Paint Economics Specification

Verifies the Simple Web GPU-paint cost model with deterministic `WebGpuPaintFrame` fixtures. The unit scenarios avoid the full HTML layout renderer so this spec stays a cheap guard for the CPU-work and communication overhead calculations. HTML-backed route coverage lives in the broader `web_gpu_paint_offload_matrix_spec`.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_renderer_gpu_paint_economics_spec.spl` |
| Updated | 2026-07-08 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies the Simple Web GPU-paint cost model with deterministic
`WebGpuPaintFrame` fixtures. The unit scenarios avoid the full HTML layout
renderer so this spec stays a cheap guard for the CPU-work and communication
overhead calculations. HTML-backed route coverage lives in the broader
`web_gpu_paint_offload_matrix_spec`.

## Examples

The scenarios cover transfer wins, total-work wins, CPU ground-truth frames
that must remain upload-bound, and frames with no GPU fill commands.

## Scenarios

### Simple web renderer GPU paint economics

#### offload decision

#### offloads solid fills when transfer cost beats upload-bound presentation

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = solid_full_frame()
val economics = web_gpu_paint_economics(frame, 0xFFFFFFFFu32)
expect(economics.cpu_paint_pixels).to_equal(0)
expect(economics.fill_op_count).to_be_greater_than(0)
expect(economics.should_offload).to_equal(true)
expect(economics.reason).to_equal("gpu-paint-transfer-win")
expect(economics.gpu_paint_transfer_pixels).to_be_less_than(economics.upload_bound_transfer_pixels)
expect(economics.gpu_paint_total_pixels).to_be_less_than(economics.upload_bound_total_pixels)
```

</details>

#### offloads when skipped CPU paint beats command overhead overall

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = many_tiny_fill_frame(0)
val economics = web_gpu_paint_economics(frame, 0xFFFFFFFFu32)
expect(economics.gpu_paint_transfer_pixels).to_be_greater_than(economics.upload_bound_transfer_pixels)
expect(economics.gpu_paint_total_pixels).to_be_less_than(economics.upload_bound_total_pixels)
expect(economics.should_offload).to_equal(true)
expect(economics.reason).to_equal("gpu-paint-total-win")
```

</details>

#### keeps CPU-ground-truth frames on the upload-bound path

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = cpu_ground_truth_frame()
val economics = web_gpu_paint_economics(frame, 0xFFFFFFFFu32)
expect(economics.cpu_paint_pixels).to_equal(16 * 16)
expect(economics.should_offload).to_equal(false)
expect(economics.reason).to_equal("cpu-ground-truth-required")
```

</details>

#### does not offload when there is no GPU fill work

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = blank_frame()
val economics = web_gpu_paint_economics(frame, 0xFFFFFFFFu32)
expect(economics.cpu_paint_pixels).to_equal(0)
expect(economics.should_offload).to_equal(false)
expect(economics.reason).to_equal("no-gpu-fill-ops")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
