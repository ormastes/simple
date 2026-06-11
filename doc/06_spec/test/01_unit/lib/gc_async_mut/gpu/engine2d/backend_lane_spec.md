# Backend Lane Specification

> <details>

<!-- sdn-diagram:id=backend_lane_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=backend_lane_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

backend_lane_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=backend_lane_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Lane Specification

## Scenarios

### Engine2D backend lane split

#### keeps drawing backends responsible for framebuffer visible rendering

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lane = engine2d_drawing_backend_lane("vulkan")

expect(lane.lane).to_equal(ENGINE2D_BACKEND_LANE_DRAWING)
expect(lane.backend_name).to_equal("vulkan")
expect(lane.owns_framebuffer).to_equal(true)
expect(lane.owns_kernel_dispatch).to_equal(false)
expect(lane.requires_readback).to_equal(true)
expect(engine2d_backend_lane_summary(lane)).to_contain("framebuffer=true")
```

</details>

#### keeps processing backends responsible for compute and offload

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lane = engine2d_processing_backend_lane("cuda")

expect(lane.lane).to_equal(ENGINE2D_BACKEND_LANE_PROCESSING)
expect(lane.backend_name).to_equal("cuda")
expect(lane.owns_framebuffer).to_equal(false)
expect(lane.owns_kernel_dispatch).to_equal(true)
expect(lane.requires_readback).to_equal(false)
expect(engine2d_operation_lane("generated_kernel")).to_equal(ENGINE2D_BACKEND_LANE_PROCESSING)
expect(engine2d_operation_lane("filter")).to_equal(ENGINE2D_BACKEND_LANE_PROCESSING)
```

</details>

#### allows an explicit combined backend without hiding the split

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lane = engine2d_combined_backend_lane("metal")

expect(lane.lane).to_equal(ENGINE2D_BACKEND_LANE_COMBINED)
expect(lane.owns_framebuffer).to_equal(true)
expect(lane.owns_kernel_dispatch).to_equal(true)
expect(engine2d_operation_lane("present")).to_equal(ENGINE2D_BACKEND_LANE_DRAWING)
expect(engine2d_operation_lane("layout_compute")).to_equal(ENGINE2D_BACKEND_LANE_PROCESSING)
```

</details>

#### builds a split plan with CPU fallback when processing is not specified

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val split = engine2d_backend_lane_plan("vulkan", "cuda", true, true)
val fallback = engine2d_backend_lane_plan("cpu", "", true, false)

expect(split.drawing_backend.backend_name).to_equal("vulkan")
expect(split.processing_backend.backend_name).to_equal("cuda")
expect(split.processing_required).to_equal(true)
expect(split.shared_device_preferred).to_equal(true)
expect(split.split_required).to_equal(true)
expect(split.fallback_reason).to_equal("")
expect(fallback.drawing_backend.backend_name).to_equal("cpu")
expect(fallback.processing_backend.backend_name).to_equal("cpu")
expect(fallback.split_required).to_equal(false)
expect(fallback.fallback_reason).to_contain("processing backend not specified")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_lane_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Engine2D backend lane split

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
