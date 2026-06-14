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
| 20 | 20 | 0 | 0 |

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

Runnable source: 12 lines folded for reproduction.
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
expect(engine2d_operation_lane("font_offload")).to_equal(ENGINE2D_BACKEND_LANE_PROCESSING)
expect(engine2d_operation_lane("vector_font")).to_equal(ENGINE2D_BACKEND_LANE_PROCESSING)
expect(engine2d_operation_lane("bitmap_glyph_raster")).to_equal(ENGINE2D_BACKEND_LANE_PROCESSING)
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

#### exposes the shared native first backend order through the lane contract

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val drawing_order = engine2d_backend_lane_drawing_preference_order()
val full_order = engine2d_backend_lane_full_preference_order()

expect(drawing_order[0]).to_equal("metal")
expect(drawing_order[1]).to_equal("cuda")
expect(drawing_order[2]).to_equal("rocm")
expect(drawing_order[4]).to_equal("vulkan")
expect(drawing_order[5]).to_equal("directx")
expect(full_order[0]).to_equal("baremetal")
expect(full_order[1]).to_equal("virtio_gpu")
expect(full_order[2]).to_equal("metal")
expect(engine2d_backend_lane_preference_summary()).to_contain("vulkan > directx > opencl")
```

</details>

#### selects the preferred available candidate without probing per frame

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(engine2d_backend_lane_preferred_candidate(["opencl", "cpu", "directx"], false)).to_equal("directx")
expect(engine2d_backend_lane_preferred_candidate(["vulkan", "cpu", "cuda"], false)).to_equal("cuda")
expect(engine2d_backend_lane_preferred_candidate(["virtio-gpu", "metal"], true)).to_equal("virtio_gpu")
expect(engine2d_backend_lane_preferred_candidate(["amd-hip", "cpu"], false)).to_equal("rocm")
expect(engine2d_backend_lane_preferred_candidate(["unknown"], false)).to_equal("")
```

</details>

#### selects font offload backends with native GPU lanes before Vulkan

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val order = engine2d_font_offload_backend_order()

expect(order[0]).to_equal("metal")
expect(order[1]).to_equal("cuda")
expect(order[2]).to_equal("rocm")
expect(order[4]).to_equal("vulkan")
expect(order[10]).to_equal("cpu_simd")
expect(order[11]).to_equal("software")
expect(engine2d_backend_lane_preferred_font_offload_candidate(["vulkan", "amd-hip", "cpu"])).to_equal("rocm")
expect(engine2d_backend_lane_preferred_font_offload_candidate(["opencl", "cpu_simd", "vulkan"])).to_equal("vulkan")
expect(engine2d_backend_lane_preferred_font_offload_candidate(["software", "cpu-simd", "cpu"])).to_equal("cpu_simd")
expect(engine2d_backend_lane_preferred_font_offload_candidate(["software", "cpu"])).to_equal("software")
expect(engine2d_backend_lane_preferred_font_offload_candidate(["unknown"])).to_equal("")
```

</details>

#### commits host semantic callbacks on the host lane

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = engine2d_host_gpu_lane_schedule(
    ENGINE2D_HOST_GPU_LANE_GPU,
    ENGINE2D_HOST_GPU_LANE_HOST,
    "focus_commit",
    128,
    512,
    true,
    false,
    true,
    7
)

expect(result.ok).to_equal(true)
expect(result.execution_kind).to_equal(ENGINE2D_HOST_GPU_EXEC_PACKET)
expect(result.committed_on_host).to_equal(true)
expect(result.gpu_batched).to_equal(false)
expect(result.estimated_ms).to_equal(7)
expect(engine2d_host_gpu_lane_summary(result)).to_contain("host_commit=true")
```

</details>

#### records faster coarse GPU render batches with explicit packet bounds

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = engine2d_host_gpu_lane_schedule(
    ENGINE2D_HOST_GPU_LANE_HOST,
    ENGINE2D_HOST_GPU_LANE_GPU,
    "draw_ir_delta",
    256,
    4096,
    false,
    false,
    true,
    12
)

expect(result.ok).to_equal(true)
expect(result.execution_kind).to_equal(ENGINE2D_HOST_GPU_EXEC_PACKET)
expect(result.committed_on_host).to_equal(false)
expect(result.gpu_batched).to_equal(true)
expect(result.fallback_explicit).to_equal(false)
expect(result.estimated_ms).to_equal(6)
expect(engine2d_host_gpu_lane_summary(result)).to_contain("estimated_ms=6")
```

</details>

#### keeps same-lane callbacks direct

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = engine2d_host_gpu_lane_schedule(
    ENGINE2D_HOST_GPU_LANE_HOST,
    ENGINE2D_HOST_GPU_LANE_HOST,
    "focus_commit",
    64,
    512,
    true,
    false,
    true,
    5
)

expect(result.ok).to_equal(true)
expect(result.execution_kind).to_equal(ENGINE2D_HOST_GPU_EXEC_DIRECT)
expect(result.committed_on_host).to_equal(true)
```

</details>

#### rejects GPU callbacks that mutate host semantics

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = engine2d_host_gpu_lane_schedule(
    ENGINE2D_HOST_GPU_LANE_HOST,
    ENGINE2D_HOST_GPU_LANE_GPU,
    "draw_ir_delta",
    128,
    512,
    true,
    false,
    true,
    8
)

expect(result.ok).to_equal(false)
expect(result.diagnostic).to_contain("cannot mutate host semantic")
expect(result.estimated_ms).to_equal(8)
```

</details>

#### rejects oversized host GPU lane packets

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = engine2d_host_gpu_lane_schedule(
    ENGINE2D_HOST_GPU_LANE_HOST,
    ENGINE2D_HOST_GPU_LANE_GPU,
    "draw_ir_delta",
    2048,
    512,
    false,
    false,
    true,
    8
)

expect(result.ok).to_equal(false)
expect(result.diagnostic).to_contain("exceeds max_packet")
expect(result.estimated_packet_bytes).to_equal(2048)
expect(result.max_packet_bytes).to_equal(512)
```

</details>

#### rejects per widget GPU dispatch instead of batching

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = engine2d_host_gpu_lane_schedule(
    ENGINE2D_HOST_GPU_LANE_HOST,
    ENGINE2D_HOST_GPU_LANE_GPU,
    "draw_ir_delta",
    128,
    512,
    false,
    true,
    true,
    8
)

expect(result.ok).to_equal(false)
expect(result.diagnostic).to_contain("per-widget GPU dispatch")
```

</details>

#### builds deterministic queue packets for cross-lane lowering

<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val packet = engine2d_host_gpu_queue_packet(
    7,
    ENGINE2D_HOST_GPU_LANE_HOST,
    ENGINE2D_HOST_GPU_LANE_GPU,
    "draw_ir_delta",
    384,
    4096,
    false,
    false,
    true,
    20
)

expect(packet.ok).to_equal(true)
expect(packet.sequence).to_equal(7)
expect(packet.execution_kind).to_equal(ENGINE2D_HOST_GPU_EXEC_PACKET)
expect(packet.payload_bytes).to_equal(384)
expect(packet.max_packet_bytes).to_equal(4096)
expect(packet.payload_checksum).to_equal(7458)
expect(packet.fallback_explicit).to_equal(false)
expect(packet.committed_on_host).to_equal(false)
expect(engine2d_host_gpu_queue_packet_summary(packet)).to_contain("seq=7")
```

</details>

#### rejects queue packets without a positive sequence

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val packet = engine2d_host_gpu_queue_packet(
    0,
    ENGINE2D_HOST_GPU_LANE_HOST,
    ENGINE2D_HOST_GPU_LANE_GPU,
    "draw_ir_delta",
    384,
    4096,
    false,
    false,
    true,
    20
)

expect(packet.ok).to_equal(false)
expect(packet.diagnostic).to_contain("sequence")
```

</details>

#### records ordered queue transport accounting

<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val draw_packet = engine2d_host_gpu_queue_packet(
    1,
    ENGINE2D_HOST_GPU_LANE_HOST,
    ENGINE2D_HOST_GPU_LANE_GPU,
    "draw_ir_delta",
    128,
    4096,
    false,
    false,
    true,
    20
)
val glyph_packet = engine2d_host_gpu_queue_packet(
    2,
    ENGINE2D_HOST_GPU_LANE_HOST,
    ENGINE2D_HOST_GPU_LANE_GPU,
    "glyph_batch",
    256,
    4096,
    false,
    false,
    false,
    20
)
val evidence = engine2d_host_gpu_queue_transport_evidence([draw_packet, glyph_packet])

expect(evidence.ok).to_equal(true)
expect(evidence.packet_count).to_equal(2)
expect(evidence.total_payload_bytes).to_equal(384)
expect(evidence.first_sequence).to_equal(1)
expect(evidence.last_sequence).to_equal(2)
expect(evidence.drained_in_order).to_equal(true)
expect(evidence.fallback_count).to_equal(1)
expect(evidence.host_commit_count).to_equal(0)
expect(evidence.checksum).to_equal(6945)
expect(engine2d_host_gpu_queue_transport_summary(evidence)).to_contain("packets=2")
```

</details>

#### rejects queue transport drained out of sequence order

<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val first = engine2d_host_gpu_queue_packet(
    2,
    ENGINE2D_HOST_GPU_LANE_HOST,
    ENGINE2D_HOST_GPU_LANE_GPU,
    "draw_ir_delta",
    128,
    4096,
    false,
    false,
    true,
    20
)
val second = engine2d_host_gpu_queue_packet(
    1,
    ENGINE2D_HOST_GPU_LANE_HOST,
    ENGINE2D_HOST_GPU_LANE_GPU,
    "glyph_batch",
    256,
    4096,
    false,
    false,
    true,
    20
)
val evidence = engine2d_host_gpu_queue_transport_evidence([first, second])

expect(evidence.ok).to_equal(false)
expect(evidence.drained_in_order).to_equal(false)
expect(evidence.diagnostic).to_contain("sequence")
```

</details>

#### records event flow timings and speedup for strict GPU batches

<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = engine2d_host_gpu_event_flow_evidence(
    ENGINE2D_HOST_GPU_LANE_HOST,
    ENGINE2D_HOST_GPU_LANE_GPU,
    "draw_ir_delta",
    3,
    2,
    384,
    4096,
    false,
    false,
    true,
    4,
    6,
    10,
    20,
    30,
    1113616374,
    true
)

expect(evidence.ok).to_equal(true)
expect(evidence.schedule.execution_kind).to_equal(ENGINE2D_HOST_GPU_EXEC_PACKET)
expect(evidence.schedule.gpu_batched).to_equal(true)
expect(evidence.schedule.fallback_explicit).to_equal(false)
expect(evidence.draw_ir_to_submit_ms).to_equal(3)
expect(evidence.submit_to_present_ms).to_equal(5)
expect(evidence.event_to_present_ms).to_equal(12)
expect(evidence.candidate_frame_p50_ms).to_equal(10)
expect(evidence.candidate_frame_p95_ms).to_equal(15)
expect(evidence.speedup_x1000).to_equal(2000)
expect(engine2d_host_gpu_event_flow_summary(evidence)).to_contain("speedup_x1000=2000")
```

</details>

#### keeps fallback event flow honest without claiming speedup

<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = engine2d_host_gpu_event_flow_evidence(
    ENGINE2D_HOST_GPU_LANE_HOST,
    ENGINE2D_HOST_GPU_LANE_GPU,
    "draw_ir_delta",
    2,
    1,
    256,
    4096,
    false,
    false,
    false,
    4,
    6,
    10,
    20,
    30,
    970686405,
    true
)

expect(evidence.ok).to_equal(true)
expect(evidence.schedule.fallback_explicit).to_equal(true)
expect(evidence.candidate_frame_p50_ms).to_equal(20)
expect(evidence.candidate_frame_p95_ms).to_equal(30)
expect(evidence.speedup_x1000).to_equal(1000)
expect(engine2d_host_gpu_event_flow_summary(evidence)).to_contain("fallback=true")
```

</details>

#### rejects event flow evidence when event order is not preserved

<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = engine2d_host_gpu_event_flow_evidence(
    ENGINE2D_HOST_GPU_LANE_HOST,
    ENGINE2D_HOST_GPU_LANE_GPU,
    "draw_ir_delta",
    2,
    1,
    256,
    4096,
    false,
    false,
    true,
    4,
    6,
    10,
    20,
    30,
    970686405,
    false
)

expect(evidence.ok).to_equal(false)
expect(evidence.diagnostic).to_contain("event order")
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
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
