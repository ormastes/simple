# Host Gpu Event Queue Specification

> <details>

<!-- sdn-diagram:id=host_gpu_event_queue_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=host_gpu_event_queue_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

host_gpu_event_queue_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=host_gpu_event_queue_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Host Gpu Event Queue Specification

## Scenarios

### no-GC host GPU event queue

#### round-trips backend handle and Draw IR payload text through runtime drain

- rt host gpu queue reset
   - Expected: submitted.packet_id equals `1`
   - Expected: drained.drained equals `1`
   - Expected: drained.last_backend_handle equals `7`
   - Expected: drained.last_payload_hash equals `12345`
   - Expected: dispatched.status equals `dispatched`
   - Expected: dispatched.backend_handle equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_host_gpu_queue_reset()
val queue = engine2d_host_gpu_runtime_queue_with_backend_handle("vulkan", 1, 7, true, 4096)
val lane = engine2d_host_gpu_lane_schedule(ENGINE2D_HOST_GPU_LANE_HOST, ENGINE2D_HOST_GPU_LANE_GPU, "draw_ir_delta", 128, 4096, false, false, true, 2)
val event = engine2d_host_gpu_event("evt-1", ENGINE2D_HOST_GPU_LANE_GPU, "draw_ir_delta", 128, 4096, false, false, false, true)
val decision = engine2d_host_gpu_event_handler_decision(event, lane)
val payload = "schema=simple-draw-ir-v2\ncomposition id=evt-1 scene=browser-frame backend=gpu\nbatch id=evt-1 backend=gpu source_kind=gui_ast source_id=evt-1 surface=s component=c commands=1"

val submitted = engine2d_host_gpu_event_submit_to_runtime_payload_text(queue, decision, lane, 12345, payload)
val drained = engine2d_host_gpu_runtime_drain(queue, 1)
val dispatched = engine2d_host_gpu_runtime_dispatch_draw_ir(queue, drained, 12345)

expect(submitted.submitted).to_be(true)
expect(submitted.packet_id).to_equal(1)
expect(drained.drained).to_equal(1)
expect(drained.last_backend_handle).to_equal(7)
expect(drained.last_payload_hash).to_equal(12345)
expect(drained.last_payload_text).to_contain("schema=simple-draw-ir-v2")
expect(dispatched.status).to_equal("dispatched")
expect(dispatched.backend_handle).to_equal(7)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/gpu/engine2d/host_gpu_event_queue_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- no-GC host GPU event queue

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
