# WebGPU Queue Write Bounds Spec

> Simple2D, Simple3D, JavaScript, and WASM browser paths all use the same WebGPU queue facade for upload evidence. This spec keeps out-of-range writes from appearing as successful queue activity.

<!-- sdn-diagram:id=webgpu_queue_write_bounds_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=webgpu_queue_write_bounds_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

webgpu_queue_write_bounds_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=webgpu_queue_write_bounds_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# WebGPU Queue Write Bounds Spec

Simple2D, Simple3D, JavaScript, and WASM browser paths all use the same WebGPU queue facade for upload evidence. This spec keeps out-of-range writes from appearing as successful queue activity.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | .spipe/web_rendering_backend_animation_hardening/state.md |
| Design | doc/04_architecture/ui/simple_gui_stack.md |
| Research | N/A |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/webgpu_queue_write_bounds_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Simple2D, Simple3D, JavaScript, and WASM browser paths all use the same WebGPU
queue facade for upload evidence. This spec keeps out-of-range writes from
appearing as successful queue activity.

## Requirements

**Requirements:** N/A

## Plan

**Plan:** .spipe/web_rendering_backend_animation_hardening/state.md

## Design

**Design:** doc/04_architecture/ui/simple_gui_stack.md

## Research

**Research:** N/A

## Syntax

The spec uses `std.spec` scenarios and direct queue/resource assertions.

## Scenarios

### browser WebGPU queue write bounds hardening

#### rejects queue writes that exceed buffer size without stamping write evidence

- var gpu ctx = webgpu create context
   - Expected: gpu_ctx.last_error equals `queue write range exceeds buffer size`
   - Expected: gpu_ctx.queue.write_count equals `0`
   - Expected: gpu_ctx.queue.write_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var gpu_ctx = webgpu_create_context(true)
val requested = gpu_ctx.request_device()
expect(requested).to_be(true)

var resources = gpu_ctx.resources
val buffer = resources.create_buffer("upload", 16, WEBGPU_BUFFER_USAGE_COPY_DST_FOR_SPEC)
gpu_ctx.resources = resources

val overflow_write = gpu_ctx.queue_write_buffer(buffer.id, 8, 12)
expect(overflow_write).to_be(false)
expect(gpu_ctx.last_error).to_equal("queue write range exceeds buffer size")
expect(gpu_ctx.queue.write_count).to_equal(0)

val valid_write = gpu_ctx.queue_write_buffer(buffer.id, 4, 12)
expect(valid_write).to_be(true)
expect(gpu_ctx.queue.write_count).to_equal(1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [.spipe/web_rendering_backend_animation_hardening/state.md](.spipe/web_rendering_backend_animation_hardening/state.md)
- **Design:** [doc/04_architecture/ui/simple_gui_stack.md](doc/04_architecture/ui/simple_gui_stack.md)


</details>
