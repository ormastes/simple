# Webgpu Software Executor Specification

> 1. var encoder = WebGPUCommandEncoder create

<!-- sdn-diagram:id=webgpu_software_executor_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=webgpu_software_executor_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

webgpu_software_executor_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=webgpu_software_executor_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Webgpu Software Executor Specification

## Scenarios

### Browser WebGPU software executor

#### replays render command buffers into deterministic counters

1. var encoder = WebGPUCommandEncoder create
   - Expected: encoder.begin_render_pass() is true
   - Expected: encoder.set_pipeline(5) is true
   - Expected: encoder.set_bind_group(0, 9) is true
   - Expected: encoder.set_vertex_buffer(0, 21, 0, 96) is true
   - Expected: encoder.set_index_buffer(22, "uint16", 0, 48) is true
   - Expected: encoder.set_scissor_rect(4, 8, 320, 240) is true
   - Expected: encoder.set_viewport(0, 0, 640, 480, 0.0, 1.0) is true
   - Expected: encoder.set_stencil_reference(7) is true
   - Expected: encoder.set_blend_constant(0.1, 0.2, 0.3, 0.4) is true
   - Expected: encoder.draw(3, 2) is true
   - Expected: encoder.draw_indexed(4, 3, 1, -1, 2) is true
   - Expected: encoder.draw_indirect(11, 0) is true
   - Expected: encoder.end_render_pass() is true
   - Expected: result.valid is true
   - Expected: result.command_count equals `13`
   - Expected: result.render_pass_count equals `1`
   - Expected: result.draw_count equals `3`
   - Expected: result.vertex_count equals `18`
   - Expected: result.compute_pass_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var encoder = WebGPUCommandEncoder.create("frame")
expect(encoder.begin_render_pass()).to_equal(true)
expect(encoder.set_pipeline(5)).to_equal(true)
expect(encoder.set_bind_group(0, 9)).to_equal(true)
expect(encoder.set_vertex_buffer(0, 21, 0, 96)).to_equal(true)
expect(encoder.set_index_buffer(22, "uint16", 0, 48)).to_equal(true)
expect(encoder.set_scissor_rect(4, 8, 320, 240)).to_equal(true)
expect(encoder.set_viewport(0, 0, 640, 480, 0.0, 1.0)).to_equal(true)
expect(encoder.set_stencil_reference(7)).to_equal(true)
expect(encoder.set_blend_constant(0.1, 0.2, 0.3, 0.4)).to_equal(true)
expect(encoder.draw(3, 2)).to_equal(true)
expect(encoder.draw_indexed(4, 3, 1, -1, 2)).to_equal(true)
expect(encoder.draw_indirect(11, 0)).to_equal(true)
expect(encoder.end_render_pass()).to_equal(true)
val command_buffer = encoder.finish("frame")
val result = webgpu_software_execute_command_buffer(command_buffer)
expect(result.valid).to_equal(true)
expect(result.command_count).to_equal(13)
expect(result.render_pass_count).to_equal(1)
expect(result.draw_count).to_equal(3)
expect(result.vertex_count).to_equal(18)
expect(result.compute_pass_count).to_equal(0)
```

</details>

#### replays render pass attachment metadata deterministically

1. var resources = WebGPUResourceTable create
2. var encoder = WebGPUCommandEncoder create
   - Expected: encoder.begin_render_pass_with_descriptor(resources, [GPURenderPassColorAttachment.texture(color.id)], GPURenderPassDepthStencilAttachment.texture(depth.id)) is true
   - Expected: encoder.end_render_pass() is true
   - Expected: result.valid is true
   - Expected: result.render_pass_count equals `1`
   - Expected: result.checksum equals `548`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var resources = WebGPUResourceTable.create()
val color = resources.create_texture("color", 320, 200, 1, GPU_TEXTURE_FORMAT_RGBA8_UNORM, WEBGPU_TEXTURE_USAGE_RENDER_ATTACHMENT)
val depth = resources.create_texture("depth", 320, 200, 1, GPU_TEXTURE_FORMAT_DEPTH24_PLUS, WEBGPU_TEXTURE_USAGE_RENDER_ATTACHMENT)
var encoder = WebGPUCommandEncoder.create("frame")
expect(encoder.begin_render_pass_with_descriptor(resources, [GPURenderPassColorAttachment.texture(color.id)], GPURenderPassDepthStencilAttachment.texture(depth.id))).to_equal(true)
expect(encoder.end_render_pass()).to_equal(true)
val result = webgpu_software_execute_command_buffer(encoder.finish("frame"))
expect(result.valid).to_equal(true)
expect(result.render_pass_count).to_equal(1)
expect(result.checksum).to_equal(548)
```

</details>

#### replays compute dispatch and queue writes

1. var encoder = WebGPUCommandEncoder create
   - Expected: encoder.begin_compute_pass() is true
   - Expected: encoder.set_pipeline(7) is true
   - Expected: encoder.dispatch_workgroups(2, 3, 4) is true
   - Expected: encoder.end_compute_pass() is true
2. var queue = WebGPUQueue create
   - Expected: queue.write_buffer(1, 0, 32) is true
   - Expected: queue.write_texture(2, 4, 4, 1, 64) is true
   - Expected: queue.submit([command_buffer]) is true
   - Expected: result.valid is true
   - Expected: result.queue_write_count equals `2`
   - Expected: result.queue_write_bytes equals `96`
   - Expected: result.buffer_state_count equals `1`
   - Expected: result.texture_state_count equals `1`
   - Expected: result.buffer_checksum equals `33`
   - Expected: result.texture_checksum equals `82`
   - Expected: result.compute_pass_count equals `1`
   - Expected: result.dispatch_count equals `1`
   - Expected: result.dispatched_workgroups equals `24`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var encoder = WebGPUCommandEncoder.create("compute")
expect(encoder.begin_compute_pass()).to_equal(true)
expect(encoder.set_pipeline(7)).to_equal(true)
expect(encoder.dispatch_workgroups(2, 3, 4)).to_equal(true)
expect(encoder.end_compute_pass()).to_equal(true)
val command_buffer = encoder.finish("compute")
var queue = WebGPUQueue.create()
expect(queue.write_buffer(1, 0, 32)).to_equal(true)
expect(queue.write_texture(2, 4, 4, 1, 64)).to_equal(true)
expect(queue.submit([command_buffer])).to_equal(true)
val result = webgpu_software_execute_queue(queue)
expect(result.valid).to_equal(true)
expect(result.queue_write_count).to_equal(2)
expect(result.queue_write_bytes).to_equal(96)
expect(result.buffer_state_count).to_equal(1)
expect(result.texture_state_count).to_equal(1)
expect(result.buffer_checksum).to_equal(33)
expect(result.texture_checksum).to_equal(82)
expect(result.compute_pass_count).to_equal(1)
expect(result.dispatch_count).to_equal(1)
expect(result.dispatched_workgroups).to_equal(24)
```

</details>

#### replays transfer command buffers

1. var encoder = WebGPUCommandEncoder create
   - Expected: encoder.copy_buffer_to_buffer(1, 0, 2, 0, 32) is true
   - Expected: encoder.copy_texture_to_texture(3, 4, 8, 8, 1) is true
   - Expected: result.valid is true
   - Expected: result.buffer_copy_count equals `1`
   - Expected: result.texture_copy_count equals `1`
   - Expected: result.buffer_state_count equals `1`
   - Expected: result.texture_state_count equals `1`
   - Expected: result.buffer_checksum equals `35`
   - Expected: result.texture_checksum equals `71`
   - Expected: result.command_count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var encoder = WebGPUCommandEncoder.create("copy")
expect(encoder.copy_buffer_to_buffer(1, 0, 2, 0, 32)).to_equal(true)
expect(encoder.copy_texture_to_texture(3, 4, 8, 8, 1)).to_equal(true)
val command_buffer = encoder.finish("copy")
val result = webgpu_software_execute_command_buffer(command_buffer)
expect(result.valid).to_equal(true)
expect(result.buffer_copy_count).to_equal(1)
expect(result.texture_copy_count).to_equal(1)
expect(result.buffer_state_count).to_equal(1)
expect(result.texture_state_count).to_equal(1)
expect(result.buffer_checksum).to_equal(35)
expect(result.texture_checksum).to_equal(71)
expect(result.command_count).to_equal(2)
```

</details>

#### copies prior queue-written buffer state deterministically

1. var encoder = WebGPUCommandEncoder create
   - Expected: encoder.copy_buffer_to_buffer(1, 0, 2, 0, 8) is true
2. var queue = WebGPUQueue create
   - Expected: queue.write_buffer(1, 0, 32) is true
   - Expected: queue.submit([command_buffer]) is true
   - Expected: result.valid is true
   - Expected: result.queue_write_count equals `1`
   - Expected: result.buffer_copy_count equals `1`
   - Expected: result.buffer_state_count equals `2`
   - Expected: result.buffer_checksum equals `76`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var encoder = WebGPUCommandEncoder.create("copy-written")
expect(encoder.copy_buffer_to_buffer(1, 0, 2, 0, 8)).to_equal(true)
val command_buffer = encoder.finish("copy-written")
var queue = WebGPUQueue.create()
expect(queue.write_buffer(1, 0, 32)).to_equal(true)
expect(queue.submit([command_buffer])).to_equal(true)
val result = webgpu_software_execute_queue(queue)
expect(result.valid).to_equal(true)
expect(result.queue_write_count).to_equal(1)
expect(result.buffer_copy_count).to_equal(1)
expect(result.buffer_state_count).to_equal(2)
expect(result.buffer_checksum).to_equal(76)
```

</details>

#### rejects invalid command sequencing

1. commands: [webgpu command draw
   - Expected: result.valid is false
   - Expected: result.error equals `WebGPU software executor draw requires an active render pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command_buffer = GPUCommandBufferHandle(
    id: 1,
    label: "bad",
    commands: [webgpu_command_draw(3, 1)],
    valid: true,
    error: ""
)
val result = webgpu_software_execute_command_buffer(command_buffer)
expect(result.valid).to_equal(false)
expect(result.error).to_equal("WebGPU software executor draw requires an active render pass")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/webgpu/webgpu_software_executor_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Browser WebGPU software executor

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
