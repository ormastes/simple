# Vulkan Backend3d Specification

> <details>

<!-- sdn-diagram:id=vulkan_backend3d_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vulkan_backend3d_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vulkan_backend3d_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vulkan_backend3d_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vulkan Backend3d Specification

## Scenarios

### Stream B: VulkanCommand3D kind-tag construction

### BeginRenderPass

#### AC-1: kind is BeginRenderPass

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = make_begin_render_pass_cmd()
val matches = cmd.kind == VulkanCommand3DKind.BeginRenderPass
expect(matches).to_equal(true)
```

</details>

#### AC-1: stores color_image

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = make_begin_render_pass_cmd()
expect(cmd.color_image).to_equal(10)
```

</details>

#### AC-1: stores depth_image

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = make_begin_render_pass_cmd()
expect(cmd.depth_image).to_equal(20)
```

</details>

### SetPipeline

#### AC-1: kind is SetPipeline

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = make_set_pipeline_cmd()
val matches = cmd.kind == VulkanCommand3DKind.SetPipeline
expect(matches).to_equal(true)
```

</details>

#### AC-1: stores pipeline_id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = make_set_pipeline_cmd()
expect(cmd.pipeline_id).to_equal(5)
```

</details>

### BindVertexBuffer

#### AC-1: kind is BindVertexBuffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = make_bind_vertex_buffer_cmd()
val matches = cmd.kind == VulkanCommand3DKind.BindVertexBuffer
expect(matches).to_equal(true)
```

</details>

#### AC-1: stores buffer_id and slot

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = make_bind_vertex_buffer_cmd()
val ok = cmd.buffer_id == 1 and cmd.slot == 0
expect(ok).to_equal(true)
```

</details>

### BindIndexBuffer

#### AC-1: kind is BindIndexBuffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = make_bind_index_buffer_cmd()
val matches = cmd.kind == VulkanCommand3DKind.BindIndexBuffer
expect(matches).to_equal(true)
```

</details>

#### AC-1: stores buffer_id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = make_bind_index_buffer_cmd()
expect(cmd.buffer_id).to_equal(2)
```

</details>

### BindTexture

#### AC-1: kind is BindTexture

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = make_bind_texture_cmd()
val matches = cmd.kind == VulkanCommand3DKind.BindTexture
expect(matches).to_equal(true)
```

</details>

#### AC-1: stores image_id and slot

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = make_bind_texture_cmd()
val ok = cmd.image_id == 3 and cmd.slot == 0
expect(ok).to_equal(true)
```

</details>

### BindUniformBuffer

#### AC-1: kind is BindUniformBuffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = make_bind_uniform_buffer_cmd()
val matches = cmd.kind == VulkanCommand3DKind.BindUniformBuffer
expect(matches).to_equal(true)
```

</details>

#### AC-1: stores buffer_id and slot

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = make_bind_uniform_buffer_cmd()
val ok = cmd.buffer_id == 4 and cmd.slot == 0
expect(ok).to_equal(true)
```

</details>

### DrawIndexed

#### AC-1: kind is DrawIndexed

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = make_draw_indexed_cmd()
val matches = cmd.kind == VulkanCommand3DKind.DrawIndexed
expect(matches).to_equal(true)
```

</details>

#### AC-1: stores index_count and base_vertex

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = make_draw_indexed_cmd()
val ok = cmd.index_count == 36 and cmd.base_vertex == 0
expect(ok).to_equal(true)
```

</details>

### EndRenderPass

#### AC-1: kind is EndRenderPass

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = make_end_render_pass_cmd()
val matches = cmd.kind == VulkanCommand3DKind.EndRenderPass
expect(matches).to_equal(true)
```

</details>

### Stream B: VulkanRenderBackend3D command recording

### capabilities

#### AC-1: backend kind is Vulkan

1. var backend = VulkanRenderBackend3D create
   - Expected: is_vulkan is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = VulkanRenderBackend3D.create()
val cap = backend.capabilities()
val is_vulkan = cap.backend == RenderBackendKind3D.Vulkan
expect(is_vulkan).to_equal(true)
```

</details>

### create_vertex_buffer records command

#### AC-1: create_vertex_buffer returns non-invalid handle

1. var backend = VulkanRenderBackend3D create


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = VulkanRenderBackend3D.create()
val buf = backend.create_vertex_buffer(256)
expect(buf.id).to_be_greater_than(-1)
```

</details>

### create_index_buffer

#### AC-1: create_index_buffer returns non-invalid handle

1. var backend = VulkanRenderBackend3D create


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = VulkanRenderBackend3D.create()
val buf = backend.create_index_buffer(64)
expect(buf.id).to_be_greater_than(-1)
```

</details>

### create_uniform_buffer

#### AC-1: create_uniform_buffer returns non-invalid handle

1. var backend = VulkanRenderBackend3D create


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = VulkanRenderBackend3D.create()
val buf = backend.create_uniform_buffer(64)
expect(buf.id).to_be_greater_than(-1)
```

</details>

### create_texture

#### AC-1: create_texture returns non-invalid TextureHandle

1. var backend = VulkanRenderBackend3D create


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = VulkanRenderBackend3D.create()
val tex = backend.create_texture(128, 128, TextureFormat3D.Rgba8Unorm)
expect(tex.id).to_be_greater_than(-1)
```

</details>

### create_pipeline

#### AC-1: create_pipeline returns non-invalid PipelineHandle

1. var backend = VulkanRenderBackend3D create


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = VulkanRenderBackend3D.create()
val desc = make_pipeline_desc()
val pip = backend.create_pipeline(desc)
expect(pip.id).to_be_greater_than(-1)
```

</details>

### frame + render pass recording sequence

#### AC-1: begin_frame does not crash

1. var backend = VulkanRenderBackend3D create
2. backend begin frame
   - Expected: backend.cmds.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = VulkanRenderBackend3D.create()
backend.begin_frame()
expect(backend.cmds.len()).to_equal(0)
```

</details>

#### AC-1: begin_render_pass returns non-invalid RenderPassHandle

1. var backend = VulkanRenderBackend3D create
2. backend begin frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = VulkanRenderBackend3D.create()
backend.begin_frame()
val color_tex = backend.create_texture(320, 240, TextureFormat3D.Rgba8Unorm)
val depth_tex = backend.create_texture(320, 240, TextureFormat3D.Depth32Float)
val rph = backend.begin_render_pass(color_tex, depth_tex)
expect(rph.id).to_be_greater_than(-1)
```

</details>

#### AC-1: end_render_pass after begin does not crash

1. var backend = VulkanRenderBackend3D create
2. backend begin frame
3. backend end render pass
   - Expected: backend.cmds.len() equals `2`
   - Expected: is_end is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = VulkanRenderBackend3D.create()
backend.begin_frame()
val color_tex = backend.create_texture(320, 240, TextureFormat3D.Rgba8Unorm)
val depth_tex = backend.create_texture(320, 240, TextureFormat3D.Depth32Float)
val rph = backend.begin_render_pass(color_tex, depth_tex)
backend.end_render_pass(rph)
expect(backend.cmds.len()).to_equal(2)
val is_end = backend.cmds[1].kind == VulkanCommand3DKind.EndRenderPass
expect(is_end).to_equal(true)
```

</details>

#### AC-1: end_frame after full sequence does not crash

1. var backend = VulkanRenderBackend3D create
2. backend begin frame
3. backend set pipeline
4. backend bind vertex buffer
5. backend bind index buffer
6. backend draw indexed
7. backend end render pass
8. backend end frame
   - Expected: backend.cmds.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = VulkanRenderBackend3D.create()
backend.begin_frame()
val color_tex = backend.create_texture(320, 240, TextureFormat3D.Rgba8Unorm)
val depth_tex = backend.create_texture(320, 240, TextureFormat3D.Depth32Float)
val rph = backend.begin_render_pass(color_tex, depth_tex)
val desc = make_pipeline_desc()
val pip = backend.create_pipeline(desc)
val vbuf = backend.create_vertex_buffer(128)
val ibuf = backend.create_index_buffer(48)
backend.set_pipeline(rph, pip)
backend.bind_vertex_buffer(rph, vbuf, 0)
backend.bind_index_buffer(rph, ibuf)
backend.draw_indexed(rph, 12, 0)
backend.end_render_pass(rph)
backend.end_frame()
expect(backend.cmds.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/engine/render/vulkan_backend3d_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Stream B: VulkanCommand3D kind-tag construction
- BeginRenderPass
- SetPipeline
- BindVertexBuffer
- BindIndexBuffer
- BindTexture
- BindUniformBuffer
- DrawIndexed
- EndRenderPass
- Stream B: VulkanRenderBackend3D command recording
- capabilities
- create_vertex_buffer records command
- create_index_buffer
- create_uniform_buffer
- create_texture
- create_pipeline
- frame + render pass recording sequence

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
