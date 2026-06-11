# Webgpu Backend3d Specification

> <details>

<!-- sdn-diagram:id=webgpu_backend3d_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=webgpu_backend3d_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

webgpu_backend3d_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=webgpu_backend3d_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 38 | 38 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Webgpu Backend3d Specification

## Scenarios

### Stream C: WebGpuCommand3D kind-tag construction

### BeginRenderPass

#### AC-6: kind is BeginRenderPass

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = make_wgpu_begin_render_pass_cmd()
val matches = cmd.kind == WebGpuCommand3DKind.BeginRenderPass
expect(matches).to_equal(true)
```

</details>

#### AC-6: stores color_tex_id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = make_wgpu_begin_render_pass_cmd()
expect(cmd.color_tex_id).to_equal(10)
```

</details>

#### AC-6: stores depth_tex_id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = make_wgpu_begin_render_pass_cmd()
expect(cmd.depth_tex_id).to_equal(20)
```

</details>

### SetPipeline

#### AC-6: kind is SetPipeline

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = make_wgpu_set_pipeline_cmd()
val matches = cmd.kind == WebGpuCommand3DKind.SetPipeline
expect(matches).to_equal(true)
```

</details>

#### AC-6: stores pipeline_id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = make_wgpu_set_pipeline_cmd()
expect(cmd.pipeline_id).to_equal(5)
```

</details>

### BindVertexBuffer

#### AC-6: kind is BindVertexBuffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = make_wgpu_bind_vertex_buffer_cmd()
val matches = cmd.kind == WebGpuCommand3DKind.BindVertexBuffer
expect(matches).to_equal(true)
```

</details>

#### AC-6: stores buffer_id and slot

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = make_wgpu_bind_vertex_buffer_cmd()
val ok = cmd.buffer_id == 1 and cmd.slot == 0
expect(ok).to_equal(true)
```

</details>

### BindIndexBuffer

#### AC-6: kind is BindIndexBuffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = make_wgpu_bind_index_buffer_cmd()
val matches = cmd.kind == WebGpuCommand3DKind.BindIndexBuffer
expect(matches).to_equal(true)
```

</details>

#### AC-6: stores buffer_id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = make_wgpu_bind_index_buffer_cmd()
expect(cmd.buffer_id).to_equal(2)
```

</details>

### BindTexture

#### AC-6: kind is BindTexture

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = make_wgpu_bind_texture_cmd()
val matches = cmd.kind == WebGpuCommand3DKind.BindTexture
expect(matches).to_equal(true)
```

</details>

#### AC-6: stores texture_id and slot

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = make_wgpu_bind_texture_cmd()
val ok = cmd.texture_id == 3 and cmd.slot == 0
expect(ok).to_equal(true)
```

</details>

### BindUniformBuffer

#### AC-6: kind is BindUniformBuffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = make_wgpu_bind_uniform_buffer_cmd()
val matches = cmd.kind == WebGpuCommand3DKind.BindUniformBuffer
expect(matches).to_equal(true)
```

</details>

#### AC-6: stores buffer_id and slot

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = make_wgpu_bind_uniform_buffer_cmd()
val ok = cmd.buffer_id == 4 and cmd.slot == 0
expect(ok).to_equal(true)
```

</details>

### DrawIndexed

#### AC-6: kind is DrawIndexed

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = make_wgpu_draw_indexed_cmd()
val matches = cmd.kind == WebGpuCommand3DKind.DrawIndexed
expect(matches).to_equal(true)
```

</details>

#### AC-6: stores index_count and base_vertex

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = make_wgpu_draw_indexed_cmd()
val ok = cmd.index_count == 36 and cmd.base_vertex == 0
expect(ok).to_equal(true)
```

</details>

### EndRenderPass

#### AC-6: kind is EndRenderPass

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = make_wgpu_end_render_pass_cmd()
val matches = cmd.kind == WebGpuCommand3DKind.EndRenderPass
expect(matches).to_equal(true)
```

</details>

### Stream C: WebGpuRenderBackend3D command recording

### capabilities

#### AC-1: backend kind is WebGpu

1. var backend = WebGpuRenderBackend3D create
   - Expected: is_webgpu is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = WebGpuRenderBackend3D.create()
val cap = backend.capabilities()
val is_webgpu = cap.backend == RenderBackendKind3D.WebGpu
expect(is_webgpu).to_equal(true)
```

</details>

#### AC-6: supports_wgsl is true for WebGpu

1. var backend = WebGpuRenderBackend3D create
   - Expected: cap.supports_wgsl is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = WebGpuRenderBackend3D.create()
val cap = backend.capabilities()
expect(cap.supports_wgsl).to_equal(true)
```

</details>

### create_vertex_buffer

#### AC-6: returns non-invalid handle

1. var backend = WebGpuRenderBackend3D create


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = WebGpuRenderBackend3D.create()
val buf = backend.create_vertex_buffer(256)
expect(buf.id).to_be_greater_than(-1)
```

</details>

### create_index_buffer

#### AC-6: returns non-invalid handle

1. var backend = WebGpuRenderBackend3D create


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = WebGpuRenderBackend3D.create()
val buf = backend.create_index_buffer(64)
expect(buf.id).to_be_greater_than(-1)
```

</details>

### create_uniform_buffer

#### AC-6: returns non-invalid handle

1. var backend = WebGpuRenderBackend3D create


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = WebGpuRenderBackend3D.create()
val buf = backend.create_uniform_buffer(64)
expect(buf.id).to_be_greater_than(-1)
```

</details>

### create_texture

#### AC-6: returns non-invalid TextureHandle

1. var backend = WebGpuRenderBackend3D create


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = WebGpuRenderBackend3D.create()
val tex = backend.create_texture(128, 128, TextureFormat3D.Rgba8Unorm)
expect(tex.id).to_be_greater_than(-1)
```

</details>

### create_pipeline

#### AC-6: returns non-invalid PipelineHandle for WGSL desc

1. var backend = WebGpuRenderBackend3D create


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = WebGpuRenderBackend3D.create()
val desc = make_wgpu_pipeline_desc()
val pip = backend.create_pipeline(desc)
expect(pip.id).to_be_greater_than(-1)
```

</details>

### frame + render pass recording sequence

#### AC-6: begin_frame does not crash

1. var backend = WebGpuRenderBackend3D create
2. backend begin frame
   - Expected: backend.cmds.len() equals `0`
   - Expected: backend.active_pass_ids.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = WebGpuRenderBackend3D.create()
backend.begin_frame()
expect(backend.cmds.len()).to_equal(0)
expect(backend.active_pass_ids.len()).to_equal(0)
```

</details>

#### AC-6: begin_render_pass returns non-invalid RenderPassHandle

1. var backend = WebGpuRenderBackend3D create
2. backend begin frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = WebGpuRenderBackend3D.create()
backend.begin_frame()
val color_tex = backend.create_texture(320, 240, TextureFormat3D.Rgba8Unorm)
val depth_tex = backend.create_texture(320, 240, TextureFormat3D.Depth32Float)
val rph = backend.begin_render_pass(color_tex, depth_tex)
expect(rph.id).to_be_greater_than(-1)
```

</details>

#### AC-6: full recording sequence does not crash

1. var backend = WebGpuRenderBackend3D create
2. backend begin frame
3. backend set pipeline
4. backend bind vertex buffer
5. backend bind index buffer
6. backend draw indexed
7. backend end render pass
8. backend end frame
   - Expected: backend.cmds.len() equals `0`
   - Expected: backend.active_pass_ids.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = WebGpuRenderBackend3D.create()
backend.begin_frame()
val color_tex = backend.create_texture(320, 240, TextureFormat3D.Rgba8Unorm)
val depth_tex = backend.create_texture(320, 240, TextureFormat3D.Depth32Float)
val rph = backend.begin_render_pass(color_tex, depth_tex)
val desc = make_wgpu_pipeline_desc()
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
expect(backend.active_pass_ids.len()).to_equal(0)
```

</details>

#### AC-6: full recording sequence records commands before end_frame

1. var backend = WebGpuRenderBackend3D create
2. backend begin frame
3. backend set pipeline
4. backend bind vertex buffer
5. backend bind index buffer
6. backend draw indexed
7. backend end render pass
   - Expected: backend.cmds.len() equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = WebGpuRenderBackend3D.create()
backend.begin_frame()
val color_tex = backend.create_texture(320, 240, TextureFormat3D.Rgba8Unorm)
val depth_tex = backend.create_texture(320, 240, TextureFormat3D.Depth32Float)
val rph = backend.begin_render_pass(color_tex, depth_tex)
val desc = make_wgpu_pipeline_desc()
val pip = backend.create_pipeline(desc)
val vbuf = backend.create_vertex_buffer(128)
val ibuf = backend.create_index_buffer(48)
backend.set_pipeline(rph, pip)
backend.bind_vertex_buffer(rph, vbuf, 0)
backend.bind_index_buffer(rph, ibuf)
backend.draw_indexed(rph, 12, 0)
backend.end_render_pass(rph)
expect(backend.cmds.len()).to_equal(6)
```

</details>

### recording validation

#### AC-10: invalid color attachment rejects begin_render_pass

1. var backend = WebGpuRenderBackend3D create
2. backend begin frame
   - Expected: rejected is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = WebGpuRenderBackend3D.create()
backend.begin_frame()
val depth_tex = backend.create_texture(320, 240, TextureFormat3D.Depth32Float)
val rph = backend.begin_render_pass(TextureHandle.invalid(), depth_tex)
val rejected = rph.id == -1 and backend.cmds.len() == 0
expect(rejected).to_equal(true)
```

</details>

#### AC-10: invalid depth attachment rejects begin_render_pass

1. var backend = WebGpuRenderBackend3D create
2. backend begin frame
   - Expected: rejected is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = WebGpuRenderBackend3D.create()
backend.begin_frame()
val color_tex = backend.create_texture(320, 240, TextureFormat3D.Rgba8Unorm)
val rph = backend.begin_render_pass(color_tex, TextureHandle.invalid())
val rejected = rph.id == -1 and backend.cmds.len() == 0
expect(rejected).to_equal(true)
```

</details>

#### AC-10: nested render pass is rejected

1. var backend = WebGpuRenderBackend3D create
2. backend begin frame
   - Expected: rejected is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = WebGpuRenderBackend3D.create()
backend.begin_frame()
val color_tex = backend.create_texture(320, 240, TextureFormat3D.Rgba8Unorm)
val depth_tex = backend.create_texture(320, 240, TextureFormat3D.Depth32Float)
val first = backend.begin_render_pass(color_tex, depth_tex)
val second = backend.begin_render_pass(color_tex, depth_tex)
val rejected = first.id >= 0 and second.id == -1 and backend.cmds.len() == 1
expect(rejected).to_equal(true)
```

</details>

#### AC-10: invalid pass handle rejects set_pipeline

1. var backend = WebGpuRenderBackend3D create
2. backend set pipeline
   - Expected: backend.cmds.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = WebGpuRenderBackend3D.create()
val pip = backend.create_pipeline(make_wgpu_pipeline_desc())
backend.set_pipeline(RenderPassHandle.invalid(), pip)
expect(backend.cmds.len()).to_equal(0)
```

</details>

#### AC-10: invalid pipeline handle is not recorded

1. var backend = WebGpuRenderBackend3D create
2. backend begin frame
3. backend set pipeline
   - Expected: backend.cmds.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = WebGpuRenderBackend3D.create()
backend.begin_frame()
val color_tex = backend.create_texture(320, 240, TextureFormat3D.Rgba8Unorm)
val depth_tex = backend.create_texture(320, 240, TextureFormat3D.Depth32Float)
val rph = backend.begin_render_pass(color_tex, depth_tex)
backend.set_pipeline(rph, PipelineHandle.invalid())
expect(backend.cmds.len()).to_equal(1)
```

</details>

#### AC-10: invalid vertex buffer handle is not recorded

1. var backend = WebGpuRenderBackend3D create
2. backend begin frame
3. backend bind vertex buffer
   - Expected: backend.cmds.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = WebGpuRenderBackend3D.create()
backend.begin_frame()
val color_tex = backend.create_texture(320, 240, TextureFormat3D.Rgba8Unorm)
val depth_tex = backend.create_texture(320, 240, TextureFormat3D.Depth32Float)
val rph = backend.begin_render_pass(color_tex, depth_tex)
backend.bind_vertex_buffer(rph, BufferHandle.invalid(), 0)
expect(backend.cmds.len()).to_equal(1)
```

</details>

#### AC-10: invalid index buffer handle is not recorded

1. var backend = WebGpuRenderBackend3D create
2. backend begin frame
3. backend bind index buffer
   - Expected: backend.cmds.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = WebGpuRenderBackend3D.create()
backend.begin_frame()
val color_tex = backend.create_texture(320, 240, TextureFormat3D.Rgba8Unorm)
val depth_tex = backend.create_texture(320, 240, TextureFormat3D.Depth32Float)
val rph = backend.begin_render_pass(color_tex, depth_tex)
backend.bind_index_buffer(rph, BufferHandle.invalid())
expect(backend.cmds.len()).to_equal(1)
```

</details>

#### AC-10: invalid texture handle is not recorded

1. var backend = WebGpuRenderBackend3D create
2. backend begin frame
3. backend bind texture
   - Expected: backend.cmds.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = WebGpuRenderBackend3D.create()
backend.begin_frame()
val color_tex = backend.create_texture(320, 240, TextureFormat3D.Rgba8Unorm)
val depth_tex = backend.create_texture(320, 240, TextureFormat3D.Depth32Float)
val rph = backend.begin_render_pass(color_tex, depth_tex)
backend.bind_texture(rph, TextureHandle.invalid(), 0)
expect(backend.cmds.len()).to_equal(1)
```

</details>

#### AC-10: negative slots are not recorded

1. var backend = WebGpuRenderBackend3D create
2. backend begin frame
3. backend bind vertex buffer
4. backend bind texture
5. backend bind uniform buffer
   - Expected: backend.cmds.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = WebGpuRenderBackend3D.create()
backend.begin_frame()
val color_tex = backend.create_texture(320, 240, TextureFormat3D.Rgba8Unorm)
val depth_tex = backend.create_texture(320, 240, TextureFormat3D.Depth32Float)
val rph = backend.begin_render_pass(color_tex, depth_tex)
val vbuf = backend.create_vertex_buffer(128)
val ubuf = backend.create_uniform_buffer(64)
backend.bind_vertex_buffer(rph, vbuf, -1)
backend.bind_texture(rph, color_tex, -1)
backend.bind_uniform_buffer(rph, ubuf, -1)
expect(backend.cmds.len()).to_equal(1)
```

</details>

#### AC-10: non-positive draw counts are not recorded

1. var backend = WebGpuRenderBackend3D create
2. backend begin frame
3. backend draw indexed
4. backend draw indexed
   - Expected: backend.cmds.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = WebGpuRenderBackend3D.create()
backend.begin_frame()
val color_tex = backend.create_texture(320, 240, TextureFormat3D.Rgba8Unorm)
val depth_tex = backend.create_texture(320, 240, TextureFormat3D.Depth32Float)
val rph = backend.begin_render_pass(color_tex, depth_tex)
backend.draw_indexed(rph, 0, 0)
backend.draw_indexed(rph, -1, 0)
expect(backend.cmds.len()).to_equal(1)
```

</details>

#### AC-10: pass-scoped commands after end_render_pass are rejected

1. var backend = WebGpuRenderBackend3D create
2. backend begin frame
3. backend end render pass
4. backend set pipeline
   - Expected: backend.cmds.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = WebGpuRenderBackend3D.create()
backend.begin_frame()
val color_tex = backend.create_texture(320, 240, TextureFormat3D.Rgba8Unorm)
val depth_tex = backend.create_texture(320, 240, TextureFormat3D.Depth32Float)
val rph = backend.begin_render_pass(color_tex, depth_tex)
val pip = backend.create_pipeline(make_wgpu_pipeline_desc())
backend.end_render_pass(rph)
backend.set_pipeline(rph, pip)
expect(backend.cmds.len()).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/engine/render/webgpu_backend3d_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Stream C: WebGpuCommand3D kind-tag construction
- BeginRenderPass
- SetPipeline
- BindVertexBuffer
- BindIndexBuffer
- BindTexture
- BindUniformBuffer
- DrawIndexed
- EndRenderPass
- Stream C: WebGpuRenderBackend3D command recording
- capabilities
- create_vertex_buffer
- create_index_buffer
- create_uniform_buffer
- create_texture
- create_pipeline
- frame + render pass recording sequence
- recording validation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 38 |
| Active scenarios | 38 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
