# Webgpu Commands Specification

> 1. var encoder = WebGPUCommandEncoder create

<!-- sdn-diagram:id=webgpu_commands_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=webgpu_commands_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

webgpu_commands_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=webgpu_commands_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 31 | 31 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Webgpu Commands Specification

## Scenarios

### Browser WebGPU command encoding

### render pass recording

#### records a render pass and submits a command buffer

1. var encoder = WebGPUCommandEncoder create
   - Expected: encoder.begin_render_pass() is true
   - Expected: encoder.set_pipeline(7) is true
   - Expected: encoder.set_bind_group(0, 4) is true
   - Expected: encoder.draw(3, 1) is true
   - Expected: encoder.draw_indexed(6, 2, 4, -1, 1) is true
   - Expected: encoder.end_render_pass() is true
   - Expected: command_buffer.valid is true
   - Expected: command_buffer.command_count() equals `6`
   - Expected: command_buffer.commands[0].kind equals `WEBGPU_COMMAND_BEGIN_RENDER_PASS`
   - Expected: command_buffer.commands[1].kind equals `WEBGPU_COMMAND_SET_PIPELINE`
   - Expected: command_buffer.commands[2].kind equals `WEBGPU_COMMAND_SET_BIND_GROUP`
   - Expected: command_buffer.commands[2].dynamic_offset_count equals `0`
   - Expected: command_buffer.commands[3].kind equals `WEBGPU_COMMAND_DRAW`
   - Expected: command_buffer.commands[4].kind equals `WEBGPU_COMMAND_DRAW_INDEXED`
   - Expected: command_buffer.commands[4].vertex_count equals `6`
   - Expected: command_buffer.commands[4].instance_count equals `2`
   - Expected: command_buffer.commands[4].offset equals `4`
   - Expected: command_buffer.commands[4].destination_offset equals `-1`
   - Expected: command_buffer.commands[4].dynamic_offset_count equals `1`
   - Expected: command_buffer.commands[5].kind equals `WEBGPU_COMMAND_END_RENDER_PASS`
2. var queue = WebGPUQueue create
   - Expected: queue.submit([command_buffer]) is true
   - Expected: queue.submitted_count() equals `1`
   - Expected: queue.submitted_command_count() equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var encoder = WebGPUCommandEncoder.create("frame")
expect(encoder.begin_render_pass()).to_equal(true)
expect(encoder.set_pipeline(7)).to_equal(true)
expect(encoder.set_bind_group(0, 4)).to_equal(true)
expect(encoder.draw(3, 1)).to_equal(true)
expect(encoder.draw_indexed(6, 2, 4, -1, 1)).to_equal(true)
expect(encoder.end_render_pass()).to_equal(true)
val command_buffer = encoder.finish("frame-commands")
expect(command_buffer.valid).to_equal(true)
expect(command_buffer.command_count()).to_equal(6)
expect(command_buffer.commands[0].kind).to_equal(WEBGPU_COMMAND_BEGIN_RENDER_PASS)
expect(command_buffer.commands[1].kind).to_equal(WEBGPU_COMMAND_SET_PIPELINE)
expect(command_buffer.commands[2].kind).to_equal(WEBGPU_COMMAND_SET_BIND_GROUP)
expect(command_buffer.commands[2].dynamic_offset_count).to_equal(0)
expect(command_buffer.commands[3].kind).to_equal(WEBGPU_COMMAND_DRAW)
expect(command_buffer.commands[4].kind).to_equal(WEBGPU_COMMAND_DRAW_INDEXED)
expect(command_buffer.commands[4].vertex_count).to_equal(6)
expect(command_buffer.commands[4].instance_count).to_equal(2)
expect(command_buffer.commands[4].offset).to_equal(4)
expect(command_buffer.commands[4].destination_offset).to_equal(-1)
expect(command_buffer.commands[4].dynamic_offset_count).to_equal(1)
expect(command_buffer.commands[5].kind).to_equal(WEBGPU_COMMAND_END_RENDER_PASS)

var queue = WebGPUQueue.create()
expect(queue.submit([command_buffer])).to_equal(true)
expect(queue.submitted_count()).to_equal(1)
expect(queue.submitted_command_count()).to_equal(6)
```

</details>

#### rejects draw outside a render pass

1. var encoder = WebGPUCommandEncoder create
   - Expected: encoder.draw(3, 1) is false
   - Expected: encoder.last_error equals `GPURenderPassEncoder draw requires an active render pass`
   - Expected: encoder.draw_indexed(3, 1, 0, 0, 0) is false
   - Expected: encoder.last_error equals `GPURenderPassEncoder drawIndexed requires an active render pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var encoder = WebGPUCommandEncoder.create("frame")
expect(encoder.draw(3, 1)).to_equal(false)
expect(encoder.last_error).to_equal("GPURenderPassEncoder draw requires an active render pass")
expect(encoder.draw_indexed(3, 1, 0, 0, 0)).to_equal(false)
expect(encoder.last_error).to_equal("GPURenderPassEncoder drawIndexed requires an active render pass")
```

</details>

#### rejects invalid indexed draw descriptors

1. var encoder = WebGPUCommandEncoder create
   - Expected: encoder.begin_render_pass() is true
   - Expected: encoder.draw_indexed(0, 1, 0, 0, 0) is false
   - Expected: encoder.last_error equals `GPURenderPassEncoder drawIndexed counts must be positive`
   - Expected: encoder.draw_indexed(3, 1, -1, 0, 0) is false
   - Expected: encoder.last_error equals `GPURenderPassEncoder drawIndexed offsets must be non-negative`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var encoder = WebGPUCommandEncoder.create("frame")
expect(encoder.begin_render_pass()).to_equal(true)
expect(encoder.draw_indexed(0, 1, 0, 0, 0)).to_equal(false)
expect(encoder.last_error).to_equal("GPURenderPassEncoder drawIndexed counts must be positive")
expect(encoder.draw_indexed(3, 1, -1, 0, 0)).to_equal(false)
expect(encoder.last_error).to_equal("GPURenderPassEncoder drawIndexed offsets must be non-negative")
```

</details>

#### records dynamic bind group offsets

1. var encoder = WebGPUCommandEncoder create
   - Expected: encoder.begin_render_pass() is true
   - Expected: encoder.set_bind_group_with_dynamic_offsets(0, 4, [0, 256]) is true
   - Expected: encoder.end_render_pass() is true
   - Expected: command_buffer.valid is true
   - Expected: command_buffer.commands[1].kind equals `WEBGPU_COMMAND_SET_BIND_GROUP`
   - Expected: command_buffer.commands[1].dynamic_offset_count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var encoder = WebGPUCommandEncoder.create("frame")
expect(encoder.begin_render_pass()).to_equal(true)
expect(encoder.set_bind_group_with_dynamic_offsets(0, 4, [0, 256])).to_equal(true)
expect(encoder.end_render_pass()).to_equal(true)
val command_buffer = encoder.finish("frame-commands")
expect(command_buffer.valid).to_equal(true)
expect(command_buffer.commands[1].kind).to_equal(WEBGPU_COMMAND_SET_BIND_GROUP)
expect(command_buffer.commands[1].dynamic_offset_count).to_equal(2)
```

</details>

#### rejects invalid dynamic bind group offsets

1. var encoder = WebGPUCommandEncoder create
   - Expected: encoder.begin_render_pass() is true
   - Expected: encoder.set_bind_group_with_dynamic_offsets(0, 4, [128]) is false
   - Expected: encoder.last_error equals `GPUPassEncoder dynamic offsets must be 256-byte aligned`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var encoder = WebGPUCommandEncoder.create("frame")
expect(encoder.begin_render_pass()).to_equal(true)
expect(encoder.set_bind_group_with_dynamic_offsets(0, 4, [128])).to_equal(false)
expect(encoder.last_error).to_equal("GPUPassEncoder dynamic offsets must be 256-byte aligned")
```

</details>

#### records vertex and index buffer bindings

1. var encoder = WebGPUCommandEncoder create
   - Expected: encoder.begin_render_pass() is true
   - Expected: encoder.set_vertex_buffer(0, 11, 16, 96) is true
   - Expected: encoder.set_index_buffer(12, "uint32", 32, 128) is true
   - Expected: encoder.set_scissor_rect(4, 8, 320, 240) is true
   - Expected: encoder.set_viewport(0, 0, 640, 480, 0.25, 0.75) is true
   - Expected: encoder.set_stencil_reference(7) is true
   - Expected: encoder.set_blend_constant(0.1, 0.2, 0.3, 0.4) is true
   - Expected: encoder.end_render_pass() is true
   - Expected: command_buffer.valid is true
   - Expected: command_buffer.commands[1].kind equals `WEBGPU_COMMAND_SET_VERTEX_BUFFER`
   - Expected: command_buffer.commands[1].slot equals `0`
   - Expected: command_buffer.commands[1].source_buffer_id equals `11`
   - Expected: command_buffer.commands[1].offset equals `16`
   - Expected: command_buffer.commands[1].size equals `96`
   - Expected: command_buffer.commands[2].kind equals `WEBGPU_COMMAND_SET_INDEX_BUFFER`
   - Expected: command_buffer.commands[2].source_buffer_id equals `12`
   - Expected: command_buffer.commands[2].offset equals `32`
   - Expected: command_buffer.commands[2].size equals `128`
   - Expected: command_buffer.commands[2].data_size equals `32`
   - Expected: command_buffer.commands[3].kind equals `WEBGPU_COMMAND_SET_SCISSOR_RECT`
   - Expected: command_buffer.commands[3].offset equals `4`
   - Expected: command_buffer.commands[3].destination_offset equals `8`
   - Expected: command_buffer.commands[3].width equals `320`
   - Expected: command_buffer.commands[3].height equals `240`
   - Expected: command_buffer.commands[4].kind equals `WEBGPU_COMMAND_SET_VIEWPORT`
   - Expected: command_buffer.commands[4].offset equals `0`
   - Expected: command_buffer.commands[4].destination_offset equals `0`
   - Expected: command_buffer.commands[4].width equals `640`
   - Expected: command_buffer.commands[4].height equals `480`
   - Expected: command_buffer.commands[4].viewport_min_depth equals `0.25`
   - Expected: command_buffer.commands[4].viewport_max_depth equals `0.75`
   - Expected: command_buffer.commands[5].kind equals `WEBGPU_COMMAND_SET_STENCIL_REFERENCE`
   - Expected: command_buffer.commands[5].data_size equals `7`
   - Expected: command_buffer.commands[6].kind equals `WEBGPU_COMMAND_SET_BLEND_CONSTANT`
   - Expected: command_buffer.commands[6].blend_constant_red equals `0.1`
   - Expected: command_buffer.commands[6].blend_constant_green equals `0.2`
   - Expected: command_buffer.commands[6].blend_constant_blue equals `0.3`
   - Expected: command_buffer.commands[6].blend_constant_alpha equals `0.4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var encoder = WebGPUCommandEncoder.create("frame")
expect(encoder.begin_render_pass()).to_equal(true)
expect(encoder.set_vertex_buffer(0, 11, 16, 96)).to_equal(true)
expect(encoder.set_index_buffer(12, "uint32", 32, 128)).to_equal(true)
expect(encoder.set_scissor_rect(4, 8, 320, 240)).to_equal(true)
expect(encoder.set_viewport(0, 0, 640, 480, 0.25, 0.75)).to_equal(true)
expect(encoder.set_stencil_reference(7)).to_equal(true)
expect(encoder.set_blend_constant(0.1, 0.2, 0.3, 0.4)).to_equal(true)
expect(encoder.end_render_pass()).to_equal(true)
val command_buffer = encoder.finish("mesh")
expect(command_buffer.valid).to_equal(true)
expect(command_buffer.commands[1].kind).to_equal(WEBGPU_COMMAND_SET_VERTEX_BUFFER)
expect(command_buffer.commands[1].slot).to_equal(0)
expect(command_buffer.commands[1].source_buffer_id).to_equal(11)
expect(command_buffer.commands[1].offset).to_equal(16)
expect(command_buffer.commands[1].size).to_equal(96)
expect(command_buffer.commands[2].kind).to_equal(WEBGPU_COMMAND_SET_INDEX_BUFFER)
expect(command_buffer.commands[2].source_buffer_id).to_equal(12)
expect(command_buffer.commands[2].offset).to_equal(32)
expect(command_buffer.commands[2].size).to_equal(128)
expect(command_buffer.commands[2].data_size).to_equal(32)
expect(command_buffer.commands[3].kind).to_equal(WEBGPU_COMMAND_SET_SCISSOR_RECT)
expect(command_buffer.commands[3].offset).to_equal(4)
expect(command_buffer.commands[3].destination_offset).to_equal(8)
expect(command_buffer.commands[3].width).to_equal(320)
expect(command_buffer.commands[3].height).to_equal(240)
expect(command_buffer.commands[4].kind).to_equal(WEBGPU_COMMAND_SET_VIEWPORT)
expect(command_buffer.commands[4].offset).to_equal(0)
expect(command_buffer.commands[4].destination_offset).to_equal(0)
expect(command_buffer.commands[4].width).to_equal(640)
expect(command_buffer.commands[4].height).to_equal(480)
expect(command_buffer.commands[4].viewport_min_depth).to_equal(0.25)
expect(command_buffer.commands[4].viewport_max_depth).to_equal(0.75)
expect(command_buffer.commands[5].kind).to_equal(WEBGPU_COMMAND_SET_STENCIL_REFERENCE)
expect(command_buffer.commands[5].data_size).to_equal(7)
expect(command_buffer.commands[6].kind).to_equal(WEBGPU_COMMAND_SET_BLEND_CONSTANT)
expect(command_buffer.commands[6].blend_constant_red).to_equal(0.1)
expect(command_buffer.commands[6].blend_constant_green).to_equal(0.2)
expect(command_buffer.commands[6].blend_constant_blue).to_equal(0.3)
expect(command_buffer.commands[6].blend_constant_alpha).to_equal(0.4)
```

</details>

#### validates vertex and index buffer bindings against resources

1. var resources = WebGPUResourceTable create
   - Expected: webgpu_validate_vertex_buffer_binding_with_resources(resources, 0, vertices.id, 16, 128) equals ``
   - Expected: webgpu_validate_index_buffer_binding_with_resources(resources, indices.id, "uint16", 0, 64) equals ``
   - Expected: webgpu_validate_vertex_buffer_binding_with_resources(resources, 0, wrong.id, 0, 16) equals `GPURenderPassEncoder vertex buffer missing VERTEX usage`
   - Expected: webgpu_validate_index_buffer_binding_with_resources(resources, wrong.id, "uint32", 0, 16) equals `GPURenderPassEncoder index buffer missing INDEX usage`
   - Expected: webgpu_validate_vertex_buffer_binding_with_resources(resources, 0, vertices.id, 240, 32) equals `GPURenderPassEncoder vertex buffer binding range exceeds buffer size`
   - Expected: webgpu_validate_index_buffer_binding_with_resources(resources, indices.id, "uint8", 0, 16) equals `GPURenderPassEncoder index buffer format must be uint16 or uint32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var resources = WebGPUResourceTable.create()
val vertices = resources.create_buffer("vertices", 256, WEBGPU_BUFFER_USAGE_VERTEX)
val indices = resources.create_buffer("indices", 128, WEBGPU_BUFFER_USAGE_INDEX)
val wrong = resources.create_buffer("uniforms", 64, WEBGPU_BUFFER_USAGE_UNIFORM)
expect(webgpu_validate_vertex_buffer_binding_with_resources(resources, 0, vertices.id, 16, 128)).to_equal("")
expect(webgpu_validate_index_buffer_binding_with_resources(resources, indices.id, "uint16", 0, 64)).to_equal("")
expect(webgpu_validate_vertex_buffer_binding_with_resources(resources, 0, wrong.id, 0, 16)).to_equal("GPURenderPassEncoder vertex buffer missing VERTEX usage")
expect(webgpu_validate_index_buffer_binding_with_resources(resources, wrong.id, "uint32", 0, 16)).to_equal("GPURenderPassEncoder index buffer missing INDEX usage")
expect(webgpu_validate_vertex_buffer_binding_with_resources(resources, 0, vertices.id, 240, 32)).to_equal("GPURenderPassEncoder vertex buffer binding range exceeds buffer size")
expect(webgpu_validate_index_buffer_binding_with_resources(resources, indices.id, "uint8", 0, 16)).to_equal("GPURenderPassEncoder index buffer format must be uint16 or uint32")
```

</details>

#### rejects invalid vertex and index buffer commands

1. var encoder = WebGPUCommandEncoder create
   - Expected: encoder.set_vertex_buffer(0, 3, 0, -1) is false
   - Expected: encoder.last_error equals `GPURenderPassEncoder setVertexBuffer requires an active render pass`
   - Expected: encoder.begin_render_pass() is true
   - Expected: encoder.set_vertex_buffer(-1, 3, 0, -1) is false
   - Expected: encoder.last_error equals `GPURenderPassEncoder vertex buffer slot must be non-negative`
   - Expected: encoder.set_index_buffer(4, "float32", 0, -1) is false
   - Expected: encoder.last_error equals `GPURenderPassEncoder index buffer format must be uint16 or uint32`
   - Expected: encoder.set_scissor_rect(-1, 0, 32, 32) is false
   - Expected: encoder.last_error equals `GPURenderPassEncoder scissor rect origin must be non-negative`
   - Expected: encoder.set_scissor_rect(0, 0, 0, 32) is false
   - Expected: encoder.last_error equals `GPURenderPassEncoder scissor rect size must be positive`
   - Expected: encoder.set_viewport(-1, 0, 32, 32, 0.0, 1.0) is false
   - Expected: encoder.last_error equals `GPURenderPassEncoder viewport origin must be non-negative`
   - Expected: encoder.set_viewport(0, 0, 0, 32, 0.0, 1.0) is false
   - Expected: encoder.last_error equals `GPURenderPassEncoder viewport size must be positive`
   - Expected: encoder.set_viewport(0, 0, 32, 32, -0.1, 1.0) is false
   - Expected: encoder.last_error equals `GPURenderPassEncoder viewport depth range must be between 0 and 1`
   - Expected: encoder.set_viewport(0, 0, 32, 32, 0.75, 0.25) is false
   - Expected: encoder.last_error equals `GPURenderPassEncoder viewport minDepth must not exceed maxDepth`
   - Expected: encoder.set_stencil_reference(-1) is false
   - Expected: encoder.last_error equals `GPURenderPassEncoder stencil reference must be non-negative`
2. var outside = WebGPUCommandEncoder create
   - Expected: outside.set_blend_constant(0.0, 0.0, 0.0, 1.0) is false
   - Expected: outside.last_error equals `GPURenderPassEncoder setBlendConstant requires an active render pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var encoder = WebGPUCommandEncoder.create("frame")
expect(encoder.set_vertex_buffer(0, 3, 0, -1)).to_equal(false)
expect(encoder.last_error).to_equal("GPURenderPassEncoder setVertexBuffer requires an active render pass")
expect(encoder.begin_render_pass()).to_equal(true)
expect(encoder.set_vertex_buffer(-1, 3, 0, -1)).to_equal(false)
expect(encoder.last_error).to_equal("GPURenderPassEncoder vertex buffer slot must be non-negative")
expect(encoder.set_index_buffer(4, "float32", 0, -1)).to_equal(false)
expect(encoder.last_error).to_equal("GPURenderPassEncoder index buffer format must be uint16 or uint32")
expect(encoder.set_scissor_rect(-1, 0, 32, 32)).to_equal(false)
expect(encoder.last_error).to_equal("GPURenderPassEncoder scissor rect origin must be non-negative")
expect(encoder.set_scissor_rect(0, 0, 0, 32)).to_equal(false)
expect(encoder.last_error).to_equal("GPURenderPassEncoder scissor rect size must be positive")
expect(encoder.set_viewport(-1, 0, 32, 32, 0.0, 1.0)).to_equal(false)
expect(encoder.last_error).to_equal("GPURenderPassEncoder viewport origin must be non-negative")
expect(encoder.set_viewport(0, 0, 0, 32, 0.0, 1.0)).to_equal(false)
expect(encoder.last_error).to_equal("GPURenderPassEncoder viewport size must be positive")
expect(encoder.set_viewport(0, 0, 32, 32, -0.1, 1.0)).to_equal(false)
expect(encoder.last_error).to_equal("GPURenderPassEncoder viewport depth range must be between 0 and 1")
expect(encoder.set_viewport(0, 0, 32, 32, 0.75, 0.25)).to_equal(false)
expect(encoder.last_error).to_equal("GPURenderPassEncoder viewport minDepth must not exceed maxDepth")
expect(encoder.set_stencil_reference(-1)).to_equal(false)
expect(encoder.last_error).to_equal("GPURenderPassEncoder stencil reference must be non-negative")
var outside = WebGPUCommandEncoder.create("outside")
expect(outside.set_blend_constant(0.0, 0.0, 0.0, 1.0)).to_equal(false)
expect(outside.last_error).to_equal("GPURenderPassEncoder setBlendConstant requires an active render pass")
```

</details>

#### records indirect draw commands

1. var encoder = WebGPUCommandEncoder create
   - Expected: encoder.begin_render_pass() is true
   - Expected: encoder.draw_indirect(3, 16) is true
   - Expected: encoder.draw_indexed_indirect(3, 32) is true
   - Expected: encoder.end_render_pass() is true
   - Expected: command_buffer.valid is true
   - Expected: command_buffer.command_count() equals `4`
   - Expected: command_buffer.commands[1].kind equals `WEBGPU_COMMAND_DRAW_INDIRECT`
   - Expected: command_buffer.commands[1].source_buffer_id equals `3`
   - Expected: command_buffer.commands[1].offset equals `16`
   - Expected: command_buffer.commands[1].size equals `16`
   - Expected: command_buffer.commands[2].kind equals `WEBGPU_COMMAND_DRAW_INDEXED_INDIRECT`
   - Expected: command_buffer.commands[2].size equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var encoder = WebGPUCommandEncoder.create("frame")
expect(encoder.begin_render_pass()).to_equal(true)
expect(encoder.draw_indirect(3, 16)).to_equal(true)
expect(encoder.draw_indexed_indirect(3, 32)).to_equal(true)
expect(encoder.end_render_pass()).to_equal(true)
val command_buffer = encoder.finish("indirect")
expect(command_buffer.valid).to_equal(true)
expect(command_buffer.command_count()).to_equal(4)
expect(command_buffer.commands[1].kind).to_equal(WEBGPU_COMMAND_DRAW_INDIRECT)
expect(command_buffer.commands[1].source_buffer_id).to_equal(3)
expect(command_buffer.commands[1].offset).to_equal(16)
expect(command_buffer.commands[1].size).to_equal(16)
expect(command_buffer.commands[2].kind).to_equal(WEBGPU_COMMAND_DRAW_INDEXED_INDIRECT)
expect(command_buffer.commands[2].size).to_equal(20)
```

</details>

#### rejects invalid indirect draw descriptors

1. var encoder = WebGPUCommandEncoder create
   - Expected: encoder.draw_indirect(3, 0) is false
   - Expected: encoder.last_error equals `GPURenderPassEncoder drawIndirect requires an active render pass`
   - Expected: encoder.begin_render_pass() is true
   - Expected: encoder.draw_indirect(0, 0) is false
   - Expected: encoder.last_error equals `GPURenderPassEncoder indirect draw buffer must be valid`
   - Expected: encoder.draw_indexed_indirect(3, 2) is false
   - Expected: encoder.last_error equals `GPURenderPassEncoder indirect draw offset must be 4-byte aligned`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var encoder = WebGPUCommandEncoder.create("frame")
expect(encoder.draw_indirect(3, 0)).to_equal(false)
expect(encoder.last_error).to_equal("GPURenderPassEncoder drawIndirect requires an active render pass")
expect(encoder.begin_render_pass()).to_equal(true)
expect(encoder.draw_indirect(0, 0)).to_equal(false)
expect(encoder.last_error).to_equal("GPURenderPassEncoder indirect draw buffer must be valid")
expect(encoder.draw_indexed_indirect(3, 2)).to_equal(false)
expect(encoder.last_error).to_equal("GPURenderPassEncoder indirect draw offset must be 4-byte aligned")
```

</details>

#### validates render pass color and depth attachments before recording

1. var resources = WebGPUResourceTable create
2. var encoder = WebGPUCommandEncoder create
   - Expected: encoder.begin_render_pass_with_descriptor(resources, [GPURenderPassColorAttachment.texture(color.id)], GPURenderPassDepthStencilAttachment.texture(depth.id)) is true
   - Expected: encoder.command_count() equals `1`
   - Expected: encoder.commands[0].kind equals `WEBGPU_COMMAND_BEGIN_RENDER_PASS`
   - Expected: encoder.commands[0].slot equals `1`
   - Expected: encoder.commands[0].destination_texture_id equals `depth.id`
   - Expected: encoder.commands[0].width equals `640`
   - Expected: encoder.commands[0].height equals `480`
   - Expected: encoder.commands[0].depth_or_layers equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var resources = WebGPUResourceTable.create()
val color = resources.create_texture("color", 640, 480, 1, GPU_TEXTURE_FORMAT_RGBA8_UNORM, WEBGPU_TEXTURE_USAGE_RENDER_ATTACHMENT)
val depth = resources.create_texture("depth", 640, 480, 1, GPU_TEXTURE_FORMAT_DEPTH24_PLUS, WEBGPU_TEXTURE_USAGE_RENDER_ATTACHMENT)
var encoder = WebGPUCommandEncoder.create("frame")
expect(encoder.begin_render_pass_with_descriptor(resources, [GPURenderPassColorAttachment.texture(color.id)], GPURenderPassDepthStencilAttachment.texture(depth.id))).to_equal(true)
expect(encoder.command_count()).to_equal(1)
expect(encoder.commands[0].kind).to_equal(WEBGPU_COMMAND_BEGIN_RENDER_PASS)
expect(encoder.commands[0].slot).to_equal(1)
expect(encoder.commands[0].destination_texture_id).to_equal(depth.id)
expect(encoder.commands[0].width).to_equal(640)
expect(encoder.commands[0].height).to_equal(480)
expect(encoder.commands[0].depth_or_layers).to_equal(1)
```

</details>

#### records depth-only render pass descriptors for shadow and prepass workloads

1. var resources = WebGPUResourceTable create
2. var encoder = WebGPUCommandEncoder create
   - Expected: encoder.begin_render_pass_with_descriptor(resources, [], GPURenderPassDepthStencilAttachment.texture_with_depth_ops(depth.id, "clear", "store")) is true
   - Expected: encoder.commands[0].slot equals `0`
   - Expected: encoder.commands[0].destination_texture_id equals `depth.id`
   - Expected: encoder.commands[0].width equals `1024`
   - Expected: encoder.commands[0].height equals `1024`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var resources = WebGPUResourceTable.create()
val depth = resources.create_texture("depth-only", 1024, 1024, 1, GPU_TEXTURE_FORMAT_DEPTH24_PLUS, WEBGPU_TEXTURE_USAGE_RENDER_ATTACHMENT)
var encoder = WebGPUCommandEncoder.create("depth-prepass")
expect(encoder.begin_render_pass_with_descriptor(resources, [], GPURenderPassDepthStencilAttachment.texture_with_depth_ops(depth.id, "clear", "store"))).to_equal(true)
expect(encoder.commands[0].slot).to_equal(0)
expect(encoder.commands[0].destination_texture_id).to_equal(depth.id)
expect(encoder.commands[0].width).to_equal(1024)
expect(encoder.commands[0].height).to_equal(1024)
```

</details>

#### validates render pass depth and stencil attachment operations

1. var resources = WebGPUResourceTable create
   - Expected: webgpu_validate_render_pass_descriptor_with_resources(resources, [GPURenderPassColorAttachment.texture(color.id)], GPURenderPassDepthStencilAttachment.texture_with_depth_ops(depth.id, "load", "discard")) equals ``
   - Expected: webgpu_validate_render_pass_descriptor_with_resources(resources, [GPURenderPassColorAttachment.texture(color.id)], GPURenderPassDepthStencilAttachment.texture_read_only(depth.id, true, false)) equals ``
   - Expected: webgpu_validate_render_pass_descriptor_with_resources(resources, [GPURenderPassColorAttachment.texture(color.id)], GPURenderPassDepthStencilAttachment.texture_read_only(depth.id, true, true)) equals `GPURenderPassDepthStencilAttachment stencil operations require a stencil-capa... (full value in folded executable source)`
   - Expected: webgpu_validate_render_pass_descriptor_with_resources(resources, [GPURenderPassColorAttachment.texture(color.id)], GPURenderPassDepthStencilAttachment.texture_with_depth_stencil_ops(depth_stencil.id, "clear", "store", "load", "discard")) equals ``
   - Expected: webgpu_validate_render_pass_descriptor_with_resources(resources, [GPURenderPassColorAttachment.texture(color.id)], GPURenderPassDepthStencilAttachment.texture_with_depth_stencil_ops(depth.id, "clear", "store", "load", "discard")) equals `GPURenderPassDepthStencilAttachment stencil operations require a stencil-capa... (full value in folded executable source)`
   - Expected: webgpu_validate_render_pass_descriptor_with_resources(resources, [GPURenderPassColorAttachment.texture(color.id)], GPURenderPassDepthStencilAttachment.texture_with_depth_ops(depth.id, "retain", "store")) equals `GPURenderPassDepthStencilAttachment depthLoadOp must be 'clear' or 'load'`
   - Expected: webgpu_validate_render_pass_descriptor_with_resources(resources, [GPURenderPassColorAttachment.texture(color.id)], GPURenderPassDepthStencilAttachment.texture_with_depth_ops(depth.id, "load", "keep")) equals `GPURenderPassDepthStencilAttachment depthStoreOp must be 'store' or 'discard'`
   - Expected: webgpu_validate_render_pass_descriptor_with_resources(resources, [GPURenderPassColorAttachment.texture(color.id)], GPURenderPassDepthStencilAttachment.texture_with_depth_stencil_ops(depth_stencil.id, "load", "store", "retain", "store")) equals `GPURenderPassDepthStencilAttachment stencilLoadOp must be 'clear' or 'load'`
   - Expected: webgpu_validate_render_pass_descriptor_with_resources(resources, [GPURenderPassColorAttachment.texture(color.id)], GPURenderPassDepthStencilAttachment.texture_with_depth_stencil_ops(depth_stencil.id, "load", "store", "load", "keep")) equals `GPURenderPassDepthStencilAttachment stencilStoreOp must be 'store' or 'discard'`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var resources = WebGPUResourceTable.create()
val color = resources.create_texture("color", 640, 480, 1, GPU_TEXTURE_FORMAT_RGBA8_UNORM, WEBGPU_TEXTURE_USAGE_RENDER_ATTACHMENT)
val depth = resources.create_texture("depth", 640, 480, 1, GPU_TEXTURE_FORMAT_DEPTH24_PLUS, WEBGPU_TEXTURE_USAGE_RENDER_ATTACHMENT)
val depth_stencil = resources.create_texture("depth-stencil", 640, 480, 1, GPU_TEXTURE_FORMAT_DEPTH24_PLUS_STENCIL8, WEBGPU_TEXTURE_USAGE_RENDER_ATTACHMENT)
expect(webgpu_validate_render_pass_descriptor_with_resources(resources, [GPURenderPassColorAttachment.texture(color.id)], GPURenderPassDepthStencilAttachment.texture_with_depth_ops(depth.id, "load", "discard"))).to_equal("")
expect(webgpu_validate_render_pass_descriptor_with_resources(resources, [GPURenderPassColorAttachment.texture(color.id)], GPURenderPassDepthStencilAttachment.texture_read_only(depth.id, true, false))).to_equal("")
expect(webgpu_validate_render_pass_descriptor_with_resources(resources, [GPURenderPassColorAttachment.texture(color.id)], GPURenderPassDepthStencilAttachment.texture_read_only(depth.id, true, true))).to_equal("GPURenderPassDepthStencilAttachment stencil operations require a stencil-capable format")
expect(webgpu_validate_render_pass_descriptor_with_resources(resources, [GPURenderPassColorAttachment.texture(color.id)], GPURenderPassDepthStencilAttachment.texture_with_depth_stencil_ops(depth_stencil.id, "clear", "store", "load", "discard"))).to_equal("")
expect(webgpu_validate_render_pass_descriptor_with_resources(resources, [GPURenderPassColorAttachment.texture(color.id)], GPURenderPassDepthStencilAttachment.texture_with_depth_stencil_ops(depth.id, "clear", "store", "load", "discard"))).to_equal("GPURenderPassDepthStencilAttachment stencil operations require a stencil-capable format")
expect(webgpu_validate_render_pass_descriptor_with_resources(resources, [GPURenderPassColorAttachment.texture(color.id)], GPURenderPassDepthStencilAttachment.texture_with_depth_ops(depth.id, "retain", "store"))).to_equal("GPURenderPassDepthStencilAttachment depthLoadOp must be 'clear' or 'load'")
expect(webgpu_validate_render_pass_descriptor_with_resources(resources, [GPURenderPassColorAttachment.texture(color.id)], GPURenderPassDepthStencilAttachment.texture_with_depth_ops(depth.id, "load", "keep"))).to_equal("GPURenderPassDepthStencilAttachment depthStoreOp must be 'store' or 'discard'")
expect(webgpu_validate_render_pass_descriptor_with_resources(resources, [GPURenderPassColorAttachment.texture(color.id)], GPURenderPassDepthStencilAttachment.texture_with_depth_stencil_ops(depth_stencil.id, "load", "store", "retain", "store"))).to_equal("GPURenderPassDepthStencilAttachment stencilLoadOp must be 'clear' or 'load'")
expect(webgpu_validate_render_pass_descriptor_with_resources(resources, [GPURenderPassColorAttachment.texture(color.id)], GPURenderPassDepthStencilAttachment.texture_with_depth_stencil_ops(depth_stencil.id, "load", "store", "load", "keep"))).to_equal("GPURenderPassDepthStencilAttachment stencilStoreOp must be 'store' or 'discard'")
```

</details>

#### rejects invalid render pass attachment descriptors

1. var resources = WebGPUResourceTable create
   - Expected: webgpu_validate_render_pass_descriptor_with_resources(resources, [], GPURenderPassDepthStencilAttachment.none()) equals `GPURenderPassDescriptor requires at least one attachment`
   - Expected: webgpu_validate_render_pass_descriptor_with_resources(resources, [GPURenderPassColorAttachment.texture(sampled.id)], GPURenderPassDepthStencilAttachment.none()) equals `GPURenderPassColorAttachment texture missing RENDER_ATTACHMENT usage`
   - Expected: webgpu_validate_render_pass_descriptor_with_resources(resources, [GPURenderPassColorAttachment.texture(color.id), GPURenderPassColorAttachment.texture(color.id)], GPURenderPassDepthStencilAttachment.none()) equals `GPURenderPassColorAttachment textures must be unique`
   - Expected: webgpu_validate_render_pass_descriptor_with_resources(resources, [GPURenderPassColorAttachment.texture(color.id)], GPURenderPassDepthStencilAttachment.texture(wrong_depth.id)) equals `GPURenderPassDepthStencilAttachment format must be depth-stencil-renderable`
   - Expected: webgpu_validate_render_pass_descriptor_with_resources(resources, [GPURenderPassColorAttachment.texture(color.id)], GPURenderPassDepthStencilAttachment.texture(small_depth.id)) equals `GPURenderPassDescriptor attachments must have matching dimensions`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var resources = WebGPUResourceTable.create()
val color = resources.create_texture("color", 640, 480, 1, GPU_TEXTURE_FORMAT_RGBA8_UNORM, WEBGPU_TEXTURE_USAGE_RENDER_ATTACHMENT)
val sampled = resources.create_texture("sampled", 640, 480, 1, GPU_TEXTURE_FORMAT_RGBA8_UNORM, WEBGPU_TEXTURE_USAGE_TEXTURE_BINDING)
val wrong_depth = resources.create_texture("wrong-depth", 640, 480, 1, GPU_TEXTURE_FORMAT_RGBA8_UNORM, WEBGPU_TEXTURE_USAGE_RENDER_ATTACHMENT)
val small_depth = resources.create_texture("small-depth", 320, 480, 1, GPU_TEXTURE_FORMAT_DEPTH24_PLUS, WEBGPU_TEXTURE_USAGE_RENDER_ATTACHMENT)
expect(webgpu_validate_render_pass_descriptor_with_resources(resources, [], GPURenderPassDepthStencilAttachment.none())).to_equal("GPURenderPassDescriptor requires at least one attachment")
expect(webgpu_validate_render_pass_descriptor_with_resources(resources, [GPURenderPassColorAttachment.texture(sampled.id)], GPURenderPassDepthStencilAttachment.none())).to_equal("GPURenderPassColorAttachment texture missing RENDER_ATTACHMENT usage")
expect(webgpu_validate_render_pass_descriptor_with_resources(resources, [GPURenderPassColorAttachment.texture(color.id), GPURenderPassColorAttachment.texture(color.id)], GPURenderPassDepthStencilAttachment.none())).to_equal("GPURenderPassColorAttachment textures must be unique")
expect(webgpu_validate_render_pass_descriptor_with_resources(resources, [GPURenderPassColorAttachment.texture(color.id)], GPURenderPassDepthStencilAttachment.texture(wrong_depth.id))).to_equal("GPURenderPassDepthStencilAttachment format must be depth-stencil-renderable")
expect(webgpu_validate_render_pass_descriptor_with_resources(resources, [GPURenderPassColorAttachment.texture(color.id)], GPURenderPassDepthStencilAttachment.texture(small_depth.id))).to_equal("GPURenderPassDescriptor attachments must have matching dimensions")
```

</details>

### compute pass recording

#### records dispatch workgroups

1. var encoder = WebGPUCommandEncoder create
   - Expected: encoder.begin_compute_pass() is true
   - Expected: encoder.set_pipeline(9) is true
   - Expected: encoder.dispatch_workgroups(2, 3, 1) is true
   - Expected: encoder.end_compute_pass() is true
   - Expected: command_buffer.valid is true
   - Expected: command_buffer.command_count() equals `4`
   - Expected: command_buffer.commands[0].kind equals `WEBGPU_COMMAND_BEGIN_COMPUTE_PASS`
   - Expected: command_buffer.commands[1].kind equals `WEBGPU_COMMAND_SET_PIPELINE`
   - Expected: command_buffer.commands[2].kind equals `WEBGPU_COMMAND_DISPATCH_WORKGROUPS`
   - Expected: command_buffer.commands[2].workgroups_x equals `2`
   - Expected: command_buffer.commands[3].kind equals `WEBGPU_COMMAND_END_COMPUTE_PASS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var encoder = WebGPUCommandEncoder.create("compute")
expect(encoder.begin_compute_pass()).to_equal(true)
expect(encoder.set_pipeline(9)).to_equal(true)
expect(encoder.dispatch_workgroups(2, 3, 1)).to_equal(true)
expect(encoder.end_compute_pass()).to_equal(true)
val command_buffer = encoder.finish("compute-commands")
expect(command_buffer.valid).to_equal(true)
expect(command_buffer.command_count()).to_equal(4)
expect(command_buffer.commands[0].kind).to_equal(WEBGPU_COMMAND_BEGIN_COMPUTE_PASS)
expect(command_buffer.commands[1].kind).to_equal(WEBGPU_COMMAND_SET_PIPELINE)
expect(command_buffer.commands[2].kind).to_equal(WEBGPU_COMMAND_DISPATCH_WORKGROUPS)
expect(command_buffer.commands[2].workgroups_x).to_equal(2)
expect(command_buffer.commands[3].kind).to_equal(WEBGPU_COMMAND_END_COMPUTE_PASS)
```

</details>

#### rejects dispatch outside a compute pass

1. var encoder = WebGPUCommandEncoder create
   - Expected: encoder.dispatch_workgroups(1, 1, 1) is false
   - Expected: encoder.last_error equals `GPUComputePassEncoder dispatch requires an active compute pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var encoder = WebGPUCommandEncoder.create("compute")
expect(encoder.dispatch_workgroups(1, 1, 1)).to_equal(false)
expect(encoder.last_error).to_equal("GPUComputePassEncoder dispatch requires an active compute pass")
```

</details>

### transfer commands

#### records buffer and texture copies outside passes

1. var encoder = WebGPUCommandEncoder create
   - Expected: encoder.copy_buffer_to_buffer(1, 4, 2, 8, 64) is true
   - Expected: encoder.copy_texture_to_texture(3, 4, 16, 8, 1) is true
   - Expected: command_buffer.valid is true
   - Expected: command_buffer.command_count() equals `2`
   - Expected: command_buffer.commands[0].kind equals `WEBGPU_COMMAND_COPY_BUFFER_TO_BUFFER`
   - Expected: command_buffer.commands[0].source_buffer_id equals `1`
   - Expected: command_buffer.commands[0].destination_buffer_id equals `2`
   - Expected: command_buffer.commands[0].offset equals `4`
   - Expected: command_buffer.commands[0].destination_offset equals `8`
   - Expected: command_buffer.commands[0].size equals `64`
   - Expected: command_buffer.commands[1].kind equals `WEBGPU_COMMAND_COPY_TEXTURE_TO_TEXTURE`
   - Expected: command_buffer.commands[1].source_texture_id equals `3`
   - Expected: command_buffer.commands[1].destination_texture_id equals `4`
   - Expected: command_buffer.commands[1].width equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var encoder = WebGPUCommandEncoder.create("transfers")
expect(encoder.copy_buffer_to_buffer(1, 4, 2, 8, 64)).to_equal(true)
expect(encoder.copy_texture_to_texture(3, 4, 16, 8, 1)).to_equal(true)
val command_buffer = encoder.finish("copy-commands")
expect(command_buffer.valid).to_equal(true)
expect(command_buffer.command_count()).to_equal(2)
expect(command_buffer.commands[0].kind).to_equal(WEBGPU_COMMAND_COPY_BUFFER_TO_BUFFER)
expect(command_buffer.commands[0].source_buffer_id).to_equal(1)
expect(command_buffer.commands[0].destination_buffer_id).to_equal(2)
expect(command_buffer.commands[0].offset).to_equal(4)
expect(command_buffer.commands[0].destination_offset).to_equal(8)
expect(command_buffer.commands[0].size).to_equal(64)
expect(command_buffer.commands[1].kind).to_equal(WEBGPU_COMMAND_COPY_TEXTURE_TO_TEXTURE)
expect(command_buffer.commands[1].source_texture_id).to_equal(3)
expect(command_buffer.commands[1].destination_texture_id).to_equal(4)
expect(command_buffer.commands[1].width).to_equal(16)
```

</details>

#### rejects copies inside active passes

1. var encoder = WebGPUCommandEncoder create
   - Expected: encoder.begin_render_pass() is true
   - Expected: encoder.copy_buffer_to_buffer(1, 0, 2, 0, 4) is false
   - Expected: encoder.last_error equals `GPUCommandEncoder copyBufferToBuffer cannot run inside a pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var encoder = WebGPUCommandEncoder.create("transfers")
expect(encoder.begin_render_pass()).to_equal(true)
expect(encoder.copy_buffer_to_buffer(1, 0, 2, 0, 4)).to_equal(false)
expect(encoder.last_error).to_equal("GPUCommandEncoder copyBufferToBuffer cannot run inside a pass")
```

</details>

#### rejects invalid copy descriptors

1. var encoder = WebGPUCommandEncoder create
   - Expected: encoder.copy_buffer_to_buffer(1, 0, 1, 0, 4) is false
   - Expected: encoder.last_error equals `GPUCommandEncoder copyBufferToBuffer requires distinct buffers`
   - Expected: encoder.copy_texture_to_texture(3, 4, 0, 8, 1) is false
   - Expected: encoder.last_error equals `GPUCommandEncoder copyTextureToTexture size must be positive`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var encoder = WebGPUCommandEncoder.create("transfers")
expect(encoder.copy_buffer_to_buffer(1, 0, 1, 0, 4)).to_equal(false)
expect(encoder.last_error).to_equal("GPUCommandEncoder copyBufferToBuffer requires distinct buffers")
expect(encoder.copy_texture_to_texture(3, 4, 0, 8, 1)).to_equal(false)
expect(encoder.last_error).to_equal("GPUCommandEncoder copyTextureToTexture size must be positive")
```

</details>

### queue writes

#### records buffer and texture writes

1. var queue = WebGPUQueue create
   - Expected: queue.write_buffer(1, 16, 128) is true
   - Expected: queue.write_texture(2, 4, 4, 1, 64) is true
   - Expected: queue.write_count() equals `2`
   - Expected: queue.write_commands[0].kind equals `WEBGPU_COMMAND_WRITE_BUFFER`
   - Expected: queue.write_commands[0].destination_buffer_id equals `1`
   - Expected: queue.write_commands[0].offset equals `16`
   - Expected: queue.write_commands[0].data_size equals `128`
   - Expected: queue.write_commands[1].kind equals `WEBGPU_COMMAND_WRITE_TEXTURE`
   - Expected: queue.write_commands[1].destination_texture_id equals `2`
   - Expected: queue.write_commands[1].width equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var queue = WebGPUQueue.create()
expect(queue.write_buffer(1, 16, 128)).to_equal(true)
expect(queue.write_texture(2, 4, 4, 1, 64)).to_equal(true)
expect(queue.write_count()).to_equal(2)
expect(queue.write_commands[0].kind).to_equal(WEBGPU_COMMAND_WRITE_BUFFER)
expect(queue.write_commands[0].destination_buffer_id).to_equal(1)
expect(queue.write_commands[0].offset).to_equal(16)
expect(queue.write_commands[0].data_size).to_equal(128)
expect(queue.write_commands[1].kind).to_equal(WEBGPU_COMMAND_WRITE_TEXTURE)
expect(queue.write_commands[1].destination_texture_id).to_equal(2)
expect(queue.write_commands[1].width).to_equal(4)
```

</details>

#### rejects invalid queue write descriptors

1. var queue = WebGPUQueue create
   - Expected: queue.write_buffer(-1, 0, 16) is false
   - Expected: queue.last_error equals `GPUQueue writeBuffer buffer must be valid`
   - Expected: queue.write_texture(2, 4, 4, 1, 0) is false
   - Expected: queue.last_error equals `GPUQueue writeTexture data size must be positive`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var queue = WebGPUQueue.create()
expect(queue.write_buffer(-1, 0, 16)).to_equal(false)
expect(queue.last_error).to_equal("GPUQueue writeBuffer buffer must be valid")
expect(queue.write_texture(2, 4, 4, 1, 0)).to_equal(false)
expect(queue.last_error).to_equal("GPUQueue writeTexture data size must be positive")
```

</details>

### resource-aware transfer validation

#### validates buffer copy resource usage and ranges

1. var resources = WebGPUResourceTable create
   - Expected: webgpu_validate_buffer_copy_with_resources(resources, source.id, 4, destination.id, 8, 16) equals ``
   - Expected: webgpu_validate_buffer_copy_with_resources(resources, 99, 0, destination.id, 0, 16) equals `GPUCommandEncoder copyBufferToBuffer source buffer does not exist`
   - Expected: webgpu_validate_buffer_copy_with_resources(resources, source.id, 0, wrong_usage.id, 0, 16) equals `GPUCommandEncoder copyBufferToBuffer destination buffer missing COPY_DST usage`
   - Expected: webgpu_validate_buffer_copy_with_resources(resources, source.id, 48, destination.id, 0, 32) equals `GPUCommandEncoder copyBufferToBuffer source range exceeds buffer size`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var resources = WebGPUResourceTable.create()
val source = resources.create_buffer("source", 64, WEBGPU_BUFFER_USAGE_COPY_SRC)
val destination = resources.create_buffer("destination", 64, WEBGPU_BUFFER_USAGE_COPY_DST)
val wrong_usage = resources.create_buffer("wrong", 64, WEBGPU_BUFFER_USAGE_COPY_SRC)
expect(webgpu_validate_buffer_copy_with_resources(resources, source.id, 4, destination.id, 8, 16)).to_equal("")
expect(webgpu_validate_buffer_copy_with_resources(resources, 99, 0, destination.id, 0, 16)).to_equal("GPUCommandEncoder copyBufferToBuffer source buffer does not exist")
expect(webgpu_validate_buffer_copy_with_resources(resources, source.id, 0, wrong_usage.id, 0, 16)).to_equal("GPUCommandEncoder copyBufferToBuffer destination buffer missing COPY_DST usage")
expect(webgpu_validate_buffer_copy_with_resources(resources, source.id, 48, destination.id, 0, 32)).to_equal("GPUCommandEncoder copyBufferToBuffer source range exceeds buffer size")
```

</details>

#### validates texture copy resource usage format and ranges

1. var resources = WebGPUResourceTable create
   - Expected: webgpu_validate_texture_copy_with_resources(resources, source.id, destination.id, 8, 8, 1) equals ``
   - Expected: webgpu_validate_texture_copy_with_resources(resources, 99, destination.id, 8, 8, 1) equals `GPUCommandEncoder copyTextureToTexture source texture does not exist`
   - Expected: webgpu_validate_texture_copy_with_resources(resources, source.id, wrong_format.id, 8, 8, 1) equals `GPUCommandEncoder copyTextureToTexture formats must match`
   - Expected: webgpu_validate_texture_copy_with_resources(resources, source.id, wrong_usage.id, 8, 8, 1) equals `GPUCommandEncoder copyTextureToTexture destination texture missing COPY_DST u... (full value in folded executable source)`
   - Expected: webgpu_validate_texture_copy_with_resources(resources, source.id, destination.id, 32, 8, 1) equals `GPUCommandEncoder copyTextureToTexture source range exceeds texture size`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var resources = WebGPUResourceTable.create()
val source = resources.create_texture("source", 16, 16, 1, GPU_TEXTURE_FORMAT_RGBA8_UNORM, WEBGPU_TEXTURE_USAGE_COPY_SRC)
val destination = resources.create_texture("destination", 16, 16, 1, GPU_TEXTURE_FORMAT_RGBA8_UNORM, WEBGPU_TEXTURE_USAGE_COPY_DST)
val wrong_format = resources.create_texture("wrong-format", 16, 16, 1, GPU_TEXTURE_FORMAT_BGRA8_UNORM, WEBGPU_TEXTURE_USAGE_COPY_DST)
val wrong_usage = resources.create_texture("wrong-usage", 16, 16, 1, GPU_TEXTURE_FORMAT_RGBA8_UNORM, WEBGPU_TEXTURE_USAGE_TEXTURE_BINDING)
expect(webgpu_validate_texture_copy_with_resources(resources, source.id, destination.id, 8, 8, 1)).to_equal("")
expect(webgpu_validate_texture_copy_with_resources(resources, 99, destination.id, 8, 8, 1)).to_equal("GPUCommandEncoder copyTextureToTexture source texture does not exist")
expect(webgpu_validate_texture_copy_with_resources(resources, source.id, wrong_format.id, 8, 8, 1)).to_equal("GPUCommandEncoder copyTextureToTexture formats must match")
expect(webgpu_validate_texture_copy_with_resources(resources, source.id, wrong_usage.id, 8, 8, 1)).to_equal("GPUCommandEncoder copyTextureToTexture destination texture missing COPY_DST usage")
expect(webgpu_validate_texture_copy_with_resources(resources, source.id, destination.id, 32, 8, 1)).to_equal("GPUCommandEncoder copyTextureToTexture source range exceeds texture size")
```

</details>

#### validates queue writes against resources

1. var resources = WebGPUResourceTable create
   - Expected: webgpu_validate_queue_write_buffer_with_resources(resources, buffer.id, 4, 16) equals ``
   - Expected: webgpu_validate_queue_write_buffer_with_resources(resources, wrong_buffer.id, 0, 16) equals `GPUQueue writeBuffer buffer missing COPY_DST usage`
   - Expected: webgpu_validate_queue_write_buffer_with_resources(resources, buffer.id, 48, 32) equals `GPUQueue writeBuffer range exceeds buffer size`
   - Expected: webgpu_validate_queue_write_texture_with_resources(resources, texture.id, 8, 8, 1, 64) equals ``
   - Expected: webgpu_validate_queue_write_texture_with_resources(resources, wrong_texture.id, 8, 8, 1, 64) equals `GPUQueue writeTexture texture missing COPY_DST usage`
   - Expected: webgpu_validate_queue_write_texture_with_resources(resources, texture.id, 32, 8, 1, 64) equals `GPUQueue writeTexture range exceeds texture size`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var resources = WebGPUResourceTable.create()
val buffer = resources.create_buffer("upload", 64, WEBGPU_BUFFER_USAGE_COPY_DST)
val texture = resources.create_texture("upload-texture", 16, 16, 1, GPU_TEXTURE_FORMAT_RGBA8_UNORM, WEBGPU_TEXTURE_USAGE_COPY_DST)
val wrong_buffer = resources.create_buffer("readback", 64, WEBGPU_BUFFER_USAGE_COPY_SRC)
val wrong_texture = resources.create_texture("sampled", 16, 16, 1, GPU_TEXTURE_FORMAT_RGBA8_UNORM, WEBGPU_TEXTURE_USAGE_TEXTURE_BINDING)
expect(webgpu_validate_queue_write_buffer_with_resources(resources, buffer.id, 4, 16)).to_equal("")
expect(webgpu_validate_queue_write_buffer_with_resources(resources, wrong_buffer.id, 0, 16)).to_equal("GPUQueue writeBuffer buffer missing COPY_DST usage")
expect(webgpu_validate_queue_write_buffer_with_resources(resources, buffer.id, 48, 32)).to_equal("GPUQueue writeBuffer range exceeds buffer size")
expect(webgpu_validate_queue_write_texture_with_resources(resources, texture.id, 8, 8, 1, 64)).to_equal("")
expect(webgpu_validate_queue_write_texture_with_resources(resources, wrong_texture.id, 8, 8, 1, 64)).to_equal("GPUQueue writeTexture texture missing COPY_DST usage")
expect(webgpu_validate_queue_write_texture_with_resources(resources, texture.id, 32, 8, 1, 64)).to_equal("GPUQueue writeTexture range exceeds texture size")
```

</details>

#### validates dynamic bind group offsets against layout and buffers

1. var resources = WebGPUResourceTable create
2. GPUBindGroupLayoutEntry dynamic buffer
3. GPUBindGroupLayoutEntry dynamic storage buffer
4. GPUBindGroupEntry buffer range
5. GPUBindGroupEntry buffer
   - Expected: webgpu_validate_bind_group_dynamic_offsets_with_resources(resources, 0, bind_group.id, [256, 0]) equals ``
   - Expected: webgpu_validate_bind_group_dynamic_offsets_with_resources(resources, 0, bind_group.id, [256]) equals `GPUPassEncoder dynamic offset count must match bind group layout`
   - Expected: webgpu_validate_bind_group_dynamic_offsets_with_resources(resources, 0, bind_group.id, [512, 0]) equals `GPUPassEncoder dynamic offset exceeds buffer size`
   - Expected: webgpu_validate_bind_group_dynamic_offsets_with_resources(resources, 0, 99, [0, 0]) equals `GPUPassEncoder bind group does not exist`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var resources = WebGPUResourceTable.create()
val uniform = resources.create_buffer("uniforms", 1024, WEBGPU_BUFFER_USAGE_UNIFORM)
val storage = resources.create_buffer("storage", 512, WEBGPU_BUFFER_USAGE_STORAGE)
val layout = resources.create_bind_group_layout("dynamic", [
    GPUBindGroupLayoutEntry.dynamic_buffer(0, WEBGPU_SHADER_STAGE_VERTEX),
    GPUBindGroupLayoutEntry.dynamic_storage_buffer(1, WEBGPU_SHADER_STAGE_FRAGMENT)
])
val bind_group = resources.create_bind_group("dynamic-0", layout.id, [
    GPUBindGroupEntry.buffer_range(0, uniform.id, 128, 512),
    GPUBindGroupEntry.buffer(1, storage.id)
])
expect(webgpu_validate_bind_group_dynamic_offsets_with_resources(resources, 0, bind_group.id, [256, 0])).to_equal("")
expect(webgpu_validate_bind_group_dynamic_offsets_with_resources(resources, 0, bind_group.id, [256])).to_equal("GPUPassEncoder dynamic offset count must match bind group layout")
expect(webgpu_validate_bind_group_dynamic_offsets_with_resources(resources, 0, bind_group.id, [512, 0])).to_equal("GPUPassEncoder dynamic offset exceeds buffer size")
expect(webgpu_validate_bind_group_dynamic_offsets_with_resources(resources, 0, 99, [0, 0])).to_equal("GPUPassEncoder bind group does not exist")
```

</details>

#### records bind groups with resource-aware dynamic offset validation

1. var resources = WebGPUResourceTable create
2. GPUBindGroupLayoutEntry dynamic buffer
3. GPUBindGroupEntry buffer
4. var encoder = WebGPUCommandEncoder create
   - Expected: encoder.begin_render_pass() is true
   - Expected: encoder.set_bind_group_with_dynamic_offsets_and_resources(resources, 0, bind_group.id, [256]) is true
   - Expected: encoder.commands[1].bind_group_id equals `bind_group.id`
   - Expected: encoder.commands[1].dynamic_offset_count equals `1`
   - Expected: encoder.set_bind_group_with_dynamic_offsets_and_resources(resources, 0, bind_group.id, [1024]) is false
   - Expected: encoder.last_error equals `GPUPassEncoder dynamic offset exceeds buffer size`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var resources = WebGPUResourceTable.create()
val uniform = resources.create_buffer("uniforms", 1024, WEBGPU_BUFFER_USAGE_UNIFORM)
val layout = resources.create_bind_group_layout("dynamic", [
    GPUBindGroupLayoutEntry.dynamic_buffer(0, WEBGPU_SHADER_STAGE_VERTEX)
])
val bind_group = resources.create_bind_group("dynamic-0", layout.id, [
    GPUBindGroupEntry.buffer(0, uniform.id)
])
var encoder = WebGPUCommandEncoder.create("frame")
expect(encoder.begin_render_pass()).to_equal(true)
expect(encoder.set_bind_group_with_dynamic_offsets_and_resources(resources, 0, bind_group.id, [256])).to_equal(true)
expect(encoder.commands[1].bind_group_id).to_equal(bind_group.id)
expect(encoder.commands[1].dynamic_offset_count).to_equal(1)
expect(encoder.set_bind_group_with_dynamic_offsets_and_resources(resources, 0, bind_group.id, [1024])).to_equal(false)
expect(encoder.last_error).to_equal("GPUPassEncoder dynamic offset exceeds buffer size")
```

</details>

#### validates indirect draw buffers against resources

1. var resources = WebGPUResourceTable create
   - Expected: webgpu_validate_indirect_draw_buffer_with_resources(resources, indirect.id, 16, 16) equals ``
   - Expected: webgpu_validate_indirect_draw_buffer_with_resources(resources, 99, 0, 16) equals `GPURenderPassEncoder indirect draw buffer does not exist`
   - Expected: webgpu_validate_indirect_draw_buffer_with_resources(resources, wrong_usage.id, 0, 16) equals `GPURenderPassEncoder indirect draw buffer missing INDIRECT usage`
   - Expected: webgpu_validate_indirect_draw_buffer_with_resources(resources, indirect.id, 48, 20) equals `GPURenderPassEncoder indirect draw range exceeds buffer size`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var resources = WebGPUResourceTable.create()
val indirect = resources.create_buffer("indirect", 64, WEBGPU_BUFFER_USAGE_INDIRECT)
val wrong_usage = resources.create_buffer("uniforms", 64, WEBGPU_BUFFER_USAGE_UNIFORM)
expect(webgpu_validate_indirect_draw_buffer_with_resources(resources, indirect.id, 16, 16)).to_equal("")
expect(webgpu_validate_indirect_draw_buffer_with_resources(resources, 99, 0, 16)).to_equal("GPURenderPassEncoder indirect draw buffer does not exist")
expect(webgpu_validate_indirect_draw_buffer_with_resources(resources, wrong_usage.id, 0, 16)).to_equal("GPURenderPassEncoder indirect draw buffer missing INDIRECT usage")
expect(webgpu_validate_indirect_draw_buffer_with_resources(resources, indirect.id, 48, 20)).to_equal("GPURenderPassEncoder indirect draw range exceeds buffer size")
```

</details>

### encoder and queue validation

#### rejects finish while a pass is active

1. var encoder = WebGPUCommandEncoder create
   - Expected: encoder.begin_render_pass() is true
   - Expected: command_buffer.valid is false
   - Expected: command_buffer.error equals `GPUCommandEncoder cannot finish while a pass is active`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var encoder = WebGPUCommandEncoder.create("frame")
expect(encoder.begin_render_pass()).to_equal(true)
val command_buffer = encoder.finish("bad")
expect(command_buffer.valid).to_equal(false)
expect(command_buffer.error).to_equal("GPUCommandEncoder cannot finish while a pass is active")
```

</details>

#### rejects recording after finish

1. var encoder = WebGPUCommandEncoder create
   - Expected: command_buffer.valid is true
   - Expected: encoder.begin_render_pass() is false
   - Expected: encoder.last_error equals `GPUCommandEncoder is already finished`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var encoder = WebGPUCommandEncoder.create("frame")
val command_buffer = encoder.finish("empty")
expect(command_buffer.valid).to_equal(true)
expect(encoder.begin_render_pass()).to_equal(false)
expect(encoder.last_error).to_equal("GPUCommandEncoder is already finished")
```

</details>

#### rejects empty queue submissions

1. var queue = WebGPUQueue create
   - Expected: queue.submit([]) is false
   - Expected: queue.last_error equals `GPUQueue submit requires at least one command buffer`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var queue = WebGPUQueue.create()
expect(queue.submit([])).to_equal(false)
expect(queue.last_error).to_equal("GPUQueue submit requires at least one command buffer")
```

</details>

#### rejects mixed invalid submissions atomically

1. var encoder = WebGPUCommandEncoder create
2. var queue = WebGPUQueue create
   - Expected: valid.valid is true
   - Expected: invalid.valid is false
   - Expected: queue.submit([valid, invalid]) is false
   - Expected: queue.last_error equals `GPUQueue cannot submit an invalid command buffer`
   - Expected: queue.submitted_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var encoder = WebGPUCommandEncoder.create("frame")
val valid = encoder.finish("empty")
val invalid = encoder.finish("already-finished")
var queue = WebGPUQueue.create()
expect(valid.valid).to_equal(true)
expect(invalid.valid).to_equal(false)
expect(queue.submit([valid, invalid])).to_equal(false)
expect(queue.last_error).to_equal("GPUQueue cannot submit an invalid command buffer")
expect(queue.submitted_count()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/webgpu/webgpu_commands_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Browser WebGPU command encoding
- render pass recording
- compute pass recording
- transfer commands
- queue writes
- resource-aware transfer validation
- encoder and queue validation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 31 |
| Active scenarios | 31 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
