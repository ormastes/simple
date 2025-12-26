# Vulkan UI Backend Design

## Overview

Design document for integrating Vulkan as a high-performance GPU-accelerated backend for the Simple UI framework. This backend will leverage GPU compute and graphics capabilities while maintaining compatibility with the existing Element/PatchSet abstraction.

## Architecture Overview

```
┌─────────────────────────────────────────────────────────────┐
│                    UI Framework Layer                        │
│  Element Tree → Diff → PatchSet → RenderBackend             │
└─────────────────────────────────────────────────────────────┘
                            │
                            ▼
┌─────────────────────────────────────────────────────────────┐
│               CPU Layer (VulkanRenderer)                     │
│  ┌──────────────┐  ┌─────────────┐  ┌──────────────┐       │
│  │Layout Engine │  │Element      │  │Resource      │       │
│  │(Flexbox/Grid)│→ │Processor    │→ │Manager       │       │
│  └──────────────┘  └─────────────┘  └──────────────┘       │
│         │                │                    │              │
│         └────────────────┴────────────────────┘              │
│                          │                                   │
└──────────────────────────┼───────────────────────────────────┘
                           │ Command Stream
                           ▼
┌─────────────────────────────────────────────────────────────┐
│                GPU Layer (Vulkan Core)                       │
│  ┌──────────────┐  ┌─────────────┐  ┌──────────────┐       │
│  │Device/Queue  │  │Render Pass  │  │Command       │       │
│  │Manager       │  │& Pipelines  │  │Buffers       │       │
│  └──────────────┘  └─────────────┘  └──────────────┘       │
│  ┌──────────────┐  ┌─────────────┐  ┌──────────────┐       │
│  │Buffer        │  │Text         │  │Shader        │       │
│  │Manager       │  │Renderer     │  │Manager       │       │
│  └──────────────┘  └─────────────┘  └──────────────┘       │
└─────────────────────────────────────────────────────────────┘
                           │
                           ▼
                      GPU Hardware
```

## CPU vs GPU Responsibilities

### CPU Layer Operations

**Layout & Measurement**
- Flexbox layout calculation
- Grid layout calculation
- Text measurement and shaping
- Hit testing for mouse events
- Focus management
- Dirty rectangle tracking

**Element Processing**
- Element tree traversal
- Style resolution and cascade
- Diff algorithm (keyed diffing, LIS)
- Patch generation and optimization
- Resource loading (images, fonts)
- Event routing

**Vulkan Setup**
- Instance/device creation
- Queue family selection
- Swapchain management
- Resource allocation
- Command buffer recording

### GPU Layer Operations

**Rendering**
- Vertex transformation (MVP matrices)
- Rasterization
- Fragment shading
- Blending and composition
- Multi-sample anti-aliasing (MSAA)

**Advanced Effects (GPU shaders)**
- Rounded corners (distance field)
- Drop shadows (gaussian blur)
- Gradients (linear, radial)
- Glow/bloom effects
- Color grading
- Post-processing

**Text Rendering**
- Signed Distance Field (SDF) text
- Subpixel rendering
- Font atlas management
- Glyph caching

**Optimizations**
- Instanced rendering (batching)
- Texture atlasing
- Geometry caching
- Occlusion culling (if complex)

## Class Diagram

### CPU Layer Classes

```
┌─────────────────────────────────────────┐
│         VulkanRenderer                   │
│  (implements RenderBackend)              │
├─────────────────────────────────────────┤
│ - device: VulkanDevice                   │
│ - layout_engine: LayoutEngine            │
│ - element_processor: ElementProcessor    │
│ - resource_manager: ResourceManager      │
│ - swapchain: Swapchain                   │
│ - frame_index: u32                       │
│ - initialized: bool                      │
├─────────────────────────────────────────┤
│ + init() -> Result                       │
│ + shutdown() -> Result                   │
│ + render(tree: &ElementTree) -> Result  │
│ + apply_patches(patches: &PatchSet)     │
│ + poll_event(timeout_ms: u64)           │
│ - record_commands(frame: &Frame)        │
│ - present_frame()                        │
└─────────────────────────────────────────┘
          │
          │ has-a
          ▼
┌─────────────────────────────────────────┐
│          LayoutEngine                    │
├─────────────────────────────────────────┤
│ - cache: LayoutCache                     │
│ - font_metrics: FontMetrics              │
├─────────────────────────────────────────┤
│ + compute_layout(tree: &Element,        │
│                  constraints: BoxConstraints)
│                  -> LayoutResult         │
│ - layout_flexbox(elem, constraints)     │
│ - layout_grid(elem, constraints)        │
│ - layout_block(elem, constraints)       │
│ - measure_text(text, style) -> Size     │
└─────────────────────────────────────────┘

┌─────────────────────────────────────────┐
│       ElementProcessor                   │
├─────────────────────────────────────────┤
│ - vertex_builder: VertexBuilder          │
│ - draw_list: DrawList                    │
├─────────────────────────────────────────┤
│ + process_tree(tree: &Element,          │
│                layout: &LayoutResult)    │
│                -> DrawList               │
│ - process_element(elem, layout)         │
│ - emit_rect(bounds, color, border)      │
│ - emit_text(bounds, text, style)        │
│ - emit_rounded_rect(bounds, radius)     │
└─────────────────────────────────────────┘

┌─────────────────────────────────────────┐
│        ResourceManager                   │
├─────────────────────────────────────────┤
│ - textures: HashMap<TextureId, Texture> │
│ - font_atlas: FontAtlas                  │
│ - pipeline_cache: HashMap<PipelineKey,  │
│                           Pipeline>      │
├─────────────────────────────────────────┤
│ + load_texture(path: &str) -> TextureId │
│ + load_font(path: &str) -> FontId       │
│ + get_pipeline(key: PipelineKey)        │
│   -> &Pipeline                           │
│ + cleanup()                              │
└─────────────────────────────────────────┘
```

### GPU Layer Classes

```
┌─────────────────────────────────────────┐
│          VulkanDevice                    │
├─────────────────────────────────────────┤
│ - instance: vk::Instance                 │
│ - physical_device: vk::PhysicalDevice    │
│ - device: vk::Device                     │
│ - graphics_queue: vk::Queue              │
│ - present_queue: vk::Queue               │
│ - command_pool: vk::CommandPool          │
│ - allocator: VmaAllocator                │
├─────────────────────────────────────────┤
│ + new(window_handle) -> Result<Self>    │
│ + create_buffer(size, usage) -> Buffer  │
│ + create_texture(width, height)         │
│   -> Texture                             │
│ + allocate_command_buffer()              │
│   -> CommandBuffer                       │
│ + submit(cmd_buf, wait, signal)         │
│ + destroy()                              │
└─────────────────────────────────────────┘

┌─────────────────────────────────────────┐
│          RenderPass                      │
├─────────────────────────────────────────┤
│ - render_pass: vk::RenderPass            │
│ - framebuffers: Vec<vk::Framebuffer>     │
│ - color_format: vk::Format               │
│ - depth_format: Option<vk::Format>       │
│ - msaa_samples: u32                      │
├─────────────────────────────────────────┤
│ + new(device, swapchain) -> Self         │
│ + begin(cmd_buf, framebuffer_idx)       │
│ + end(cmd_buf)                           │
│ + recreate(swapchain)                    │
└─────────────────────────────────────────┘

┌─────────────────────────────────────────┐
│          Pipeline                        │
├─────────────────────────────────────────┤
│ - pipeline: vk::Pipeline                 │
│ - layout: vk::PipelineLayout             │
│ - descriptor_sets: Vec<vk::DescriptorSet>
│ - pipeline_type: PipelineType            │
├─────────────────────────────────────────┤
│ + new(device, render_pass, shaders)     │
│   -> Self                                │
│ + bind(cmd_buf)                          │
│ + push_constants(cmd_buf, data)         │
│ + bind_descriptor_set(cmd_buf, set_idx) │
└─────────────────────────────────────────┘

┌─────────────────────────────────────────┐
│         CommandBuffer                    │
├─────────────────────────────────────────┤
│ - cmd_buf: vk::CommandBuffer             │
│ - state: CommandBufferState              │
├─────────────────────────────────────────┤
│ + begin()                                │
│ + end()                                  │
│ + begin_render_pass(render_pass)        │
│ + end_render_pass()                      │
│ + bind_pipeline(pipeline)                │
│ + bind_vertex_buffer(buffer)            │
│ + bind_index_buffer(buffer)             │
│ + draw(vertex_count, instance_count)    │
│ + draw_indexed(index_count)             │
│ + set_viewport(x, y, w, h)              │
│ + set_scissor(x, y, w, h)               │
└─────────────────────────────────────────┘

┌─────────────────────────────────────────┐
│         BufferManager                    │
├─────────────────────────────────────────┤
│ - vertex_buffers: Vec<Buffer>            │
│ - index_buffers: Vec<Buffer>             │
│ - uniform_buffers: Vec<Buffer>           │
│ - staging_buffers: Vec<Buffer>           │
│ - frame_index: usize                     │
├─────────────────────────────────────────┤
│ + alloc_vertex_buffer(size) -> Buffer   │
│ + alloc_index_buffer(size) -> Buffer    │
│ + alloc_uniform_buffer(size) -> Buffer  │
│ + upload_data(buffer, data)             │
│ + next_frame()                           │
│ + cleanup_old_buffers()                  │
└─────────────────────────────────────────┘

┌─────────────────────────────────────────┐
│         TextRenderer                     │
├─────────────────────────────────────────┤
│ - font_atlas: Texture                    │
│ - sdf_pipeline: Pipeline                 │
│ - glyph_cache: HashMap<GlyphKey, Rect>  │
│ - atlas_packer: RectPacker               │
├─────────────────────────────────────────┤
│ + render_text(cmd_buf, text, pos,       │
│               style) -> DrawCall         │
│ + cache_glyph(glyph_id, font_id)        │
│   -> Rect                                │
│ + regenerate_atlas()                     │
└─────────────────────────────────────────┘
```

## Data Structures

### DrawList
```simple
# Batched draw commands for GPU
pub struct DrawList:
    vertices: Array[Vertex]
    indices: Array[u32]
    draw_calls: Array[DrawCall]

pub struct Vertex:
    position: (f32, f32)      # Screen coordinates
    uv: (f32, f32)            # Texture coordinates
    color: u32                # RGBA packed

pub struct DrawCall:
    pipeline: PipelineType
    vertex_offset: u32
    vertex_count: u32
    index_offset: u32
    index_count: u32
    texture: Option[TextureId]
    scissor: Option[Rect]
```

### PipelineType
```simple
pub enum PipelineType:
    SolidColor       # Filled rectangles
    Textured         # Images
    RoundedRect      # Rounded corners (SDF)
    Text             # SDF text
    Gradient         # Linear/radial gradients
    Shadow           # Drop shadows
```

## Rendering Pipeline

### Frame Rendering Flow

```
1. Begin Frame
   ├─ Acquire swapchain image
   ├─ Reset command buffer
   └─ Begin render pass

2. Layout Phase (CPU)
   ├─ Compute layout from element tree
   ├─ Cache layout results
   └─ Determine dirty regions

3. Process Phase (CPU)
   ├─ Traverse element tree
   ├─ Generate draw list (vertices/indices)
   ├─ Batch draw calls by pipeline
   └─ Upload to GPU buffers

4. Record Phase (CPU → GPU)
   ├─ Bind pipelines
   ├─ Set viewport/scissor
   ├─ Bind descriptor sets
   ├─ Issue draw calls
   └─ Apply post-processing

5. Submit & Present
   ├─ End render pass
   ├─ Submit command buffer
   ├─ Present swapchain image
   └─ Update frame index
```

### Incremental Updates (Patches)

```
1. Receive PatchSet
   ├─ Identify affected elements
   └─ Mark dirty regions

2. Partial Layout Update
   ├─ Re-layout only affected subtrees
   └─ Update layout cache

3. Minimal Re-processing
   ├─ Regenerate draw list for dirty regions
   ├─ Reuse cached geometry for clean regions
   └─ Upload only changed buffers

4. Render Frame
   ├─ Use scissor rects for dirty regions
   └─ Skip unaffected areas
```

## Shader Architecture

### Vertex Shaders

All pipelines use a common vertex shader:
```glsl
#version 450

layout(location = 0) in vec2 inPosition;
layout(location = 1) in vec2 inUV;
layout(location = 2) in vec4 inColor;

layout(location = 0) out vec2 fragUV;
layout(location = 1) out vec4 fragColor;

layout(push_constant) uniform PushConstants {
    mat4 projection;  // Orthographic projection
} pc;

void main() {
    gl_Position = pc.projection * vec4(inPosition, 0.0, 1.0);
    fragUV = inUV;
    fragColor = inColor;
}
```

### Fragment Shaders

**SolidColor Pipeline**
```glsl
#version 450

layout(location = 0) in vec2 fragUV;
layout(location = 1) in vec4 fragColor;
layout(location = 0) out vec4 outColor;

void main() {
    outColor = fragColor;
}
```

**RoundedRect Pipeline (SDF)**
```glsl
#version 450

layout(location = 0) in vec2 fragUV;
layout(location = 1) in vec4 fragColor;
layout(location = 0) out vec4 outColor;

layout(push_constant) uniform PushConstants {
    mat4 projection;
    vec4 rect;      // x, y, width, height
    vec4 radii;     // top-left, top-right, bottom-right, bottom-left
    float border_width;
    vec4 border_color;
} pc;

// Rounded rectangle SDF
float roundedBoxSDF(vec2 p, vec2 size, vec4 radii) {
    // Select radius based on quadrant
    float r = p.x > 0.0
        ? (p.y > 0.0 ? radii.w : radii.z)
        : (p.y > 0.0 ? radii.x : radii.y);

    vec2 q = abs(p) - size + r;
    return min(max(q.x, q.y), 0.0) + length(max(q, 0.0)) - r;
}

void main() {
    vec2 p = fragUV * pc.rect.zw - pc.rect.zw * 0.5;
    float dist = roundedBoxSDF(p, pc.rect.zw * 0.5, pc.radii);

    // Anti-aliased edge
    float alpha = 1.0 - smoothstep(-0.5, 0.5, dist);

    // Border
    float border = abs(dist + pc.border_width * 0.5) - pc.border_width * 0.5;
    float borderAlpha = 1.0 - smoothstep(-0.5, 0.5, border);

    vec4 color = mix(fragColor, pc.border_color, borderAlpha);
    outColor = vec4(color.rgb, color.a * alpha);
}
```

**Text Pipeline (SDF)**
```glsl
#version 450

layout(location = 0) in vec2 fragUV;
layout(location = 1) in vec4 fragColor;
layout(location = 0) out vec4 outColor;

layout(set = 0, binding = 0) uniform sampler2D fontAtlas;

void main() {
    float dist = texture(fontAtlas, fragUV).a;
    float alpha = smoothstep(0.5 - fwidth(dist), 0.5 + fwidth(dist), dist);
    outColor = vec4(fragColor.rgb, fragColor.a * alpha);
}
```

## Memory Management

### Buffer Strategy

**Triple Buffering**
- 3 sets of vertex/index/uniform buffers
- Rotate buffers each frame
- Prevents CPU/GPU sync stalls

**Staging Buffers**
- CPU-visible staging buffers for uploads
- GPU-local device buffers for rendering
- Copy from staging to device once per frame

**Buffer Pooling**
- Reuse buffers across frames
- Grow buffers as needed
- Cleanup unused buffers after N frames

### Texture Management

**Font Atlas**
- Single texture with all glyphs (SDF)
- Dynamic packing with rect packer
- Regenerate when cache full

**Image Atlas**
- Pack small images into single texture
- Reduce descriptor set switches
- Use mipmap for minification

## Optimization Strategies

### CPU Optimizations

1. **Layout Caching**: Cache layout results, only recompute dirty subtrees
2. **Draw Call Batching**: Merge consecutive draw calls with same pipeline
3. **Culling**: Skip elements outside viewport
4. **Dirty Tracking**: Only update changed regions

### GPU Optimizations

1. **Instanced Rendering**: Batch similar elements (buttons, icons)
2. **Texture Atlas**: Reduce texture binds
3. **Pipeline Caching**: Reuse compiled pipelines
4. **Descriptor Set Pooling**: Reuse descriptor sets
5. **Command Buffer Reuse**: Cache command buffers for static content

### Advanced Optimizations

1. **Multi-threading**: Parallel layout calculation
2. **Compute Shaders**: Complex effects (blur, glow)
3. **Indirect Drawing**: GPU-driven rendering
4. **Occlusion Queries**: Skip hidden elements

## Implementation Phases

### Phase 1: Core Infrastructure
- [ ] VulkanDevice setup (instance, device, queues)
- [ ] Swapchain management
- [ ] Basic render pass
- [ ] Command buffer recording
- [ ] Buffer manager

### Phase 2: Basic Rendering
- [ ] Solid color pipeline
- [ ] Rectangle rendering
- [ ] Vertex/index buffer generation
- [ ] Simple element tree rendering

### Phase 3: Layout Engine
- [ ] Basic block layout
- [ ] Flexbox layout
- [ ] Layout caching
- [ ] Text measurement (stub)

### Phase 4: Advanced Rendering
- [ ] Rounded rectangle pipeline (SDF)
- [ ] Textured pipeline (images)
- [ ] SDF text rendering
- [ ] Font atlas management

### Phase 5: Optimization
- [ ] Draw call batching
- [ ] Dirty region tracking
- [ ] Patch-based updates
- [ ] Triple buffering

### Phase 6: Effects
- [ ] Drop shadows
- [ ] Gradients
- [ ] Blur (compute shader)
- [ ] Post-processing

## Testing Strategy

1. **Unit Tests**: Individual components (layout, batching)
2. **Integration Tests**: Full rendering pipeline
3. **Visual Tests**: Compare with reference images
4. **Performance Tests**: Frame time, batching efficiency
5. **Stress Tests**: Large element trees, many updates

## References

- Vulkan Spec: https://www.khronos.org/vulkan/
- VMA (Vulkan Memory Allocator): https://github.com/GPUOpen-LibrariesAndSDKs/VulkanMemoryAllocator
- SDF Text Rendering: https://github.com/Chlumsky/msdfgen
- Dear ImGui (reference): https://github.com/ocornut/imgui
