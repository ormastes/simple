# Vulkan UI Backend Class Diagrams

## System Architecture Overview

```
┌────────────────────────────────────────────────────────────────────────┐
│                         UI Framework (Platform Agnostic)                │
│                                                                          │
│  ┌──────────────┐     ┌─────────────┐     ┌──────────────────────┐    │
│  │ Element Tree │────▶│   Differ    │────▶│    PatchSet          │    │
│  │  (Virtual)   │     │  (Keyed)    │     │  (Minimal Updates)   │    │
│  └──────────────┘     └─────────────┘     └──────────────────────┘    │
│                                                      │                  │
│                                                      ▼                  │
│                               ┌─────────────────────────────────┐      │
│                               │   RenderBackend (trait)         │      │
│                               │  - init(), shutdown()           │      │
│                               │  - render(tree)                 │      │
│                               │  - apply_patches(patches)       │      │
│                               │  - poll_event()                 │      │
│                               └─────────────────────────────────┘      │
└────────────────────────────────────────────────────────────────────────┘
                                         │
                 ┌───────────────────────┼───────────────────────┐
                 │                       │                       │
                 ▼                       ▼                       ▼
        ┌────────────────┐    ┌──────────────────┐    ┌─────────────────┐
        │  TuiRenderer   │    │  HtmlRenderer    │    │ VulkanRenderer  │
        │  (Terminal)    │    │  (Web/SSR)       │    │  (GPU)          │
        └────────────────┘    └──────────────────┘    └─────────────────┘
                                                                │
                                                                ▼
                               ┌─────────────────────────────────────┐
                               │      Vulkan Backend Architecture    │
                               │      (Detailed below)               │
                               └─────────────────────────────────────┘
```

## CPU Layer Detailed Architecture

```
┌────────────────────────────────────────────────────────────────────────┐
│                          VulkanRenderer                                 │
│                      (implements RenderBackend)                         │
├────────────────────────────────────────────────────────────────────────┤
│  Fields:                                                                │
│    - device: VulkanDevice              # GPU device manager             │
│    - swapchain: Swapchain              # Window surface images          │
│    - render_pass: RenderPass           # Render pass & framebuffers    │
│    - layout_engine: LayoutEngine       # Computes layout               │
│    - element_processor: ElementProcessor # Builds draw lists           │
│    - resource_manager: ResourceManager # Textures, fonts, pipelines    │
│    - buffer_manager: BufferManager     # Vertex/index/uniform buffers  │
│    - text_renderer: TextRenderer       # SDF text rendering            │
│    - frame_data: [FrameData; 3]        # Triple buffering             │
│    - frame_index: usize                # Current frame                 │
│    - initialized: bool                                                  │
├────────────────────────────────────────────────────────────────────────┤
│  Methods:                                                               │
│    + new(window, width, height) -> Result<Self>                        │
│    + init() -> Result<()>                                              │
│    + shutdown() -> Result<()>                                          │
│    + render(tree: &ElementTree) -> Result<()>                         │
│    + apply_patches(patches: &PatchSet) -> Result<()>                  │
│    + poll_event(timeout_ms: u64) -> Result<Option<Event>>             │
│    - begin_frame() -> Result<Frame>                                    │
│    - record_commands(frame: &Frame, draw_list: &DrawList)             │
│    - end_frame(frame: Frame) -> Result<()>                             │
└────────────────────────────────────────────────────────────────────────┘
                    │ owns          │ owns          │ owns
         ┌──────────┴─────┬─────────┴──────┬───────┴────────┐
         ▼                ▼                ▼                ▼
┌─────────────────┐ ┌──────────────┐ ┌───────────────┐ ┌─────────────────┐
│  LayoutEngine   │ │ElementProc.  │ │ResourceMgr    │ │ BufferManager   │
├─────────────────┤ ├──────────────┤ ├───────────────┤ ├─────────────────┤
│ - cache:        │ │ - vertex_    │ │ - textures:   │ │ - vertex_pool:  │
│   LayoutCache   │ │   builder:   │ │   HashMap     │ │   Vec<Buffer>   │
│ - font_metrics  │ │   VertexBld  │ │ - font_atlas  │ │ - index_pool    │
│                 │ │ - draw_list  │ │ - pipelines   │ │ - uniform_pool  │
├─────────────────┤ ├──────────────┤ ├───────────────┤ ├─────────────────┤
│ + compute_      │ │ + process_   │ │ + load_texture│ │ + alloc_vertex_ │
│   layout()      │ │   tree()     │ │ + load_font   │ │   buffer()      │
│ - layout_       │ │ - process_   │ │ + get_pipeline│ │ + upload_data() │
│   flexbox()     │ │   element()  │ │ + cleanup()   │ │ + next_frame()  │
│ - layout_grid() │ │ - emit_rect()│ │               │ │                 │
│ - measure_text()│ │ - emit_text()│ │               │ │                 │
└─────────────────┘ └──────────────┘ └───────────────┘ └─────────────────┘
```

## GPU Layer Detailed Architecture

```
┌────────────────────────────────────────────────────────────────────────┐
│                          VulkanDevice                                   │
│                   (Low-level Vulkan abstraction)                        │
├────────────────────────────────────────────────────────────────────────┤
│  Fields:                                                                │
│    - instance: vk::Instance                                             │
│    - physical_device: vk::PhysicalDevice                                │
│    - device: vk::Device                                                 │
│    - graphics_queue: vk::Queue                                          │
│    - present_queue: vk::Queue                                           │
│    - graphics_family_index: u32                                         │
│    - present_family_index: u32                                          │
│    - command_pool: vk::CommandPool                                      │
│    - allocator: VmaAllocator                # Vulkan Memory Allocator   │
│    - descriptor_pool: vk::DescriptorPool                                │
├────────────────────────────────────────────────────────────────────────┤
│  Methods:                                                               │
│    + new(window_handle) -> Result<Self>                                │
│    + create_buffer(size, usage, memory_usage) -> Result<Buffer>        │
│    + create_image(width, height, format, usage) -> Result<Image>       │
│    + create_shader(code: &[u8]) -> Result<vk::ShaderModule>            │
│    + allocate_command_buffer() -> Result<vk::CommandBuffer>            │
│    + submit(cmd_buf, wait_semaphores, signal_semaphores) -> Result<()> │
│    + wait_idle() -> Result<()>                                         │
│    + destroy()                                                          │
└────────────────────────────────────────────────────────────────────────┘
                    │ creates       │ creates       │ creates
         ┌──────────┴─────┬─────────┴──────┬───────┴────────┐
         ▼                ▼                ▼                ▼
┌─────────────────┐ ┌──────────────┐ ┌───────────────┐ ┌─────────────────┐
│   Swapchain     │ │ RenderPass   │ │   Pipeline    │ │ CommandBuffer   │
├─────────────────┤ ├──────────────┤ ├───────────────┤ ├─────────────────┤
│ - swapchain:    │ │ - render_    │ │ - pipeline:   │ │ - cmd_buf:      │
│   vk::Swapchain │ │   pass:      │ │   vk::Pipeline│ │   vk::CmdBuffer │
│ - images:       │ │   vk::Render │ │ - layout:     │ │ - state:        │
│   Vec<Image>    │ │   Pass       │ │   vk::Pipeline│ │   CmdBufState   │
│ - image_views   │ │ - frame_     │ │   Layout      │ │                 │
│ - extent        │ │   buffers:   │ │ - descriptor_ │ │                 │
│ - format        │ │   Vec<vk::   │ │   sets        │ │                 │
│                 │ │   Framebuffer│ │ - type:       │ │                 │
│                 │ │ - clear_color│ │   PipelineType│ │                 │
├─────────────────┤ ├──────────────┤ ├───────────────┤ ├─────────────────┤
│ + new()         │ │ + new()      │ │ + new()       │ │ + begin()       │
│ + acquire_      │ │ + begin()    │ │ + bind()      │ │ + end()         │
│   image()       │ │ + end()      │ │ + push_       │ │ + begin_render_ │
│ + present()     │ │ + recreate() │ │   constants() │ │   pass()        │
│ + recreate()    │ │              │ │ + bind_       │ │ + end_render_   │
│                 │ │              │ │   descriptor_ │ │   pass()        │
│                 │ │              │ │   set()       │ │ + bind_pipeline │
│                 │ │              │ │               │ │ + draw()        │
│                 │ │              │ │               │ │ + draw_indexed()│
└─────────────────┘ └──────────────┘ └───────────────┘ └─────────────────┘
```

## Data Flow Diagram

```
┌─────────────────────────────────────────────────────────────────────────┐
│                         Frame Rendering Flow                             │
└─────────────────────────────────────────────────────────────────────────┘

                            ┌──────────────────┐
                            │  Element Tree    │
                            │  (Virtual DOM)   │
                            └────────┬─────────┘
                                     │
                                     ▼
                   ┌─────────────────────────────────┐
                   │     Layout Engine (CPU)         │
                   │  - Flexbox/Grid calculation     │
                   │  - Text measurement             │
                   │  - Cache layout results         │
                   └────────┬────────────────────────┘
                            │ LayoutResult
                            ▼
                   ┌─────────────────────────────────┐
                   │  Element Processor (CPU)        │
                   │  - Traverse element tree        │
                   │  - Generate vertices/indices    │
                   │  - Batch by pipeline type       │
                   │  - Build DrawList               │
                   └────────┬────────────────────────┘
                            │ DrawList
                            ▼
    ┌──────────────────────────────────────────────────────┐
    │         Buffer Manager (CPU → GPU Upload)            │
    │  - Allocate vertex/index buffers                     │
    │  - Upload vertex data to GPU                         │
    │  - Upload index data to GPU                          │
    │  - Upload uniform data (projection matrix, etc.)     │
    └────────┬─────────────────────────────────────────────┘
             │ GPU Buffers
             ▼
    ┌──────────────────────────────────────────────────────┐
    │        Command Buffer Recording (CPU → GPU)          │
    │  - Begin render pass                                 │
    │  - For each DrawCall:                                │
    │    - Bind pipeline                                   │
    │    - Bind descriptor sets                            │
    │    - Set viewport/scissor                            │
    │    - Bind vertex/index buffers                       │
    │    - Push constants (transforms, colors)             │
    │    - Draw indexed                                    │
    │  - End render pass                                   │
    └────────┬─────────────────────────────────────────────┘
             │ CommandBuffer
             ▼
    ┌──────────────────────────────────────────────────────┐
    │         GPU Execution (Parallel)                     │
    │  - Vertex shader (transform to clip space)           │
    │  - Rasterization                                     │
    │  - Fragment shader (color, SDF, etc.)                │
    │  - Depth test, blending                              │
    │  - Write to framebuffer                              │
    └────────┬─────────────────────────────────────────────┘
             │ Rendered Image
             ▼
    ┌──────────────────────────────────────────────────────┐
    │          Swapchain Present                           │
    │  - Submit command buffer to queue                    │
    │  - Wait for GPU to finish                            │
    │  - Present image to screen                           │
    │  - Acquire next swapchain image                      │
    └──────────────────────────────────────────────────────┘
```

## Patch-Based Update Flow

```
┌─────────────────────────────────────────────────────────────────────────┐
│                      Incremental Update (Patches)                        │
└─────────────────────────────────────────────────────────────────────────┘

                    ┌──────────────────────┐
                    │  Old Element Tree    │
                    └───────┬──────────────┘
                            │
                            ├──────────┐
                            │          │
                            ▼          ▼
                   ┌────────────┐  ┌──────────────────┐
                   │   Differ   │  │ New Element Tree │
                   └────┬───────┘  └──────────────────┘
                        │ Diff Algorithm (keyed, LIS)
                        ▼
                   ┌─────────────────────────────────┐
                   │       PatchSet                  │
                   │  - SetText                      │
                   │  - SetAttr, SetStyle            │
                   │  - InsertChild, RemoveChild     │
                   │  - ReplaceSubtree               │
                   └────────┬────────────────────────┘
                            │
                            ▼
           ┌────────────────────────────────────────────┐
           │   Identify Affected Elements               │
           │  - Mark dirty regions (bounding boxes)     │
           │  - Mark affected layout nodes              │
           └────────┬───────────────────────────────────┘
                    │
                    ▼
           ┌────────────────────────────────────────────┐
           │   Partial Layout Update                    │
           │  - Re-layout only affected subtrees        │
           │  - Reuse cached layout for clean subtrees  │
           └────────┬───────────────────────────────────┘
                    │
                    ▼
           ┌────────────────────────────────────────────┐
           │   Partial Element Processing               │
           │  - Regenerate DrawList for dirty regions   │
           │  - Reuse cached geometry for clean regions │
           └────────┬───────────────────────────────────┘
                    │
                    ▼
           ┌────────────────────────────────────────────┐
           │   Selective GPU Upload                     │
           │  - Upload only changed vertex data         │
           │  - Update only affected buffers            │
           └────────┬───────────────────────────────────┘
                    │
                    ▼
           ┌────────────────────────────────────────────┐
           │   Optimized Rendering                      │
           │  - Use scissor rects for dirty regions     │
           │  - Skip unaffected areas                   │
           │  - Render only changed parts               │
           └────────────────────────────────────────────┘
```

## Pipeline Type Decision Tree

```
Element
  │
  ├─ Is Text?
  │    └─ Use TextPipeline (SDF)
  │
  ├─ Has Rounded Corners?
  │    └─ Use RoundedRectPipeline (SDF)
  │
  ├─ Has Background Image?
  │    └─ Use TexturedPipeline
  │
  ├─ Has Gradient?
  │    └─ Use GradientPipeline
  │
  ├─ Has Shadow?
  │    └─ Use ShadowPipeline (multi-pass)
  │
  └─ Default
       └─ Use SolidColorPipeline
```

## Memory Layout

### Vertex Buffer Layout

```
┌─────────────────────────────────────────────────────────┐
│                  Vertex Buffer (per frame)              │
├─────────────────────────────────────────────────────────┤
│  Vertex 0:  [ pos.x, pos.y, uv.x, uv.y, color (RGBA) ]  │
│  Vertex 1:  [ pos.x, pos.y, uv.x, uv.y, color (RGBA) ]  │
│  ...                                                     │
│  Vertex N:  [ pos.x, pos.y, uv.x, uv.y, color (RGBA) ]  │
├─────────────────────────────────────────────────────────┤
│  Total size: N * sizeof(Vertex)                         │
│  sizeof(Vertex) = 2*f32 + 2*f32 + 4*u8 = 20 bytes       │
└─────────────────────────────────────────────────────────┘
```

### Index Buffer Layout

```
┌─────────────────────────────────────────────────────────┐
│                   Index Buffer (per frame)              │
├─────────────────────────────────────────────────────────┤
│  Triangle 0:  [ i0, i1, i2 ]                            │
│  Triangle 1:  [ i3, i4, i5 ]                            │
│  ...                                                     │
│  Triangle M:  [ ..., ..., ... ]                         │
├─────────────────────────────────────────────────────────┤
│  Total size: M * 3 * sizeof(u32)                        │
└─────────────────────────────────────────────────────────┘
```

### Uniform Buffer Layout

```
┌─────────────────────────────────────────────────────────┐
│               Uniform Buffer (per frame)                │
├─────────────────────────────────────────────────────────┤
│  projection: mat4 (16 floats)    // Orthographic       │
│  viewport: vec4                  // x, y, w, h         │
│  time: f32                       // For animations     │
│  _padding: [f32; 3]              // Alignment          │
├─────────────────────────────────────────────────────────┤
│  Total size: (16 + 4 + 1 + 3) * 4 = 96 bytes           │
│  Aligned to 256 bytes (UBO alignment)                   │
└─────────────────────────────────────────────────────────┘
```

## Resource Lifetime

```
Application Lifetime:
    ├─ VulkanDevice (instance, device, queues)
    ├─ DescriptorPool
    ├─ PipelineCache
    └─ CommandPool

Window Lifetime:
    ├─ Swapchain
    ├─ RenderPass
    └─ Framebuffers

Frame Lifetime (3x for triple buffering):
    ├─ Vertex Buffers
    ├─ Index Buffers
    ├─ Uniform Buffers
    ├─ Command Buffers
    └─ Semaphores/Fences

Element Tree Lifetime:
    ├─ Font Atlas (regenerate when full)
    ├─ Image Textures (cache until evicted)
    └─ Layout Cache (clear on tree change)
```

## Synchronization

```
Frame N-2      Frame N-1      Frame N        Frame N+1
   │              │              │              │
   │              │              │              │
   ▼              ▼              ▼              ▼
[CPU Layout] [CPU Layout] [CPU Layout] [CPU Layout]
   │              │              │              │
   ▼              ▼              ▼              ▼
[CPU Process][CPU Process][CPU Process][CPU Process]
   │              │              │              │
   ▼              ▼              ▼              ▼
[GPU Render] [GPU Render] [GPU Render] [GPU Render]
   │              │              │              │
   └──────────────┴──────────────┴──────────────┘
           (Fence per frame prevents overwrite)

Synchronization primitives:
  - imageAvailableSemaphore (swapchain ready)
  - renderFinishedSemaphore (rendering done)
  - inFlightFence (frame N resources available)
```
