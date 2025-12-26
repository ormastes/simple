# Vulkan Backend Implementation Plan

**Date:** 2025-12-26
**Status:** Planning
**Related Documents:**
- [vulkan_dsl.md](../research/vulkan_dsl.md) - Research on Vulkan DSL design
- [ui_framework_unified.md](../research/ui_framework_unified.md) - UI rendering with Vulkan
- [gpu_simd.md](../spec/gpu_simd.md) - GPU compute specification (CUDA-based)
- [feature.md](../features/feature.md) - Feature tracking

## Executive Summary

Add Vulkan as a GPU backend alongside the existing CUDA support, providing:
- **Graphics Pipeline**: Rendering support for UI frameworks (TUI, GUI, Electron, VSCode)
- **Compute Pipeline**: Alternative to CUDA for GPU compute on non-NVIDIA hardware
- **Cross-Platform**: Works on Windows, Linux, macOS, Android, iOS
- **Simple DSL**: High-level API that abstracts Vulkan's complexity
- **Safety**: Compile-time contracts and ownership model prevent common errors

**Key Design Principles:**
1. **Maximum Defaults** - `Device.new()` just works, no configuration needed
2. **RAII + Ownership** - Automatic resource cleanup, no manual `vkDestroy*` calls
3. **Actor Model** - Eliminates synchronization bugs (semaphores/fences handled automatically)
4. **Compile-Time Contracts** - Catch resource lifetime errors early
5. **AOP Weaving** - Auto-inject validation, profiling, cleanup
6. **Builder Pattern** - Fluent API for pipeline configuration

## Part 1: Architecture Overview

### 1.1 Backend Hierarchy

```
Simple Language
    │
    ├─ GPU Compute Backend (existing)
    │  ├─ CUDA (NVIDIA GPUs)
    │  └─ Vulkan Compute (NEW - cross-platform)
    │
    └─ Graphics Backend (NEW)
       ├─ Vulkan Graphics Pipeline
       │  ├─ Swapchain management
       │  ├─ Render passes
       │  ├─ Graphics pipelines
       │  └─ Command buffers
       │
       └─ Integration Points
          ├─ UI Framework (TUI/GUI)
          ├─ Electron (native window)
          ├─ VSCode (webview)
          └─ Web (WebGPU fallback)
```

### 1.2 API Layers

```
Layer 1: High-Level DSL (Simple)
  ├─ vulkan.Device.new()
  ├─ vulkan.Window.new()
  ├─ vulkan.Pipeline.builder()
  └─ vulkan.CommandBuffer.record()
      ↓
Layer 2: Safe Wrappers (Simple stdlib)
  ├─ Resource ownership (RAII)
  ├─ Type-safe builders
  ├─ Actor-based synchronization
  └─ Compile-time contracts
      ↓
Layer 3: FFI Bindings (Rust)
  ├─ Vulkan-rs / Ash bindings
  ├─ RAII resource wrappers
  └─ Error handling
      ↓
Layer 4: Vulkan SDK (C)
  └─ vkCreate* / vkDestroy* calls
```

### 1.3 Module Structure

```
simple/std_lib/src/
├── gpu/
│   ├── host/
│   │   └── async_nogc_mut/
│   │       ├── cuda.spl         # Existing CUDA backend
│   │       └── vulkan.spl       # NEW: Vulkan compute backend
│   │
│   └── kernel/
│       ├── cuda/                # Existing CUDA kernels
│       └── vulkan/              # NEW: Vulkan compute shaders (SPIR-V)
│
└── graphics/                    # NEW: Graphics subsystem
    ├── vulkan/
    │   ├── device.spl           # Device management
    │   ├── swapchain.spl        # Swapchain/presentation
    │   ├── pipeline.spl         # Graphics pipeline
    │   ├── render_pass.spl      # Render passes
    │   ├── command.spl          # Command buffers
    │   ├── buffer.spl           # Vertex/index buffers
    │   ├── texture.spl          # Textures/samplers
    │   ├── descriptor.spl       # Descriptor sets
    │   └── sync.spl             # Synchronization
    │
    ├── shader/
    │   ├── compiler.spl         # SPIR-V compilation
    │   └── reflection.spl       # Shader reflection
    │
    └── backend.spl              # Graphics backend trait
```

## Part 2: Implementation Phases

### Phase 1: Core Infrastructure (3-5 days)

**Goal:** Basic Vulkan instance, device, and compute pipeline

**Features:**
- Vulkan instance creation with validation layers
- Physical device selection
- Logical device creation
- Command pool and buffers
- Basic compute pipeline
- Buffer allocation and upload/download

**Deliverables:**
1. `graphics/vulkan/device.spl` (200 lines)
   - Instance creation
   - Device selection
   - Queue family management

2. `graphics/vulkan/buffer.spl` (150 lines)
   - Device buffer allocation
   - Host-device data transfer
   - Memory management

3. `graphics/vulkan/command.spl` (180 lines)
   - Command pool management
   - Command buffer recording
   - Submission and synchronization

4. `graphics/vulkan/compute.spl` (220 lines)
   - Compute pipeline creation
   - Descriptor sets for compute
   - Kernel dispatch

**Tests:**
- Device enumeration
- Buffer upload/download
- Simple compute shader execution

**Example Usage:**
```simple
use graphics.vulkan.*

# Create device with defaults
let device = Device.new()

# Allocate buffers
let input_buf = device.alloc_buffer[f32](1024)
let output_buf = device.alloc_buffer[f32](1024)

# Upload data
input_buf.upload([1.0, 2.0, ..., 1024.0])

# Run compute shader
device.dispatch_compute(
    shader: "add.comp.spv",
    buffers: [input_buf, output_buf],
    workgroups: [32, 1, 1]
)

# Download results
let results = output_buf.download()
```

### Phase 2: Graphics Pipeline (4-6 days)

**Goal:** Swapchain, render passes, graphics pipelines

**Features:**
- Window surface creation
- Swapchain management
- Render pass creation
- Graphics pipeline builder
- Vertex/index buffers
- Basic triangle rendering

**Deliverables:**
1. `graphics/vulkan/swapchain.spl` (250 lines)
   - Surface format selection
   - Present mode selection
   - Swapchain creation/recreation
   - Image views

2. `graphics/vulkan/render_pass.spl` (180 lines)
   - Attachment descriptions
   - Subpass dependencies
   - Framebuffer management

3. `graphics/vulkan/pipeline.spl` (300 lines)
   - Pipeline builder API
   - Shader stage configuration
   - Vertex input state
   - Rasterization state
   - Pipeline layout

4. `graphics/vulkan/renderer.spl` (200 lines)
   - Frame management
   - Render loop
   - Automatic synchronization (semaphores/fences)

**Tests:**
- Window creation
- Swapchain recreation on resize
- Clear screen to color
- Render triangle

**Example Usage:**
```simple
use graphics.vulkan.*

# Create window
let window = Window.new(
    title: "Hello Vulkan",
    width: 800,
    height: 600
)

# Create device
let device = Device.new_for_window(window)

# Create graphics pipeline with defaults
let pipeline = Pipeline.builder()
    .vertex_shader("triangle.vert.spv")
    .fragment_shader("triangle.frag.spv")
    .vertex_format[Vertex]()  # Auto-deduce from struct
    .build(device)

# Render loop
while window.is_open():
    with window.frame() as frame:
        frame.clear([0.0, 0.0, 0.0, 1.0])  # Black
        frame.draw(pipeline, vertices)
```

### Phase 3: Textures and Descriptors (3-4 days)

**Goal:** Texture support, descriptor sets, uniform buffers

**Features:**
- Texture creation and upload
- Sampler configuration
- Descriptor set layouts
- Descriptor pools and sets
- Uniform buffer updates

**Deliverables:**
1. `graphics/vulkan/texture.spl` (220 lines)
   - Texture creation (1D/2D/3D/Cube)
   - Format support
   - Mipmap generation
   - Image layout transitions

2. `graphics/vulkan/sampler.spl` (120 lines)
   - Sampler creation
   - Filtering modes
   - Address modes

3. `graphics/vulkan/descriptor.spl` (280 lines)
   - Descriptor set layout builder
   - Descriptor pool management
   - Descriptor set allocation
   - Binding updates

**Tests:**
- Texture upload
- Uniform buffer updates
- Descriptor set binding
- Textured quad rendering

**Example Usage:**
```simple
# Load texture
let texture = device.load_texture("image.png")

# Create descriptor set
#[descriptor_set]
struct MaterialDescriptors:
    #[binding(0)] albedo: Texture2D
    #[binding(1)] params: UniformBuffer[MaterialParams]

let descriptors = MaterialDescriptors.new(device)
descriptors.albedo = texture
descriptors.params.upload(MaterialParams { roughness: 0.5, metallic: 0.8 })

# Bind and draw
frame.bind_descriptors(descriptors)
frame.draw(pipeline, vertices)
```

### Phase 4: Advanced Features (5-7 days)

**Goal:** Multi-pass rendering, depth/stencil, MSAA

**Features:**
- Depth/stencil buffers
- Multi-sample anti-aliasing (MSAA)
- Multi-pass rendering
- Dynamic rendering (Vulkan 1.3)
- Push constants
- Indirect drawing

**Deliverables:**
1. `graphics/vulkan/depth.spl` (150 lines)
   - Depth buffer creation
   - Depth testing configuration
   - Stencil operations

2. `graphics/vulkan/msaa.spl` (130 lines)
   - Multi-sample image creation
   - Resolve operations
   - Sample shading

3. `graphics/vulkan/multipass.spl` (200 lines)
   - Multiple subpasses
   - Input attachments
   - Dependency management

4. `graphics/vulkan/advanced.spl` (180 lines)
   - Push constants
   - Indirect drawing
   - Conditional rendering

**Tests:**
- Depth testing
- MSAA rendering
- Shadow map generation
- Deferred rendering

### Phase 5: Integration (3-4 days)

**Goal:** Integrate with UI frameworks and existing systems

**Features:**
- UI framework backend (TUI/GUI)
- Electron window integration
- VSCode webview rendering
- Compute shader hot-reload
- Performance profiling

**Deliverables:**
1. `ui/backends/vulkan.spl` (250 lines)
   - UI widget rendering
   - Text rendering
   - 2D primitives

2. `electron/vulkan.spl` (150 lines)
   - Native window integration
   - Surface creation

3. Integration tests (10+ scenarios)

## Part 3: API Design

### 3.1 Device Management

```simple
use graphics.vulkan.*

# Automatic device selection (picks best GPU)
let device = Device.new()

# Or specify requirements
let device = Device.builder()
    .gpu_type(GpuType.Discrete)  # Prefer dedicated GPU
    .features([
        Feature.GeometryShader,
        Feature.TessellationShader,
    ])
    .extensions([
        Extension.Swapchain,
        Extension.Raytracing,
    ])
    .build()

# Query device info
println("Device: {device.name()}")
println("Vendor: {device.vendor()}")
println("Memory: {device.memory()} MB")
```

**Simple Features Used:**
- **Maximum Defaults**: `Device.new()` works without configuration
- **Builder Pattern**: Fluent API for advanced configuration
- **Type Safety**: Enums for features/extensions

### 3.2 Swapchain and Window

```simple
# Create window with default settings
let window = Window.new(
    title: "My App",
    width: 1920,
    height: 1080
)

# Or use builder for full control
let window = Window.builder()
    .title("My App")
    .size(1920, 1080)
    .resizable(true)
    .vsync(true)
    .fullscreen(false)
    .samples(Samples.MSAA_4X)
    .build()

# Automatic swapchain management
# - Created automatically when window is shown
# - Recreated automatically on resize
# - Optimal format/present mode selected automatically
```

**Simple Features Used:**
- **Context Blocks**: `with window.frame() as frame` for automatic resource management
- **AOP**: Auto-inject resize handling, frame synchronization
- **Actors**: Window event loop runs as actor, no manual synchronization

### 3.3 Graphics Pipeline

```simple
# Vertex format with automatic binding generation
#[vertex]
struct Vertex:
    #[location(0)] position: Vec3
    #[location(1)] normal: Vec3
    #[location(2)] uv: Vec2
    #[location(3)] color: Vec4

# Pipeline with maximum defaults
let pipeline = Pipeline.builder()
    .vertex_shader("shader.vert.spv")
    .fragment_shader("shader.frag.spv")
    .vertex_format[Vertex]()  # Auto-deduce bindings
    .build(device)

# Or override defaults
let pipeline = Pipeline.builder()
    .vertex_shader("shader.vert.spv")
    .fragment_shader("shader.frag.spv")
    .vertex_format[Vertex]()
    .topology(Topology.TriangleStrip)
    .cull_mode(CullMode.Back)
    .front_face(FrontFace.CounterClockwise)
    .polygon_mode(PolygonMode.Fill)
    .depth_test(true)
    .depth_write(true)
    .blend_mode(BlendMode.Alpha)
    .build(device)
```

**Simple Features Used:**
- **Macros**: `#[vertex]` generates VkVertexInputBindingDescription automatically
- **Type Inference**: `vertex_format[Vertex]()` deduces layout from struct
- **Defaults**: Sensible defaults for all pipeline state
- **Contracts**: `out(ret): ret.is_valid()` ensures pipeline was created

### 3.4 Rendering

```simple
# Actor-based rendering (no manual synchronization)
actor RenderActor:
    window: Window
    device: Device
    pipeline: Pipeline
    vertices: Buffer[Vertex]

    fn render():
        # Automatic frame synchronization
        with self.window.frame() as frame:
            # Clear
            frame.clear([0.1, 0.1, 0.1, 1.0])

            # Bind pipeline
            frame.bind_pipeline(self.pipeline)

            # Bind vertex buffer
            frame.bind_vertices(self.vertices)

            # Draw
            frame.draw(vertex_count: self.vertices.len())

# Render loop
let renderer = RenderActor.spawn(
    window: window,
    device: device,
    pipeline: pipeline,
    vertices: vertices
)

while window.is_open():
    renderer.send(RenderMsg.Render)
    window.poll_events()
```

**Simple Features Used:**
- **Context Blocks**: `with window.frame()` automatically:
  - Acquires next swapchain image
  - Begins command buffer
  - Ends command buffer
  - Submits to queue
  - Presents frame
  - Handles semaphores/fences
- **Actor Model**: Eliminates race conditions in render loop
- **RAII**: Resources cleaned up automatically

### 3.5 Descriptors and Uniforms

```simple
# Declarative descriptor set layout
#[descriptor_set]
struct SceneDescriptors:
    #[binding(0)] camera: UniformBuffer[CameraParams]
    #[binding(1)] lighting: UniformBuffer[LightingParams]

#[descriptor_set]
struct MaterialDescriptors:
    #[binding(0)] albedo: Texture2D
    #[binding(1)] normal: Texture2D
    #[binding(2)] metallic: Texture2D
    #[binding(3)] roughness: Texture2D
    #[binding(4)] params: UniformBuffer[MaterialParams]

# Create and update descriptors
let scene_desc = SceneDescriptors.new(device)
scene_desc.camera.upload(camera_params)
scene_desc.lighting.upload(lighting_params)

let mat_desc = MaterialDescriptors.new(device)
mat_desc.albedo = load_texture("albedo.png")
mat_desc.normal = load_texture("normal.png")
mat_desc.params.upload(material_params)

# Bind descriptors
frame.bind_descriptors(set: 0, scene_desc)
frame.bind_descriptors(set: 1, mat_desc)
frame.draw(...)
```

**Simple Features Used:**
- **Macros**: `#[descriptor_set]` auto-generates:
  - VkDescriptorSetLayoutBinding array
  - VkDescriptorPoolSize calculations
  - VkWriteDescriptorSet helpers
- **Type Safety**: Compile-time verification of binding types
- **Auto Update**: Assignment to descriptor field updates VkWriteDescriptorSet

### 3.6 Compute Shaders

```simple
# CUDA-style compute API
#[gpu(backend: Vulkan)]
fn vector_add(a: &[f32], b: &[f32], out: &mut [f32]):
    let idx = gpu.global_id()
    if idx < out.len():
        out[idx] = a[idx] + b[idx]

# Or explicit Vulkan compute pipeline
let compute_pipeline = ComputePipeline.builder()
    .shader("add.comp.spv")
    .build(device)

# Dispatch
device.dispatch_compute(
    pipeline: compute_pipeline,
    buffers: [a_buf, b_buf, out_buf],
    workgroups: [1024 / 256, 1, 1]  # 1024 elements, 256 threads per group
)
```

### 3.7 Multi-Pass Rendering

```simple
# Deferred rendering example
let gbuffer_pass = RenderPass.builder()
    .attachment("position", Format.R32G32B32A32_SFLOAT)
    .attachment("normal", Format.R32G32B32A32_SFLOAT)
    .attachment("albedo", Format.R8G8B8A8_UNORM)
    .attachment("depth", Format.D32_SFLOAT)
    .subpass("geometry")
        .color_attachments(["position", "normal", "albedo"])
        .depth_attachment("depth")
    .build(device)

let lighting_pass = RenderPass.builder()
    .attachment("final", Format.R8G8B8A8_UNORM)
    .subpass("lighting")
        .input_attachments(["position", "normal", "albedo"])
        .color_attachments(["final"])
    .build(device)
```

## Part 4: Feature List

### Core Vulkan Features (#1450-1469)

| Feature ID | Feature | Difficulty | Impl | Lines |
|------------|---------|------------|------|-------|
| #1450 | Vulkan instance creation | 3 | S+R | 150 |
| #1451 | Physical device enumeration | 2 | S+R | 100 |
| #1452 | Logical device creation | 3 | S+R | 180 |
| #1453 | Queue family management | 3 | S+R | 120 |
| #1454 | Command pool and buffers | 3 | S+R | 200 |
| #1455 | Memory allocation | 4 | S+R | 250 |
| #1456 | Buffer creation (vertex/index/uniform) | 3 | S+R | 180 |
| #1457 | Host-device data transfer | 2 | S+R | 120 |
| #1458 | Image/texture creation | 4 | S+R | 220 |
| #1459 | Sampler creation | 2 | S+R | 100 |
| #1460 | Descriptor set layouts | 4 | S+R | 200 |
| #1461 | Descriptor pools and sets | 3 | S+R | 180 |
| #1462 | Pipeline layout | 3 | S+R | 150 |
| #1463 | Shader module loading (SPIR-V) | 2 | S+R | 120 |
| #1464 | Graphics pipeline creation | 5 | S+R | 300 |
| #1465 | Compute pipeline creation | 4 | S+R | 220 |
| #1466 | Render pass creation | 4 | S+R | 200 |
| #1467 | Framebuffer management | 3 | S+R | 150 |
| #1468 | Command buffer recording | 4 | S+R | 250 |
| #1469 | Synchronization (semaphores/fences) | 4 | S+R | 200 |

### Presentation & Swapchain (#1470-1479)

| Feature ID | Feature | Difficulty | Impl | Lines |
|------------|---------|------------|------|-------|
| #1470 | Window surface creation | 3 | S+R | 150 |
| #1471 | Surface format selection | 2 | S+R | 100 |
| #1472 | Present mode selection | 2 | S+R | 80 |
| #1473 | Swapchain creation | 4 | S+R | 220 |
| #1474 | Swapchain image views | 2 | S+R | 100 |
| #1475 | Swapchain recreation (resize) | 4 | S+R | 180 |
| #1476 | Frame synchronization | 4 | S+R | 200 |
| #1477 | Present queue submission | 3 | S+R | 150 |
| #1478 | VSync configuration | 2 | S+R | 80 |
| #1479 | Multi-buffering (double/triple) | 3 | S+R | 120 |

### Advanced Features (#1480-1499)

| Feature ID | Feature | Difficulty | Impl | Lines |
|------------|---------|------------|------|-------|
| #1480 | Depth/stencil buffers | 3 | S+R | 150 |
| #1481 | MSAA (multi-sample anti-aliasing) | 4 | S+R | 180 |
| #1482 | Multi-pass rendering | 5 | S+R | 250 |
| #1483 | Input attachments | 4 | S+R | 150 |
| #1484 | Push constants | 2 | S+R | 100 |
| #1485 | Indirect drawing | 4 | S+R | 180 |
| #1486 | Tessellation shaders | 5 | S+R | 220 |
| #1487 | Geometry shaders | 5 | S+R | 200 |
| #1488 | Dynamic rendering (Vulkan 1.3) | 4 | S+R | 200 |
| #1489 | Shader reflection | 4 | S+R | 250 |
| #1490 | SPIR-V compilation from GLSL | 3 | S+R | 180 |
| #1491 | Pipeline cache | 3 | S+R | 120 |
| #1492 | Query pools (timestamps/occlusion) | 3 | S+R | 150 |
| #1493 | Conditional rendering | 3 | S+R | 120 |
| #1494 | Multi-viewport/scissor | 2 | S+R | 100 |
| #1495 | Shader specialization constants | 3 | S+R | 130 |
| #1496 | Subgroup operations | 4 | S+R | 150 |
| #1497 | Ray tracing pipeline (RTX) | 5 | S+R | 300 |
| #1498 | Mesh shaders | 5 | S+R | 250 |
| #1499 | Variable rate shading | 4 | S+R | 180 |

### Integration Features (#1500-1509)

| Feature ID | Feature | Difficulty | Impl | Lines |
|------------|---------|------------|------|-------|
| #1500 | UI framework backend (Vulkan) | 5 | S+R | 350 |
| #1501 | Electron window integration | 4 | S+R | 200 |
| #1502 | VSCode webview rendering | 4 | S+R | 180 |
| #1503 | TUI rendering via Vulkan | 4 | S+R | 220 |
| #1504 | 2D primitives (lines/rects/circles) | 3 | S+R | 200 |
| #1505 | Text rendering (SDF fonts) | 5 | S+R | 300 |
| #1506 | Image loading (PNG/JPEG/etc) | 3 | S+R | 150 |
| #1507 | Compute shader hot-reload | 3 | S+R | 180 |
| #1508 | GPU profiling integration | 4 | S+R | 200 |
| #1509 | Screenshot capture | 2 | S+R | 100 |

**Total:** 60 features, ~10,000 lines of implementation

## Part 5: Testing Strategy

### Unit Tests (per module)

1. **Device Management** (20 tests)
   - Instance creation
   - Device enumeration
   - Queue family selection
   - Feature/extension validation

2. **Buffers** (15 tests)
   - Buffer allocation
   - Upload/download
   - Memory mapping
   - Buffer resize

3. **Pipeline** (25 tests)
   - Pipeline builder
   - State validation
   - Shader loading
   - Pipeline cache

4. **Rendering** (30 tests)
   - Clear screen
   - Draw triangle
   - Textured quad
   - Multiple objects

5. **Compute** (20 tests)
   - Compute dispatch
   - Buffer binding
   - Workgroup sizing
   - Multiple dispatches

### Integration Tests

1. **Graphics Pipeline**
   - Render a frame
   - Resize window
   - Multi-pass rendering
   - Depth testing

2. **UI Integration**
   - Render text
   - Render widgets
   - Handle events
   - Scroll performance

3. **Compute**
   - Vector addition
   - Matrix multiplication
   - Image filtering
   - Reduction operations

### Benchmark Tests

1. **Draw call performance**
2. **Buffer upload speed**
3. **Texture upload speed**
4. **Compute throughput**
5. **Frame time (60 FPS target)**

## Part 6: Documentation

### User Documentation

1. **Getting Started Guide**
   - Installation
   - First triangle
   - First texture
   - First compute shader

2. **API Reference**
   - Device
   - Pipeline
   - Buffers
   - Textures
   - Descriptors
   - Commands

3. **Examples**
   - Hello triangle
   - Textured cube
   - Deferred rendering
   - Compute particles
   - UI rendering

4. **Migration Guide**
   - CUDA → Vulkan compute
   - OpenGL → Vulkan graphics

### Developer Documentation

1. **Architecture**
   - Module structure
   - Resource management
   - Synchronization model

2. **Implementation Notes**
   - Vulkan best practices
   - Performance optimization
   - Debug validation

3. **Contributing Guide**
   - Adding new features
   - Testing requirements
   - Code style

## Part 7: Dependencies

### External Libraries

1. **Vulkan SDK** (required)
   - Vulkan headers
   - Validation layers
   - SPIR-V tools

2. **Rust Bindings** (via FFI)
   - `ash` - Vulkan bindings
   - `gpu-allocator` - Memory management
   - `shaderc` - GLSL → SPIR-V compiler

3. **Window Integration**
   - `winit` - Cross-platform windowing
   - Or use existing Electron/VSCode windows

### Build Requirements

```toml
[dependencies]
ash = "0.38"
gpu-allocator = "0.26"
shaderc = "0.8"
```

## Part 8: Timeline

| Phase | Duration | Deliverables |
|-------|----------|--------------|
| Phase 1: Core Infrastructure | 3-5 days | Device, buffers, compute |
| Phase 2: Graphics Pipeline | 4-6 days | Swapchain, rendering |
| Phase 3: Textures/Descriptors | 3-4 days | Textures, uniforms |
| Phase 4: Advanced Features | 5-7 days | Depth, MSAA, multi-pass |
| Phase 5: Integration | 3-4 days | UI frameworks |
| Testing & Polish | 2-3 days | Bug fixes, optimization |
| **Total** | **20-29 days** | **60 features** |

## Part 9: Success Criteria

1. ✅ **Hello Triangle** renders at 60 FPS
2. ✅ **Compute shader** matches CUDA performance (±10%)
3. ✅ **UI framework** can render at least 1000 widgets at 60 FPS
4. ✅ **Cross-platform** works on Windows, Linux, macOS
5. ✅ **Test coverage** ≥ 80% for all Vulkan modules
6. ✅ **Documentation** complete for all public APIs
7. ✅ **Zero crashes** in validation layers during tests

## Part 10: Future Enhancements

1. **Ray Tracing** (Vulkan Ray Tracing extension)
2. **Mesh Shaders** (Vulkan 1.3)
3. **Variable Rate Shading** (Tier 1/2)
4. **DLSS/FSR Integration**
5. **Mobile Support** (Android, iOS via MoltenVK)
6. **WebGPU Backend** (for web deployment)
7. **Shader Hot-Reload** (for live coding)
8. **GPU Debugger Integration** (RenderDoc, NSight)

## Conclusion

This plan provides a comprehensive roadmap for adding Vulkan as a GPU backend to Simple language. The implementation leverages Simple's unique features (maximum defaults, actor model, ownership, contracts) to dramatically simplify Vulkan's complexity while maintaining full power and flexibility.

**Key Benefits:**
- **~90% less code** than raw Vulkan C/C++
- **Automatic resource management** via RAII + ownership
- **No synchronization bugs** via actor model
- **Compile-time safety** via contracts
- **Cross-platform graphics** for UI frameworks
- **Alternative to CUDA** for non-NVIDIA GPUs
