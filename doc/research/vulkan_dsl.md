# Vulkan DSL Research: Why Vulkan is Hard and How Simple Can Help

**Date:** 2025-12-26
**Status:** Research Document
**Related:** [ui_framework_unified.md](ui_framework_unified.md), [feature.md](../features/feature.md) #1369-1378, [sdn.md](../spec/sdn.md)

## Executive Summary

Vulkan is notoriously difficult to use due to extreme verbosity, manual resource management, synchronization complexity, and lack of sensible defaults. This document analyzes why Vulkan is hard and proposes DSL candidates that leverage Simple's unique features to dramatically simplify GPU programming.

**Key Simple Features That Help:**
1. **Maximum Defaults** - Zero-config initialization (`Device.new()` just works)
2. **`with` Context Blocks** - Automatic resource management (`with window.frame() as frame`)
3. **Underscore Literals** - Compact coordinate types (`100_200_loc`, `1_0_0_vec3`)
4. **Custom Type Literals** - User-defined types with underscore syntax (`1_0_0_0_quat`)
5. **Multi-Value Units** - Type-safe dimensional vectors (`100_200_m2`, `5_10_m_per_s2`)
6. **SDN Configuration** - Declarative config with functional defaults
7. **Functional Defaults** - Runtime-computed optimal values (`@fn(device) => ...`)
8. **Actor Model** - Eliminates synchronization bugs
9. **Immutable Objects** - Prevents data races in concurrent GPU/CPU
10. **Compile-Time Contracts** - Catch resource lifetime errors early
11. **AOP Weaving** - Auto-inject validation, profiling, cleanup
12. **Macros** - Reduce typing for repetitive patterns (`#[vertex]` auto-generates bindings)

---

## 1. Why Vulkan is Hard: Problem Analysis

### 1.1 Problem Categories

| Category | Vulkan Lines | Description | Simple Solution |
|----------|-------------|-------------|-----------------|
| **Verbosity** | ~1000 to draw triangle | Explicit everything | Smart defaults |
| **Resource Lifecycle** | Manual alloc/free | Memory leaks, use-after-free | Ownership + contracts |
| **Synchronization** | Semaphores, fences, barriers | Race conditions, deadlocks | Actor model |
| **Pipeline State** | 50+ configuration options | Easy to forget settings | Defaults + validation |
| **Descriptor Sets** | Manual binding management | Off-by-one errors | Reflection macros |
| **Memory Management** | Device/host memory, alignment | Complex allocation | Auto memory pools |
| **Command Buffers** | Record, submit, reuse | Lifetime confusion | RAII + AOP cleanup |
| **Validation** | Optional layers | Runtime crashes | Compile-time contracts |
| **Shader Interface** | SPIR-V, manual layout | Type mismatches | Type-safe bindings |

### 1.2 Vulkan "Hello Triangle" Complexity

```
Vulkan Hello Triangle (C/C++)
├── Instance creation (~50 lines)
│   ├── VkApplicationInfo
│   ├── VkInstanceCreateInfo
│   ├── Extension enumeration
│   └── Validation layer setup
├── Physical device selection (~80 lines)
│   ├── Enumerate devices
│   ├── Check queue families
│   ├── Check device extensions
│   └── Query surface capabilities
├── Logical device creation (~60 lines)
│   ├── Queue create info
│   ├── Device features
│   └── Device extensions
├── Swapchain creation (~100 lines)
│   ├── Surface format selection
│   ├── Present mode selection
│   ├── Extent calculation
│   └── Image view creation
├── Render pass (~50 lines)
│   ├── Attachment descriptions
│   ├── Subpass description
│   └── Subpass dependencies
├── Graphics pipeline (~200 lines)
│   ├── Shader modules (2x)
│   ├── Vertex input state
│   ├── Input assembly state
│   ├── Viewport state
│   ├── Rasterization state
│   ├── Multisample state
│   ├── Color blend state
│   └── Pipeline layout
├── Framebuffers (~30 lines)
├── Command pool & buffers (~50 lines)
├── Sync objects (~40 lines)
│   ├── Semaphores (image available)
│   ├── Semaphores (render finished)
│   └── Fences (in-flight frames)
├── Render loop (~100 lines)
│   ├── Acquire image
│   ├── Record commands
│   ├── Submit queue
│   └── Present image
└── Cleanup (~100 lines)
    ├── Wait device idle
    └── Destroy all objects in reverse order

TOTAL: ~800-1000 lines for a triangle
```

### 1.3 Specific Pain Points

#### 1.3.1 Explicit Everything (No Defaults)

```c
// Vulkan: Must specify EVERYTHING
VkPipelineRasterizationStateCreateInfo rasterizer = {
    .sType = VK_STRUCTURE_TYPE_PIPELINE_RASTERIZATION_STATE_CREATE_INFO,
    .pNext = NULL,
    .flags = 0,
    .depthClampEnable = VK_FALSE,           // Almost always false
    .rasterizerDiscardEnable = VK_FALSE,    // Almost always false
    .polygonMode = VK_POLYGON_MODE_FILL,    // Almost always fill
    .cullMode = VK_CULL_MODE_BACK_BIT,      // Common default
    .frontFace = VK_FRONT_FACE_CLOCKWISE,   // Common default
    .depthBiasEnable = VK_FALSE,            // Rarely used
    .depthBiasConstantFactor = 0.0f,
    .depthBiasClamp = 0.0f,
    .depthBiasSlopeFactor = 0.0f,
    .lineWidth = 1.0f                        // Almost always 1.0
};
```

#### 1.3.2 Manual Resource Lifecycle

```c
// Vulkan: Manual cleanup in REVERSE ORDER
void cleanup() {
    vkDeviceWaitIdle(device);

    for (size_t i = 0; i < MAX_FRAMES_IN_FLIGHT; i++) {
        vkDestroySemaphore(device, renderFinishedSemaphores[i], NULL);
        vkDestroySemaphore(device, imageAvailableSemaphores[i], NULL);
        vkDestroyFence(device, inFlightFences[i], NULL);
    }

    vkDestroyCommandPool(device, commandPool, NULL);

    for (auto framebuffer : swapChainFramebuffers) {
        vkDestroyFramebuffer(device, framebuffer, NULL);
    }

    vkDestroyPipeline(device, graphicsPipeline, NULL);
    vkDestroyPipelineLayout(device, pipelineLayout, NULL);
    vkDestroyRenderPass(device, renderPass, NULL);

    for (auto imageView : swapChainImageViews) {
        vkDestroyImageView(device, imageView, NULL);
    }

    vkDestroySwapchainKHR(device, swapChain, NULL);
    vkDestroyDevice(device, NULL);
    vkDestroySurfaceKHR(instance, surface, NULL);
    vkDestroyInstance(instance, NULL);
    // Forget one? Memory leak. Wrong order? Crash.
}
```

#### 1.3.3 Synchronization Nightmare

```c
// Vulkan: Manual synchronization
VkSubmitInfo submitInfo = {
    .sType = VK_STRUCTURE_TYPE_SUBMIT_INFO,
    .waitSemaphoreCount = 1,
    .pWaitSemaphores = waitSemaphores,        // Wait for image
    .pWaitDstStageMask = waitStages,          // At which stage?
    .commandBufferCount = 1,
    .pCommandBuffers = &commandBuffers[imageIndex],
    .signalSemaphoreCount = 1,
    .pSignalSemaphores = signalSemaphores     // Signal when done
};

// What if semaphore is signaled but not waited?
// What if fence is never reset?
// What if barrier stage mask is wrong?
// All lead to race conditions or deadlocks
```

---

## 2. How Simple Helps: Feature Mapping

### 2.1 Smart Defaults

Simple's philosophy: **Everything has a sensible default.**

```simple
# Simple Vulkan DSL: Defaults everywhere
pipeline = Pipeline.new()
    .shader(vertex_shader)
    .shader(fragment_shader)
    # That's it. All rasterization, blend, depth settings use defaults.
    # Override only what you need:
    .cull_mode(CullMode.None)  # Optional override
```

**Implementation:** All Vulkan structs wrapped with default constructors:

```simple
struct RasterizationState:
    depth_clamp: bool = false
    discard: bool = false
    polygon_mode: PolygonMode = PolygonMode.Fill
    cull_mode: CullMode = CullMode.Back
    front_face: FrontFace = FrontFace.Clockwise
    line_width: f32 = 1.0
    # ... all have defaults
```

### 2.2 Actor Model for Concurrency

Simple's actor model eliminates synchronization bugs.

```simple
# GPU work as actors - no manual semaphores
actor RenderActor:
    device: VulkanDevice
    swapchain: Swapchain

    fn render(frame: Frame):
        # Automatic message passing replaces semaphores
        image_index = self.swapchain.acquire_next()

        cmd = CommandBuffer.new()
        cmd.begin_render_pass(self.swapchain.framebuffer(image_index))
        cmd.draw(frame.vertices)
        cmd.end_render_pass()

        # Actor mailbox automatically handles frame synchronization
        self.device.submit(cmd)
        self.swapchain.present(image_index)
```

**Benefit:** The actor runtime handles:
- Semaphore creation/signaling
- Fence waiting
- Frame-in-flight management
- Resource lifetime across frames

### 2.3 Immutable Objects Prevent Data Races

```simple
# Immutable pipeline state - safe to share across threads
let pipeline = Pipeline.new()
    .vertex_format(vertex_format)
    .shaders([vert, frag])
    .freeze()  # Returns immutable reference

# Multiple render threads can use same pipeline
actor RenderThread1:
    pipeline: Pipeline  # Immutable, safe to share

actor RenderThread2:
    pipeline: Pipeline  # Same immutable pipeline
```

### 2.4 Compile-Time Contracts

Contracts catch resource errors at compile time.

```simple
struct Buffer:
    handle: VkBuffer
    memory: VkDeviceMemory
    size: u64
    mapped: bool

    in: handle != VK_NULL_HANDLE
    in: memory != VK_NULL_HANDLE

    # Postcondition: buffer must be unmapped before destruction
    out: not mapped

    invariant: size > 0

fn copy_to_buffer(dst: mut Buffer, data: [u8]):
    in: data.len() <= dst.size      # Compile-time size check
    in: dst.mapped                  # Must be mapped

    # Implementation
    memcpy(dst.ptr, data.ptr, data.len())
```

**Runtime Contract Example:**
```simple
fn create_pipeline(device: Device, shaders: [Shader]) -> Pipeline:
    in: shaders.len() >= 1                    # At least one shader
    in: shaders.any(s => s.stage == Vertex)   # Must have vertex
    out(ret): ret.is_valid()                  # Pipeline created

    # Compile-time verification of shader compatibility
```

### 2.5 AOP for Cross-Cutting Concerns

AOP weaves validation, profiling, and cleanup automatically.

```simple
# Aspect: Automatic validation layer
aspect VulkanValidation:
    before Pipeline.create(self, *):
        if not self.shaders.any(s => s.stage == Vertex):
            error("Pipeline requires vertex shader")

    after Buffer.new(ret, *):
        log.debug("Buffer created: {ret.size} bytes")

    around CommandBuffer.submit(self, cmd):
        let start = time.now()
        proceed()
        metrics.record("gpu_submit_time", time.since(start))

# Aspect: Automatic resource cleanup
aspect ResourceCleanup:
    after_return VulkanContext.destroy(self):
        # Automatically destroy all tracked resources
        for resource in self.tracked_resources.reverse():
            resource.destroy()
```

### 2.6 Macros Reduce Typing

```simple
# Macro for descriptor set layout (reduces 50 lines to 5)
#[descriptor_set]
struct MaterialDescriptors:
    #[binding(0)] albedo: Texture2D
    #[binding(1)] normal: Texture2D
    #[binding(2)] metallic: Texture2D
    #[binding(3)] params: UniformBuffer[MaterialParams]

# Expands to full VkDescriptorSetLayoutBinding array,
# VkDescriptorPoolSize, VkWriteDescriptorSet, etc.

# Macro for vertex format (reduces 30 lines to 3)
#[vertex]
struct Vertex:
    #[location(0)] position: Vec3
    #[location(1)] normal: Vec3
    #[location(2)] uv: Vec2

# Expands to VkVertexInputBindingDescription,
# VkVertexInputAttributeDescription array
```

---

## 3. DSL Candidates

### 3.1 Builder Pattern DSL (Recommended)

Fluent API with smart defaults, mirrors Simple's UI Builder Pattern.

#### 3.1.1 Maximum Defaults (Zero Config)

```simple
import vulkan.{Device, Swapchain, Pipeline}

fn main():
    # Everything uses sensible defaults - ZERO configuration needed
    device = Device.new()                    # Auto-selects best GPU
    swapchain = Swapchain.new(device)        # VSync, double buffer, best format
    pipeline = Pipeline.new()
        .render_pass_from(swapchain)         # Infers render pass from swapchain

    # Render loop with context manager (with/as block)
    while with window.frame() as frame:
        frame.draw(pipeline, vertices)
        # frame automatically ends when block exits (RAII)
```

**Lines:** ~8 vs ~1000 in C++ (99.2% reduction!)

#### 3.1.2 Override Only What You Need

```simple
import vulkan.{Device, Swapchain, Pipeline}

fn main():
    # Override specific settings, rest stay default
    device = Device.new()
        .prefer_discrete()                   # Only if you need discrete GPU
        .validation(DEBUG)                   # Only in debug builds

    swapchain = Swapchain.new(device)
        .triple_buffer()                     # Override: prefer triple buffering

    pipeline = Pipeline.new()
        .cull_mode(CullMode.None)           # Override: disable culling
        .render_pass_from(swapchain)

    while with window.frame() as frame:
        frame.draw(pipeline, vertices)
```

#### 3.1.3 Default Philosophy

| Setting | Vulkan Requires | Simple Default |
|---------|-----------------|----------------|
| GPU selection | Manual enumeration | Best discrete, fallback integrated |
| Queue families | Manual query | Auto-detect graphics+present |
| Swapchain format | Query capabilities | Best SRGB format available |
| Present mode | Query capabilities | VSync (Fifo) |
| Image count | Query min/max | 2 (double buffer) |
| Render pass | Manual creation | Inferred from swapchain |
| Pipeline state | 50+ fields required | All have sensible defaults |
| Synchronization | Manual semaphores/fences | Automatic via `with` block |

**Lines:** ~8-15 vs ~1000 in C++

### 3.2 Declarative Scene DSL

For scene-based applications (games, visualization).

```simple
import vulkan.scene

scene MyScene:
    camera:
        position: Vec3(0, 0, -5)
        fov: 60.0
        near: 0.1
        far: 1000.0

    objects:
        mesh "triangle":
            vertices: triangle_vertices
            material:
                shader: "unlit"
                color: Color.red()

        mesh "cube":
            vertices: cube_vertices
            transform:
                position: Vec3(2, 0, 0)
                rotation: Quat.identity()
            material:
                shader: "pbr"
                albedo: Texture.load("cube_albedo.png")
                normal: Texture.load("cube_normal.png")

    lights:
        directional:
            direction: Vec3(-1, -1, -1)
            color: Color.white()
            intensity: 1.0

fn main():
    renderer = SceneRenderer.new()
    renderer.render(MyScene)
```

### 3.3 Immediate Mode DSL

For UI and debug rendering (similar to Dear ImGui).

#### 3.3.1 With Block Context (Recommended)

```simple
import gfx.immediate as im
import gfx.types.{Rect, Loc2, Loc3, Color}

fn render():
    # Use `with` block - no begin/end needed
    with im:
        # 2D UI using underscore-separated coordinates
        rect(100_100_200_50_rect.color(Color.blue))   # x_y_w_h_rect
        text(110_120_loc, "Hello Vulkan!")            # Uses default font

        # 3D debug
        line_3d(0_0_0_loc3, 1_1_1_loc3, Color.green)
        sphere_wireframe(0_2_0_loc3, 0.5, Color.red)
```

#### 3.3.2 Multi-Input Type Syntax

Simple introduces **underscore-separated literal syntax** for common coordinate/dimension types:

```simple
# Type inference from suffix
100_200_loc        # Loc2(100, 200) - 2D location
100_200_300_loc3   # Loc3(100, 200, 300) - 3D location
50_30_size         # Size2(50, 30) - 2D size
10_20_100_50_rect  # Rect(10, 20, 100, 50) - x, y, width, height

# Naming convention: dimension in type name
Loc2   / _loc      # 2D (implicit default for graphics)
Loc3   / _loc3     # 3D (explicit suffix)
Size2  / _size     # 2D size
Size3  / _size3    # 3D size
Rect   / _rect     # 2D rectangle (x, y, w, h)
Box    / _box      # 3D box (x, y, z, w, h, d)

# Method chaining on literals
100_100_200_50_rect.color(Color.blue).rounded(5)
0_0_0_loc3.offset(1, 0, 0)
```

#### 3.3.3 Type Naming Convention

| Type | Literal Suffix | Example | Notes |
|------|---------------|---------|-------|
| `Loc2` | `_loc` | `100_200_loc` | 2D is default (no "2") |
| `Loc3` | `_loc3` | `1_2_3_loc3` | 3D explicit |
| `Size2` | `_size` | `50_30_size` | Width × Height |
| `Size3` | `_size3` | `10_20_30_size3` | W × H × D |
| `Rect` | `_rect` | `0_0_100_50_rect` | x, y, w, h |
| `Box` | `_box` | `0_0_0_10_10_10_box` | x, y, z, w, h, d |
| `Color` | `_rgb` / `_rgba` | `255_128_0_rgb` | RGB(A) values |
| `Vec2` | `_vec2` | `1.5_2.0_vec2` | Float vector |
| `Vec3` | `_vec3` | `1_0_0_vec3` | Float vector |

#### 3.3.4 Comparison: Old vs New

```simple
# OLD: Verbose, explicit constructors
im.begin()
im.rect(100, 100, 200, 50, Color.blue())
im.text(110, 120, "Hello", Font.default())
im.line_3d(Vec3.zero(), Vec3(1, 1, 1), Color.green())
im.end()

# NEW: With block + underscore literals + implicit defaults
with im:
    rect(100_100_200_50_rect.color(Color.blue))
    text(110_120_loc, "Hello")           # Font: implicit default
    line_3d(0_0_0_loc3, 1_1_1_loc3, Color.green)
```

**Benefits:**
- `with` block eliminates `begin()`/`end()` boilerplate
- Underscore syntax reduces visual noise
- Dimension in type name (`_loc3` vs `_loc`) clarifies intent
- Implicit defaults (font, color) reduce parameters

#### 3.3.5 Custom Type Literal Suffix

User-defined types can support multi-value underscore syntax by implementing the `FromLiteral` trait:

```simple
# Define a custom type
struct Quaternion:
    w: f32
    x: f32
    y: f32
    z: f32

# Implement multi-value literal support
impl FromLiteral for Quaternion:
    const SUFFIX = "quat"          # Enables: 1_0_0_0_quat
    const ARITY = 4                # Requires exactly 4 values

    fn from_parts(parts: [f32; 4]) -> Self:
        Quaternion(parts[0], parts[1], parts[2], parts[3])

# Usage
rotation = 1_0_0_0_quat              # Quaternion(1, 0, 0, 0) - identity
rotation = 0.707_0_0.707_0_quat      # 90° rotation around Y
```

**Custom Type Registration:**

```simple
# Custom game types
struct Tile:
    x: i32
    y: i32
    layer: i32

impl FromLiteral for Tile:
    const SUFFIX = "tile"
    const ARITY = 3

    fn from_parts(parts: [i32; 3]) -> Self:
        Tile(parts[0], parts[1], parts[2])

# Variadic arity (2 or 3 values)
struct Point:
    x: f32
    y: f32
    z: f32 = 0.0                     # Default z for 2D

impl FromLiteral for Point:
    const SUFFIX = "pt"
    const ARITY = 2..3               # Accepts 2 or 3 values

    fn from_parts(parts: [f32]) -> Self:
        match parts.len():
            2 => Point(parts[0], parts[1], 0.0)
            3 => Point(parts[0], parts[1], parts[2])

# Usage
pos = 100_200_pt                     # Point(100, 200, 0)
pos = 100_200_50_pt                  # Point(100, 200, 50)
tile = 5_3_0_tile                    # Tile(5, 3, 0)
```

**Custom Type Table:**

| Custom Type | Suffix | Arity | Example | Description |
|-------------|--------|-------|---------|-------------|
| `Quaternion` | `_quat` | 4 | `1_0_0_0_quat` | w, x, y, z rotation |
| `Tile` | `_tile` | 3 | `5_3_0_tile` | x, y, layer |
| `Point` | `_pt` | 2-3 | `100_200_pt` | Optional z |
| `Margin` | `_margin` | 1-4 | `10_margin`, `10_20_margin` | CSS-style |
| `HSL` | `_hsl` | 3 | `180_100_50_hsl` | Hue, Sat, Light |

#### 3.3.6 Units with Multi-Value Input

Physical units from Simple's units system integrate with multi-value literals:

```simple
import std.units

# Single-value units (existing)
distance = 100_m                     # 100 meters
time = 5_s                           # 5 seconds
mass = 2.5_kg                        # 2.5 kilograms

# Multi-value units with dimensions
position = 100_200_m2                # Position2D(100m, 200m)
position = 10_20_30_m3               # Position3D(10m, 20m, 30m)
velocity = 5_10_m_per_s2             # Velocity2D(5 m/s, 10 m/s)
force = 1_2_3_N3                     # Force3D(1N, 2N, 3N)
```

**Unit Literal Syntax Rules:**

```simple
# Format: value1_value2_..._unit[dimension]
# dimension suffix: 2 = 2D, 3 = 3D (no suffix = scalar or default 2D)

# Length units
10_m                                 # 10 meters (scalar)
10_20_m2                             # (10m, 20m) - 2D position
10_20_30_m3                          # (10m, 20m, 30m) - 3D position

# Compound units use underscore-separated names
5_10_m_per_s2                        # Velocity2D(5 m/s, 10 m/s)
1_2_3_m_per_s2_3                     # Acceleration3D

# Angle units
45_deg                               # 45 degrees (scalar)
45_90_deg2                           # (45°, 90°) - 2D rotation
0_45_90_deg3                         # Euler angles (pitch, yaw, roll)

# Mixed with custom types
transform = 100_200_px2              # Pixel position
bbox = 0_0_100_50_m_rect             # Rect with meter units
```

**Unit Type Table:**

| Category | Scalar | 2D | 3D | Example |
|----------|--------|-------|-------|---------|
| Length | `_m`, `_cm`, `_px` | `_m2`, `_px2` | `_m3` | `100_200_px2` |
| Velocity | `_m_per_s` | `_m_per_s2` | `_m_per_s3` | `5_10_m_per_s2` |
| Angle | `_deg`, `_rad` | `_deg2` | `_deg3` | `45_90_deg2` |
| Force | `_N` | `_N2` | `_N3` | `1_2_3_N3` |
| Time | `_s`, `_ms` | - | - | `16_ms` |

**Defining Unit-Aware Custom Types:**

```simple
import std.units

# Custom type with unit constraint
struct Velocity2D[U: LengthPerTime]:
    x: U
    y: U

impl[U: LengthPerTime] FromLiteral for Velocity2D[U]:
    const SUFFIX = U.suffix + "2"    # e.g., "m_per_s2"
    const ARITY = 2

    fn from_parts(parts: [f32; 2]) -> Self:
        Velocity2D(U.new(parts[0]), U.new(parts[1]))

# Physics simulation with unit-checked math
fn update_position(pos: Position3D[m], vel: Velocity3D[m_per_s], dt: Duration[s]) -> Position3D[m]:
    pos + vel * dt                   # Compile-time unit checking
```

**Integration with Graphics Types:**

```simple
# Graphics primitives with units
viewport = 0_0_1920_1080_px_rect     # Viewport in pixels
world_box = 0_0_0_100_100_50_m_box   # World bounding box in meters

# Conversion between unit systems
screen_pos = world_pos.to_px(camera) # meters → pixels
world_pos = screen_pos.to_m(camera)  # pixels → meters

# Immediate mode with units
with im:
    rect(100_100_200_50_px_rect.color(Color.blue))
    line(0_0_px2, 100_100_px2, Color.red)

    # World-space drawing (auto-converts via camera)
    with im.world_space(camera):
        circle(player.position, 1_m)  # 1 meter radius
```

**See Also:** [Unit Types Specification](../spec/units.md) for complete unit system documentation.

### 3.4 Compute DSL

For GPU compute workloads.

```simple
import vulkan.compute

#[compute(local_size = (256, 1, 1))]
fn vector_add(a: Buffer[f32], b: Buffer[f32], result: mut Buffer[f32]):
    let idx = global_id.x
    result[idx] = a[idx] + b[idx]

fn main():
    let a = Buffer.from([1.0, 2.0, 3.0, 4.0])
    let b = Buffer.from([5.0, 6.0, 7.0, 8.0])
    let result = Buffer.new[f32](4)

    compute.dispatch(vector_add, a, b, result)
    compute.sync()

    print(result.read())  # [6.0, 8.0, 10.0, 12.0]
```

### 3.5 Shader DSL (Embedded GLSL)

Type-safe shader definitions with compile-time validation.

```simple
import vulkan.shader

shader TriangleShader:
    vertex:
        in position: Vec3 @ location(0)
        in color: Vec3 @ location(1)

        out frag_color: Vec3

        uniform mvp: Mat4

        fn main():
            gl_Position = mvp * Vec4(position, 1.0)
            frag_color = color

    fragment:
        in frag_color: Vec3

        out out_color: Vec4

        fn main():
            out_color = Vec4(frag_color, 1.0)

# Compile-time validation:
# - Vertex out matches fragment in
# - Uniform types match descriptor set
# - Location indices are unique
```

---

## 4. DSL Comparison Matrix

| DSL | Use Case | Lines Saved | Learning Curve | Flexibility |
|-----|----------|-------------|----------------|-------------|
| **Builder Pattern** | General rendering | 95% | Low | High |
| **Declarative Scene** | Games, visualization | 90% | Medium | Medium |
| **Immediate Mode** | UI, debug | 85% | Very Low | Low |
| **Compute** | GPGPU | 90% | Low | High |
| **Shader DSL** | Custom shaders | 80% | Medium | Very High |

**Recommendation:** Start with **Builder Pattern DSL** as the core, add others incrementally.

---

## 5. Implementation Architecture

### 5.1 Layered Architecture

```
┌─────────────────────────────────────────────────────────┐
│                    Simple DSL Layer                      │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────────┐  │
│  │   Builder   │  │ Declarative │  │ Immediate/Comp  │  │
│  │   Pattern   │  │    Scene    │  │     Compute     │  │
│  └──────┬──────┘  └──────┬──────┘  └────────┬────────┘  │
│         │                │                   │          │
│         └────────────────┼───────────────────┘          │
│                          ▼                              │
│  ┌─────────────────────────────────────────────────────┐│
│  │              Vulkan Abstraction Layer               ││
│  │  - Smart defaults for all structs                   ││
│  │  - Automatic synchronization via actors             ││
│  │  - Resource tracking and cleanup via AOP            ││
│  │  - Compile-time validation via contracts            ││
│  └──────────────────────┬──────────────────────────────┘│
│                         ▼                               │
│  ┌─────────────────────────────────────────────────────┐│
│  │            Vulkan FFI Bindings (Raw)                ││
│  │  - vkCreateInstance, vkCreateDevice, etc.           ││
│  └─────────────────────────────────────────────────────┘│
└─────────────────────────────────────────────────────────┘
```

### 5.2 File Structure

```
simple/std_lib/src/vulkan/
├── __init__.spl           # Module exports
├── device.spl             # Device, PhysicalDevice, Queue
├── swapchain.spl          # Swapchain, Surface
├── pipeline.spl           # GraphicsPipeline, ComputePipeline
├── shader.spl             # Shader loading, SPIR-V
├── buffer.spl             # Buffer, memory allocation
├── texture.spl            # Image, ImageView, Sampler
├── descriptors.spl        # DescriptorSet, DescriptorPool
├── commands.spl           # CommandBuffer, CommandPool
├── sync.spl               # Semaphore, Fence, Barrier
├── render_pass.spl        # RenderPass, Framebuffer
├── defaults.spl           # All default configurations
├── dsl/
│   ├── builder.spl        # Builder pattern DSL
│   ├── scene.spl          # Declarative scene DSL
│   ├── immediate.spl      # Immediate mode DSL
│   └── compute.spl        # Compute DSL
├── macros/
│   ├── vertex.spl         # #[vertex] macro
│   ├── descriptor.spl     # #[descriptor_set] macro
│   └── shader.spl         # Shader DSL macro
└── aspects/
    ├── validation.spl     # Validation layer aspect
    ├── profiling.spl      # GPU profiling aspect
    └── cleanup.spl        # Resource cleanup aspect
```

---

## 6. Example: Full Application

### 6.1 Triangle with Maximum Defaults

```simple
import vulkan.{Device, Swapchain, Pipeline, Buffer}
import gfx.types.{Vec2, Vec3}
import window.Window

#[vertex]
struct Vertex:
    #[location(0)] position: Vec2
    #[location(1)] color: Vec3

let VERTICES = [
    Vertex { position: 0.0_-0.5_vec2, color: 1_0_0_vec3 },   # Red top
    Vertex { position: 0.5_0.5_vec2, color: 0_1_0_vec3 },    # Green bottom-right
    Vertex { position: -0.5_0.5_vec2, color: 0_0_1_vec3 },   # Blue bottom-left
]

fn main():
    window = Window.new("Vulkan Triangle", 800_600_size)

    # MAXIMUM DEFAULTS - everything auto-configured
    device = Device.new()
    swapchain = Swapchain.new(device)
    pipeline = Pipeline.new()
        .render_pass_from(swapchain)    # Infers from swapchain

    vertex_buffer = Buffer.vertex(VERTICES)

    # Render loop with context manager
    while with window.frame() as frame:
        frame.draw(pipeline, vertex_buffer)
        # frame.end() called automatically
```

**Total: ~20 lines vs ~1000 in C++ (98% reduction)**

### 6.2 Triangle with Custom Settings

```simple
import vulkan.{Device, Swapchain, Pipeline, Shader, Buffer}
import gfx.types.{Vec2, Vec3}
import window.Window

#[vertex]
struct Vertex:
    #[location(0)] position: Vec2
    #[location(1)] color: Vec3

let VERTICES = [
    Vertex { position: 0.0_-0.5_vec2, color: 1_0_0_vec3 },
    Vertex { position: 0.5_0.5_vec2, color: 0_1_0_vec3 },
    Vertex { position: -0.5_0.5_vec2, color: 0_0_1_vec3 },
]

fn main():
    window = Window.new("Vulkan Triangle", 800_600_size)

    # Override only what you need
    device = Device.new()
        .prefer_discrete()              # Override: prefer dedicated GPU
        .validation(DEBUG)              # Override: validation in debug only

    swapchain = Swapchain.new(device)
        .triple_buffer()                # Override: prefer triple buffering

    pipeline = Pipeline.new()
        .shaders("triangle.vert.spv", "triangle.frag.spv")  # Custom shaders
        .cull_mode(CullMode.None)       # Override: no culling
        .render_pass_from(swapchain)

    vertex_buffer = Buffer.vertex(VERTICES)

    while with window.frame() as frame:
        frame.draw(pipeline, vertex_buffer)
```

**Total: ~30 lines vs ~1000 in C++ (97% reduction)**

---

## 7. Simple Language Features Usage Summary

| Problem | Vulkan Pain | Simple Feature | Benefit |
|---------|-------------|----------------|---------|
| Verbosity | 50+ struct fields | **Smart defaults** | 98% less code |
| Resource leaks | Manual destroy order | **RAII + `with` blocks** | Auto cleanup |
| Synchronization | Manual semaphores/fences | **Actor model + `with`** | No race conditions |
| Data races | Shared mutable state | **Immutable objects** | Thread-safe |
| Invalid state | Runtime crashes | **Compile-time contracts** | Early error detection |
| Boilerplate | Repetitive patterns | **Macros** | Code generation |
| Cross-cutting | Scattered validation/logging | **AOP** | Centralized aspects |
| Type safety | SPIR-V type mismatches | **Type-safe shader DSL** | Compile-time validation |
| Coordinate noise | `Vec3(1, 2, 3)` verbose | **Underscore literals** | `1_2_3_vec3` compact |
| Begin/end pairs | Manual scope management | **`with` context blocks** | Automatic scoping |
| Custom types | Manual constructors | **Custom `FromLiteral`** | `1_0_0_0_quat` syntax |
| Unit mismatches | Mixed px/meters | **Multi-value units** | `100_200_m2` type-safe |
| Dimensional analysis | Manual conversions | **Unit constraints** | Compile-time checks |

---

## 8. Recommendations

1. **Start with Builder Pattern DSL** - Most flexible, lowest learning curve
2. **Implement smart defaults first** - Biggest impact on usability
3. **Add actor-based synchronization** - Eliminates hardest Vulkan bugs
4. **Use AOP for validation/cleanup** - Removes boilerplate
5. **Add shader DSL later** - High value but complex
6. **Consider WGPU as alternative** - Simpler API, cross-platform

---

## 9. SDN-Based Vulkan Configuration

### 9.1 Why SDN for Vulkan?

SDN (Simple Data Notation) provides a declarative configuration format that's perfect for Vulkan's complex setup. Combined with **functional defaults**, SDN enables:

1. **Declarative Configuration** - Describe what you want, not how to create it
2. **Functional Defaults** - Compute optimal values at runtime based on device capabilities
3. **Type Safety** - SDN tables enforce structure and types
4. **Readability** - Minimal syntax, easy to understand

### 9.2 Functional Defaults Grammar Extension

Current SDN supports static values. We extend it with **functional defaults** using `@fn()` syntax:

```ebnf
# SDN Grammar Extension for Functional Defaults

value           = bare_string | quoted_string | number | bool | null
                | inline_value | functional_default ;

# NEW: Functional default - a function that computes a value at runtime
functional_default = "@fn(" [params] ")" "=>" expression ;

params          = param ("," param)* ;
param           = identifier [ ":" type ] ;

expression      = identifier
                | expression "." identifier
                | expression "." identifier "(" [args] ")"
                | expression "[" expression "]"
                | expression binop expression
                | "if" expression "then" expression "else" expression
                | literal ;

binop           = "+" | "-" | "*" | "/" | ">" | "<" | ">=" | "<=" | "==" | "!=" | "and" | "or" ;
```

### 9.3 Functional Default Examples

```sdn
# Functional defaults compute optimal values at configuration load time

# Basic: Call a function to get device's best format
format: @fn() => device.best_format([BGRA8, RGBA8])

# With parameters: Receive context
image_count: @fn(device) => min(device.max_images, 3)

# Conditional: Choose based on device capabilities
sample_count: @fn(device) => if device.supports_msaa(8) then 8 else 4

# Chain calls: Navigate through device properties
memory_type: @fn(device) => device.memory_properties.find_type(DeviceLocal | HostVisible)

# Math expressions
workgroup_size: @fn(device) => min(device.max_workgroup_size, 256)

# Boolean expressions
validation: @fn(config) => config.debug_mode and config.platform != "release"
```

### 9.4 Vulkan Configuration with SDN

#### 9.4.1 Device Configuration

```sdn
# vulkan_config.sdn - Complete Vulkan device configuration

device:
    # Static preference
    prefer_discrete: true

    # Functional: Auto-select best queue families
    graphics_queue: @fn(device) => device.find_queue_family(Graphics)
    compute_queue: @fn(device) => device.find_queue_family(Compute | Transfer)
    transfer_queue: @fn(device) => device.find_dedicated_transfer_queue() or device.graphics_queue

    # Features based on what's available
    features:
        geometry_shader: @fn(device) => device.supports(GeometryShader)
        tessellation: @fn(device) => device.supports(TessellationShader)
        anisotropy: @fn(device) => device.supports(SamplerAnisotropy)

    # Validation layers (only in debug)
    validation_layers: @fn(config) => if config.debug then ["VK_LAYER_KHRONOS_validation"] else []
```

#### 9.4.2 Swapchain Configuration

```sdn
swapchain:
    # Functional defaults for optimal swapchain settings
    surface_format:
        format: @fn(surface) => surface.best_format([BGRA8_SRGB, RGBA8_SRGB, BGRA8_UNORM])
        color_space: @fn(surface) => surface.best_color_space([SRGB_NONLINEAR, HDR10])

    # Present mode selection with fallback chain
    present_mode: @fn(surface) => surface.best_present_mode([
        Mailbox,    # Triple buffering, no tearing
        FifoRelaxed, # VSync with relaxed
        Fifo        # Guaranteed VSync
    ])

    # Image count: prefer triple buffering
    image_count: @fn(caps) => clamp(3, caps.min_image_count, caps.max_image_count)

    # Extent: match window or use current
    extent:
        width: @fn(caps, window) => if caps.current_extent.width == 0xFFFFFFFF
                                    then window.width
                                    else caps.current_extent.width
        height: @fn(caps, window) => if caps.current_extent.height == 0xFFFFFFFF
                                     then window.height
                                     else caps.current_extent.height

    # Transform based on device orientation
    pre_transform: @fn(caps) => caps.current_transform

    # Composite alpha with fallback
    composite_alpha: @fn(caps) => caps.best_composite_alpha([Opaque, PreMultiplied, Inherit])
```

#### 9.4.3 Pipeline Configuration

```sdn
pipeline "main_graphics":
    # Shaders (static paths)
    shaders:
        vertex: "shaders/main.vert.spv"
        fragment: "shaders/main.frag.spv"

    # Vertex input - infer from shader reflection or specify
    vertex_input: @fn(shader) => shader.reflect_vertex_input()

    # Rasterization with smart defaults
    rasterization:
        polygon_mode: Fill          # Static default
        cull_mode: Back             # Static default
        front_face: CounterClockwise
        line_width: 1.0
        depth_clamp: false
        depth_bias: @fn(config) => if config.shadow_pass then
                                       { enable: true, constant: 1.25, slope: 1.75 }
                                   else
                                       { enable: false }

    # Multisample with device-aware defaults
    multisample:
        samples: @fn(device) => device.best_sample_count([8, 4, 2, 1])
        sample_shading: @fn(device, config) => config.quality >= High and device.supports_sample_shading
        min_sample_shading: @fn(config) => if config.quality == Ultra then 1.0 else 0.25

    # Depth/stencil
    depth_stencil:
        depth_test: true
        depth_write: true
        depth_compare: Less
        depth_bounds: false
        stencil_test: false

    # Color blend
    color_blend:
        logic_op: false
        attachments:
            - blend_enable: false
              color_write_mask: RGBA
```

#### 9.4.4 Render Pass Configuration

```sdn
render_pass "main":
    attachments:
        color:
            format: @fn(swapchain) => swapchain.format
            samples: @fn(pipeline) => pipeline.multisample.samples
            load_op: Clear
            store_op: Store
            initial_layout: Undefined
            final_layout: PresentSrc

        depth:
            format: @fn(device) => device.best_depth_format([D32_SFLOAT, D24_UNORM_S8_UINT, D16_UNORM])
            samples: @fn(pipeline) => pipeline.multisample.samples
            load_op: Clear
            store_op: DontCare
            initial_layout: Undefined
            final_layout: DepthStencilAttachmentOptimal

    subpasses:
        - name: "main"
          color_attachments: [{ attachment: "color", layout: ColorAttachmentOptimal }]
          depth_attachment: { attachment: "depth", layout: DepthStencilAttachmentOptimal }

    dependencies:
        - src: External
          dst: "main"
          src_stage: ColorAttachmentOutput | EarlyFragmentTests
          dst_stage: ColorAttachmentOutput | EarlyFragmentTests
          src_access: 0
          dst_access: ColorAttachmentWrite | DepthStencilAttachmentWrite
```

#### 9.4.5 Memory and Buffer Configuration

```sdn
memory:
    # Allocator selection
    allocator: @fn(config) => if config.use_vma then "vma" else "simple"

    # Default memory pools
    pools:
        device_local:
            flags: DeviceLocal
            block_size: @fn(device) => min(device.heap_size(DeviceLocal) / 8, 256 * MB)

        staging:
            flags: HostVisible | HostCoherent
            block_size: 64 * MB

        uniform:
            flags: @fn(device) => if device.has_bar_memory
                                  then DeviceLocal | HostVisible | HostCoherent
                                  else HostVisible | HostCoherent
            block_size: @fn(device) => if device.has_bar_memory then 32 * MB else 16 * MB

buffer "vertex_buffer":
    usage: VertexBuffer | TransferDst
    memory: @fn() => memory.pools.device_local
    size: @fn(mesh) => mesh.vertex_count * mesh.vertex_stride

buffer "uniform_buffer":
    usage: UniformBuffer
    memory: @fn() => memory.pools.uniform
    size: @fn(frame_count) => sizeof(UniformData) * frame_count
```

### 9.5 Functional Defaults Implementation

#### 9.5.1 SDN Parser Extension

```simple
# src/sdn/src/parser.rs extension for functional defaults

enum SdnValue:
    # ... existing variants ...
    FunctionalDefault(FunctionalDefault)

struct FunctionalDefault:
    params: [String]
    expression: Expression

enum Expression:
    Identifier(String)
    MemberAccess(Box[Expression], String)
    MethodCall(Box[Expression], String, [Expression])
    Index(Box[Expression], Box[Expression])
    BinaryOp(Box[Expression], BinOp, Box[Expression])
    Conditional(Box[Expression], Box[Expression], Box[Expression])
    Literal(SdnValue)
    Array([Expression])

enum BinOp:
    Add, Sub, Mul, Div
    Gt, Lt, Gte, Lte, Eq, Ne
    And, Or

fn parse_value(self) -> SdnValue:
    if self.peek() == "@fn":
        self.parse_functional_default()
    else:
        self.parse_static_value()

fn parse_functional_default(self) -> SdnValue:
    self.expect("@fn")
    self.expect("(")
    params = self.parse_params()
    self.expect(")")
    self.expect("=>")
    expr = self.parse_expression()
    SdnValue.FunctionalDefault(FunctionalDefault { params, expression: expr })

fn parse_expression(self) -> Expression:
    self.parse_conditional_or_lower()

fn parse_conditional_or_lower(self) -> Expression:
    if self.peek() == "if":
        self.consume()
        cond = self.parse_or_expr()
        self.expect("then")
        then_branch = self.parse_or_expr()
        self.expect("else")
        else_branch = self.parse_or_expr()
        Expression.Conditional(box cond, box then_branch, box else_branch)
    else:
        self.parse_or_expr()
```

#### 9.5.2 Functional Default Evaluator

```simple
# Runtime evaluation of functional defaults

struct FnDefaultContext:
    device: VulkanDevice
    surface: VulkanSurface
    config: Config
    # ... other context values

fn evaluate_fn_default(fn_default: FunctionalDefault, ctx: FnDefaultContext) -> SdnValue:
    # Build parameter bindings
    bindings = Dict.new()
    for param in fn_default.params:
        match param:
            "device" => bindings.insert(param, ctx.device)
            "surface" => bindings.insert(param, ctx.surface)
            "config" => bindings.insert(param, ctx.config)
            "caps" => bindings.insert(param, ctx.surface.capabilities())
            "window" => bindings.insert(param, ctx.window)
            _ => error("Unknown parameter: {param}")

    # Evaluate expression
    evaluate_expr(fn_default.expression, bindings)

fn evaluate_expr(expr: Expression, bindings: Dict[String, Any]) -> Any:
    match expr:
        Identifier(name) =>
            bindings.get(name) or error("Unbound: {name}")

        MemberAccess(obj, field) =>
            let obj_val = evaluate_expr(obj, bindings)
            obj_val.get_field(field)

        MethodCall(obj, method, args) =>
            let obj_val = evaluate_expr(obj, bindings)
            let arg_vals = args.map(a => evaluate_expr(a, bindings))
            obj_val.call_method(method, arg_vals)

        BinaryOp(left, op, right) =>
            let l = evaluate_expr(left, bindings)
            let r = evaluate_expr(right, bindings)
            apply_binop(op, l, r)

        Conditional(cond, then_b, else_b) =>
            if evaluate_expr(cond, bindings):
                evaluate_expr(then_b, bindings)
            else:
                evaluate_expr(else_b, bindings)

        Literal(val) => val

        Array(items) => items.map(i => evaluate_expr(i, bindings))
```

#### 9.5.3 Vulkan Config Loader

```simple
# Load and evaluate SDN Vulkan configuration

import sdn
import vulkan.{Device, Surface}

struct VulkanConfig:
    device: DeviceConfig
    swapchain: SwapchainConfig
    pipelines: Dict[String, PipelineConfig]
    render_passes: Dict[String, RenderPassConfig]
    memory: MemoryConfig

fn load_vulkan_config(path: String, device: Device, surface: Surface, config: Config) -> VulkanConfig:
    # Parse SDN file
    let sdn_doc = sdn.parse_file(path)

    # Create evaluation context
    let ctx = FnDefaultContext {
        device: device,
        surface: surface,
        config: config,
        window: surface.window(),
    }

    # Evaluate all functional defaults
    let evaluated = evaluate_document(sdn_doc, ctx)

    # Convert to typed config
    VulkanConfig.from_sdn(evaluated)

fn evaluate_document(doc: SdnDocument, ctx: FnDefaultContext) -> SdnDocument:
    # Recursively evaluate all functional defaults in the document
    doc.transform(|value| match value:
        SdnValue.FunctionalDefault(fn_def) =>
            let result = evaluate_fn_default(fn_def, ctx)
            SdnValue.from_any(result)
        _ => value
    )
```

### 9.6 Complete Example: SDN Vulkan Configuration

```sdn
# game_renderer.sdn - Full game renderer configuration

version: "1.0"
name: "GameRenderer"

device:
    prefer_discrete: true
    required_extensions:
        - VK_KHR_swapchain
        - VK_KHR_dynamic_rendering
    optional_extensions:
        - VK_EXT_mesh_shader
        - VK_KHR_ray_tracing_pipeline

    features:
        # Required features
        sampler_anisotropy: true
        # Optional based on device
        mesh_shader: @fn(device) => device.supports_extension("VK_EXT_mesh_shader")
        ray_tracing: @fn(device) => device.supports_extension("VK_KHR_ray_tracing_pipeline")

swapchain:
    format: @fn(surface) => surface.best_format([BGRA8_SRGB, RGBA8_SRGB])
    present_mode: @fn(surface, config) =>
        if config.vsync then Fifo
        else surface.best_present_mode([Mailbox, Immediate])
    image_count: @fn(caps) => clamp(3, caps.min_image_count, caps.max_image_count)

pipelines:
    pbr_forward:
        shaders:
            vertex: "shaders/pbr_forward.vert.spv"
            fragment: "shaders/pbr_forward.frag.spv"
        rasterization:
            cull_mode: Back
            front_face: CounterClockwise
        depth_stencil:
            depth_test: true
            depth_write: true
            depth_compare: Less
        multisample:
            samples: @fn(device, config) =>
                if config.quality >= High then device.best_sample_count([8, 4])
                else device.best_sample_count([4, 2, 1])

    skybox:
        shaders:
            vertex: "shaders/skybox.vert.spv"
            fragment: "shaders/skybox.frag.spv"
        rasterization:
            cull_mode: Front  # Inside-out cube
        depth_stencil:
            depth_test: true
            depth_write: false
            depth_compare: LessOrEqual

    ui_overlay:
        shaders:
            vertex: "shaders/ui.vert.spv"
            fragment: "shaders/ui.frag.spv"
        rasterization:
            cull_mode: None
        depth_stencil:
            depth_test: false
            depth_write: false
        color_blend:
            attachments:
                - blend_enable: true
                  src_color: SrcAlpha
                  dst_color: OneMinusSrcAlpha
                  src_alpha: One
                  dst_alpha: OneMinusSrcAlpha

render_passes:
    main:
        attachments:
            color:
                format: @fn(swapchain) => swapchain.format
                load_op: Clear
                store_op: Store
                clear_value: [0.1, 0.1, 0.1, 1.0]
            depth:
                format: @fn(device) => device.best_depth_format([D32_SFLOAT, D24_UNORM_S8_UINT])
                load_op: Clear
                store_op: DontCare
                clear_value: [1.0, 0]

        subpasses:
            - name: "scene"
              pipelines: [pbr_forward, skybox]
            - name: "ui"
              pipelines: [ui_overlay]

memory:
    allocator: @fn(config) => if config.use_vma then "vma" else "built_in"
    budgets:
        textures: @fn(device) => device.heap_size(DeviceLocal) * 0.4
        geometry: @fn(device) => device.heap_size(DeviceLocal) * 0.3
        uniforms: @fn(device) => min(device.heap_size(HostVisible) * 0.2, 128 * MB)
```

### 9.7 Benefits of SDN + Functional Defaults

| Benefit | Description | Example |
|---------|-------------|---------|
| **Device-Aware Defaults** | Configuration adapts to hardware | `samples: @fn(device) => device.best_sample_count([8, 4, 2])` |
| **Quality Scaling** | Settings adjust based on config | `if config.quality >= High then ...` |
| **Fallback Chains** | Graceful degradation | `surface.best_format([BGRA8, RGBA8, RGB8])` |
| **Type Safety** | Compile-time validation of config structure | SDN typed tables |
| **Separation of Concerns** | Config separate from code | `vulkan_config.sdn` file |
| **Hot Reloading** | Update config without recompile | Re-parse SDN file |
| **Documentation** | Self-documenting configuration | Comments + structure |

---

## References

- [Vulkan Tutorial](https://vulkan-tutorial.com/)
- [Vulkan Guide](https://vkguide.dev/)
- [ash-rs (Rust Vulkan bindings)](https://github.com/ash-rs/ash)
- [wgpu (WebGPU implementation)](https://wgpu.rs/)
- [Dear ImGui](https://github.com/ocornut/imgui)
- [Slint UI](https://slint.dev/)
- [SDN Specification](../spec/sdn.md)
