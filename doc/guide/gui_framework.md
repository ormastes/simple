# Simple GUI Framework

**Status:** SFFI wrappers complete, Rust runtime implementations pending
**Last Updated:** 2026-02-16

A complete GUI and graphics framework for the Simple language, built on production-grade Rust libraries. Covers windowing, 2D/3D graphics, physics, audio, gamepad input, GPU compute, and widget systems.

---

## Table of Contents

1. [Architecture Overview](#1-architecture-overview)
2. [Component Stack](#2-component-stack)
3. [Windowing (Winit)](#3-windowing-winit)
4. [2D Graphics (Lyon)](#4-2d-graphics-lyon)
5. [Physics (Rapier2D)](#5-physics-rapier2d)
6. [Audio (Rodio)](#6-audio-rodio)
7. [Gamepad Input (Gilrs)](#7-gamepad-input-gilrs)
8. [GPU Backend (Vulkan)](#8-gpu-backend-vulkan)
9. [Vulkan UI Backend](#9-vulkan-ui-backend)
10. [Vulkan DSL](#10-vulkan-dsl)
11. [3D Rendering](#11-3d-rendering)
12. [Widget Systems](#12-widget-systems)
13. [Test Infrastructure](#13-test-infrastructure)
14. [Rust Implementation Guide](#14-rust-implementation-guide)
15. [File Reference](#15-file-reference)

---

## 1. Architecture Overview

```
+-----------------------------------------------------------+
|                  Simple Application Layer                   |
|  Element Tree -> Diff -> PatchSet -> RenderBackend         |
+-----------------------------------------------------------+
                           |
         +-----------------+------------------+
         |                 |                  |
         v                 v                  v
  +-------------+  +---------------+  +----------------+
  | TuiRenderer |  | HtmlRenderer  |  | VulkanRenderer |
  | (Terminal)  |  | (Web/SSR)     |  | (GPU)          |
  +-------------+  +---------------+  +----------------+
                                              |
+-----------------------------------------------------------+
|                   SFFI Wrapper Layer                        |
|  Two-Tier Pattern: extern fn rt_* -> fn wrapper()          |
+-----------------------------------------------------------+
         |          |          |         |          |
         v          v          v         v          v
    +--------+ +--------+ +--------+ +------+ +--------+
    | Winit  | | Lyon   | |Rapier2D| |Rodio | | Gilrs  |
    |Window  | |Graphics| |Physics | |Audio | |Gamepad |
    +--------+ +--------+ +--------+ +------+ +--------+
```

### SFFI Pattern (All Components)

**Tier 1: Raw FFI** (Simple `extern fn` declarations)
```simple
extern fn rt_winit_window_new(event_loop: i64, w: i64, h: i64, title: text) -> i64
```

**Tier 2: Type-safe Wrappers** (Simple functions with structs)
```simple
fn window_create(event_loop: EventLoop, w: i64, h: i64, title: text) -> Window:
    val handle = rt_winit_window_new(event_loop.handle, w, h, title)
    Window(handle: handle, event_loop: event_loop, is_valid: handle != 0)
```

**Tier 3: Rust Runtime** (to be implemented per component)
```rust
#[no_mangle]
pub extern "C" fn rt_winit_window_new(...) -> i64 { /* implementation */ }
```

---

## 2. Component Stack

| Component | Library | SFFI File | Lines | Extern Fns | Tests | Status |
|-----------|---------|-----------|-------|------------|-------|--------|
| **Windowing** | Winit | `src/app/io/window_ffi.spl` | 750 | 63 | 43 | SFFI complete |
| **2D Graphics** | Lyon | `src/app/io/graphics2d_ffi.spl` | 700 | 57 | 42 | SFFI complete |
| **Physics** | Rapier2D | `src/app/io/rapier2d_ffi.spl` | 620 | 52 | 30+ | SFFI complete |
| **GPU Compute** | Vulkan | `src/app/io/vulkan_ffi.spl` | 301 | 47 | 20+ | SFFI complete |
| **Audio** | Rodio | `src/app/io/audio_ffi.spl` | 550 | 40+ | 40+ | SFFI complete |
| **Gamepad** | Gilrs | `src/app/io/gamepad_ffi.spl` | 400+ | 30+ | 30+ | SFFI complete |
| **Total** | | | **3,321+** | **289+** | **205+** | |

### Rust Implementation Estimates

| Component | Estimated Rust Lines | Compiled Size | Difficulty |
|-----------|---------------------|---------------|------------|
| Winit | 1,000-1,200 | ~800KB | Medium-High |
| Lyon | 800-1,000 | ~300KB | Medium |
| Rapier2D | 800-1,000 | ~500KB | Medium |
| Rodio | 600-800 | ~400KB | Low-Medium |
| Gilrs | 800-1,000 | ~200KB | Low-Medium |
| **Total** | **4,000-5,000** | **~2.2MB** | |

---

## 3. Windowing (Winit)

### Overview

Cross-platform window management with event loop, keyboard/mouse input, and monitor/clipboard support.

**Files:**
- SFFI: `src/app/io/window_ffi.spl` (750 lines, 63 extern fns, 90+ wrappers)
- Tests: `test/unit/app/io/window_ffi_spec.spl` (450 lines, 43 tests)
- Demo: `examples/06_io/graphics/window_creation.spl` (142 lines)

### Features

**Event Loop:** `window_create_event_loop()`, `window_poll_events()`, `window_wait_events()`, `window_run_event_loop()`

**Window Configuration:**
```simple
struct WindowConfig:
    width: i64          # Default: 800
    height: i64         # Default: 600
    title: text         # Default: "Simple Window"
    resizable: bool     # Default: true
    decorations: bool   # Default: true
    transparency: bool  # Default: false
    fullscreen: bool    # Default: false
    # ... 14 customizable properties
```

**Window Management:** Create, destroy, get/set size, position, min/max constraints, visibility, minimize/maximize, fullscreen, decorations, always-on-top, focus, redraw, scale factor, window ID.

**Cursor Control:** Show/hide, grab (FPS games), set position.

**Event System (17 types):**
```simple
enum EventType:
    WindowResized, WindowMoved, WindowCloseRequested, WindowDestroyed
    WindowFocused, WindowUnfocused, WindowScaleFactorChanged
    KeyboardInput, ReceivedCharacter
    MouseButton, MouseMoved, MouseWheel, CursorEntered, CursorLeft
    TouchEvent, RedrawRequested
```

**Keyboard:** 40+ virtual keys (A-Z, 0-9, F1-F12, arrows, modifiers), scancodes, character input.

**Mouse:** Left/Right/Middle buttons, high-precision position (f64), scroll wheel, enter/leave tracking.

**Monitor & Clipboard:** Enumerate monitors (name, size, position, scale), get/set clipboard text.

### Rust Architecture (Recommended: Channel-Based)

Due to Winit's threading requirements (EventLoop owns the thread), use command/event queue:

```rust
enum WindowCommand {
    CreateWindow { id: i64, width: u32, height: u32, title: String },
    SetTitle { id: i64, title: String },
    SetSize { id: i64, width: u32, height: u32 },
    // ...
}

struct WindowManager {
    command_tx: Sender<WindowCommand>,
    event_rx: Receiver<StoredEvent>,
}
```

Main thread (Simple FFI calls) sends commands via channel. Window thread (runs event loop) processes commands and sends events back.

**Platform Notes:**
- **Windows:** HiDPI requires manifest; cursor grab requires active window
- **macOS:** Must run on main thread (Cocoa); Retina scale factor 2.0
- **Linux:** X11 or Wayland; may need libxcb

### Cargo Dependencies

```toml
winit = "0.29"
raw-window-handle = "0.5"  # For graphics integration
clipboard = "0.5"          # Clipboard support
```

---

## 4. 2D Graphics (Lyon)

### Overview

GPU-based 2D vector graphics tessellation. Converts paths and shapes into triangle meshes for GPU rendering.

**Files:**
- SFFI: `src/app/io/graphics2d_ffi.spl` (700 lines, 57 extern fns, 85+ wrappers)
- Tests: `test/unit/app/io/graphics2d_ffi_spec.spl` (450 lines, 42 tests)
- Demo: `examples/06_io/graphics/graphics2d.spl` (222 lines)

### Features

**Path Building (Builder Pattern):**
```simple
val builder = graphics_path_builder_new()
graphics_path_begin(builder, Point2D(x: 0.0, y: 0.0))
graphics_path_line_to(builder, Point2D(x: 100.0, y: 0.0))
graphics_path_quadratic_to(builder, ctrl, end_point)
graphics_path_cubic_to(builder, ctrl1, ctrl2, end_point)
graphics_path_arc_to(builder, center, radius, angle)
graphics_path_close(builder)
val path = graphics_path_build(builder)
```

**Shape Primitives:** Rectangle (regular + rounded), Circle, Ellipse, Polygon (arbitrary vertices), Star (inner/outer radius + point count).

**Path Operations:** Bounding box, point-in-path test, transform (translate, rotate, scale, compose).

**Fill Tessellation:**
```simple
val circle = graphics_circle(Point2D(x: 100.0, y: 100.0), 50.0)
val fill = graphics_fill_tessellate(circle, 0.1)  # tolerance
val vertices = graphics_fill_get_vertices(fill)
val indices = graphics_fill_get_indices(fill)
# Upload to GPU and render
```
Fill rules: EvenOdd, NonZero. Tolerance controls quality vs. performance.

**Stroke Tessellation:**
Line caps (Butt, Square, Round), line joins (Miter, Round, Bevel), miter limit, variable width. Output includes normals for advanced rendering.

**Vertex/Index Buffers:** GPU-ready triangle mesh. Position (x, y), normal (nx, ny). CCW winding. Directly uploadable.

### Tessellation Quality

| Tolerance | Triangles (Circle) | Quality | Use Case |
|-----------|-------------------|---------|----------|
| 0.01 | ~200 | Excellent | Icons, logos |
| 0.1 | ~50 | Good | UI elements |
| 0.5 | ~20 | Acceptable | Large shapes |
| 1.0 | ~10 | Low | Placeholder |

### Use Cases

**Vector UI:** Rounded buttons, styled controls
**Data Visualization:** Line charts, bar charts, pie charts
**Icon Rendering:** Stars, custom shapes
**Shape Transforms:** Translate + rotate + scale compositions

### Cargo Dependencies

```toml
lyon = "1.0"
lyon_tessellation = "1.0"
lyon_path = "1.0"
lyon_geom = "1.0"
```

---

## 5. Physics (Rapier2D)

### Overview

2D physics engine with rigid body dynamics, collision detection, forces, and joints.

**Files:**
- SFFI: `src/app/io/rapier2d_ffi.spl` (620 lines, 52 extern fns, 80+ wrappers)
- Tests: `test/unit/app/io/rapier2d_ffi_spec.spl` (360 lines, 30+ tests)
- Demo: `examples/experiments/physics_rapier2d_demo.spl` (120 lines)

### Features

**Core Types:** `Vector2` (2D math), `Rotation2` (radians/degrees), `Transform2` (position + rotation)

**Physics World:**
```simple
val world = physics_create_world(Vector2(x: 0.0, y: -9.81))
physics_step(world, 1.0 / 60.0)  # 60 FPS timestep
physics_set_gravity(world, Vector2(x: 0.0, y: -20.0))
val stats = physics_world_stats(world)
```

**Rigid Bodies:** Dynamic, Static, Kinematic. Create, get/set position/rotation, get/set velocity (linear + angular), apply force/impulse/torque, mass, damping, sleep management.

**Colliders (Shapes):** Circle, Box, Capsule, Polygon (arbitrary vertices). Offset from body, material (restitution, friction, density), sensor (trigger volumes).

**Collision Detection:** Broadphase + narrowphase. Collision events, contact points, collision pairs, raycasting.

**Joints:** Revolute (hinge), Prismatic (slider), Fixed, Spring. Motor parameters.

### Cargo Dependencies

```toml
rapier2d = "0.17"
nalgebra = "0.32"
```

---

## 6. Audio (Rodio)

### Overview

Audio playback with streaming, spatial audio, and effects.

**Files:**
- SFFI: `src/app/io/audio_ffi.spl` (550 lines, 40+ extern fns)
- Tests: `test/unit/app/io/audio_ffi_spec.spl` (460 lines, 40+ tests)
- Demo: `examples/06_io/multimedia/audio_playback.spl` (230 lines)

### Features

**Audio Engine:** Initialize/shutdown, play sounds from file or memory.

**Playback Control:** Play, pause, resume, stop. Volume, speed, loop, position seek.

**Audio Sources:** WAV, MP3, OGG, FLAC. File and memory sources. Streaming for large files.

**Spatial Audio:** 3D positioning, listener position/orientation, distance attenuation.

**Effects:** Volume, speed, reverb, delay.

### Cargo Dependencies

```toml
rodio = "0.17"
```

---

## 7. Gamepad Input (Gilrs)

### Overview

Cross-platform gamepad/controller input with button/axis mapping and rumble.

**Files:**
- SFFI: `src/app/io/gamepad_ffi.spl` (400+ lines, 30+ extern fns)
- Tests: `test/unit/app/io/gamepad_ffi_spec.spl` (300+ lines, 30+ tests)
- Demo: `examples/06_io/multimedia/gamepad_input.spl`

### Features

**Gamepad Discovery:** Enumerate connected gamepads, detect connect/disconnect.

**Input:** Button states (pressed/released), axis values (sticks, triggers), D-pad. 40+ standard buttons/axes.

**Rumble/Vibration:** Force feedback with intensity and duration.

**Event Model:** Poll-based event queue. Thread-safe, single context per program.

### Cargo Dependencies

```toml
gilrs = "0.10"
```

---

## 8. GPU Backend (Vulkan)

### Overview

GPU compute via SPIR-V. Compiles Simple MIR to SPIR-V bytecode for Vulkan execution.

**Files:**
- SFFI: `src/app/io/vulkan_ffi.spl` (301 lines, 47 extern fns)
- Backend: `src/compiler/backend/vulkan_backend.spl`, `vulkan_type_mapper.spl`
- Architecture: `doc/architecture/vulkan_backend.md`

### Compilation Pipeline

```
Simple Source -> Parser (AST) -> HIR (Type-checked) -> MIR
                                                        |
                                              +---------+---------+
                                              |                   |
                                        Vulkan Backend    Software Fallback
                                              |
                                        SPIR-V Builder
                                              |
                                        SPIR-V Bytecode
                                              |
                                        Runtime FFI (12 functions)
                                              |
                                        Vulkan Runtime
                                              |
                                        GPU Hardware
```

### Runtime FFI (12 functions)

```simple
# Device management
extern fn rt_vk_available() -> i32
extern fn rt_vk_device_create() -> u64
extern fn rt_vk_device_free(handle: u64) -> i32
extern fn rt_vk_device_sync(handle: u64) -> i32

# Buffer management
extern fn rt_vk_buffer_alloc(device: u64, size: u64) -> u64
extern fn rt_vk_buffer_free(buffer: u64) -> i32
extern fn rt_vk_buffer_upload(buffer: u64, data: *const u8, size: u64) -> i32
extern fn rt_vk_buffer_download(buffer: u64, data: *mut u8, size: u64) -> i32

# Kernel management
extern fn rt_vk_kernel_compile(device: u64, spirv: *const u8, len: u64) -> u64
extern fn rt_vk_kernel_free(pipeline: u64) -> i32
extern fn rt_vk_kernel_launch(...) -> i32
extern fn rt_vk_kernel_launch_1d(...) -> i32
```

### Type Mapping (MIR -> SPIR-V)

| TypeId | SPIR-V | Add Op | Div Op (signed) |
|--------|--------|--------|-----------------|
| I32 | `OpTypeInt 32 1` | `OpIAdd` | `OpSDiv` |
| F32 | `OpTypeFloat 32` | `OpFAdd` | `OpFDiv` |
| Bool | `OpTypeBool` | - | - |

### GPU Intrinsics

| MIR | SPIR-V Built-in |
|-----|-----------------|
| `GpuGlobalId(0)` | `gl_GlobalInvocationID.x` |
| `GpuLocalId(0)` | `gl_LocalInvocationID.x` |
| `GpuBarrier` | `OpControlBarrier` |
| `GpuAtomicAdd` | `OpAtomicIAdd` |

### Performance

| Operation | Overhead |
|-----------|----------|
| SPIR-V generation | ~10us |
| Kernel compilation | ~50ms |
| Buffer allocation | ~100us |
| Buffer upload (1MB) | ~2ms |
| Kernel launch | ~50us |

---

## 9. Vulkan UI Backend

### Overview

GPU-accelerated UI rendering backend using Vulkan. Integrates with the Element/PatchSet abstraction for efficient incremental updates.

### Architecture

```
+-----------------------------------------------------------+
|               CPU Layer (VulkanRenderer)                    |
|  Layout Engine -> Element Processor -> Resource Manager    |
+-----------------------------------------------------------+
                    | Command Stream
+-----------------------------------------------------------+
|               GPU Layer (Vulkan Core)                       |
|  Device/Queue | Render Pass | Command Buffers              |
|  Buffer Mgr   | Text Render | Shader Manager               |
+-----------------------------------------------------------+
```

### CPU Responsibilities

- **Layout:** Flexbox/Grid calculation, text measurement, hit testing, dirty rectangle tracking
- **Element Processing:** Tree traversal, style resolution, diff/patch generation, draw call batching
- **Vulkan Setup:** Instance/device creation, swapchain management, command buffer recording

### GPU Responsibilities

- **Rendering:** Vertex transform, rasterization, fragment shading, blending, MSAA
- **Effects:** Rounded corners (SDF), drop shadows (gaussian blur), gradients, glow/bloom
- **Text:** SDF text rendering, subpixel rendering, font atlas management

### Pipeline Types

| Pipeline | Purpose | Shader |
|----------|---------|--------|
| SolidColor | Filled rectangles | Basic color output |
| RoundedRect | Rounded corners | SDF distance field |
| Textured | Images | Texture sampling |
| Text | SDF text | Font atlas + smoothstep |
| Gradient | Linear/radial gradients | Interpolation |
| Shadow | Drop shadows | Gaussian blur |

### Shader Examples

**Rounded Rectangle (SDF):**
```glsl
float roundedBoxSDF(vec2 p, vec2 size, vec4 radii) {
    float r = p.x > 0.0
        ? (p.y > 0.0 ? radii.w : radii.z)
        : (p.y > 0.0 ? radii.x : radii.y);
    vec2 q = abs(p) - size + r;
    return min(max(q.x, q.y), 0.0) + length(max(q, 0.0)) - r;
}
```

**SDF Text:**
```glsl
float dist = texture(fontAtlas, fragUV).a;
float alpha = smoothstep(0.5 - fwidth(dist), 0.5 + fwidth(dist), dist);
outColor = vec4(fragColor.rgb, fragColor.a * alpha);
```

### Frame Rendering Flow

1. **Begin Frame:** Acquire swapchain image, reset command buffer
2. **Layout (CPU):** Compute layout, cache results, determine dirty regions
3. **Process (CPU):** Traverse element tree, generate draw list (vertices/indices), batch by pipeline
4. **Record (CPU->GPU):** Bind pipelines, set viewport/scissor, issue draw calls
5. **Present:** Submit command buffer, present swapchain image

### Incremental Updates (Patches)

Receive PatchSet -> Identify affected elements -> Partial layout update -> Minimal re-processing -> Selective GPU upload -> Optimized rendering with scissor rects.

### Memory Strategy

- **Triple Buffering:** 3 sets of vertex/index/uniform buffers, rotated per frame
- **Staging Buffers:** CPU-visible for uploads, GPU-local for rendering
- **Buffer Pooling:** Reuse across frames, grow as needed
- **Font Atlas:** Single SDF texture, dynamic rect packing, regenerate when full

---

## 10. Vulkan DSL

### Problem: Vulkan Verbosity

Vulkan "Hello Triangle" requires ~800-1,000 lines in C/C++. Simple aims to reduce this by 95-98%.

### Simple Language Features That Help

| Feature | Vulkan Problem Solved |
|---------|----------------------|
| Smart defaults | 50+ struct fields per pipeline |
| `with` context blocks | Manual resource lifecycle |
| Actor model | Synchronization (semaphores, fences) |
| Immutable objects | Data races in GPU/CPU sharing |
| Compile-time contracts | Invalid state crashes |
| AOP weaving | Scattered validation/logging |
| Macros | Repetitive descriptors/vertex formats |
| Underscore literals | Verbose constructors (`100_200_loc`) |
| Custom `FromLiteral` | User-defined type literals (`1_0_0_0_quat`) |
| Multi-value units | Unit mismatches (`100_200_m2`) |

### Builder Pattern DSL (Primary)

```simple
import vulkan.{Device, Swapchain, Pipeline, Buffer}

#[vertex]
struct Vertex:
    #[location(0)] position: Vec2
    #[location(1)] color: Vec3

fn main():
    window = Window.new("Vulkan Triangle", 800_600_size)
    device = Device.new()                    # Auto-selects best GPU
    swapchain = Swapchain.new(device)        # VSync, double buffer, best format
    pipeline = Pipeline.new()
        .render_pass_from(swapchain)
    vertex_buffer = Buffer.vertex(VERTICES)

    while with window.frame() as frame:
        frame.draw(pipeline, vertex_buffer)
        # frame automatically ends (RAII)
```

**~20 lines vs ~1,000 in C++ (98% reduction)**

### Immediate Mode DSL

```simple
import gfx.immediate as im

fn render():
    with im:
        rect(100_100_200_50_rect.color(Color.blue))
        text(110_120_loc, "Hello Vulkan!")
        line_3d(0_0_0_loc3, 1_1_1_loc3, Color.green)
```

### Underscore Literal Types

| Type | Suffix | Example | Description |
|------|--------|---------|-------------|
| `Loc2` | `_loc` | `100_200_loc` | 2D location |
| `Loc3` | `_loc3` | `1_2_3_loc3` | 3D location |
| `Size2` | `_size` | `50_30_size` | 2D size |
| `Rect` | `_rect` | `0_0_100_50_rect` | Rectangle |
| `Color` | `_rgb` | `255_128_0_rgb` | RGB color |
| `Vec3` | `_vec3` | `1_0_0_vec3` | Float vector |
| Custom | `_quat` | `1_0_0_0_quat` | User-defined via `FromLiteral` |

### SDN Configuration with Functional Defaults

```sdn
device:
    prefer_discrete: true
    graphics_queue: @fn(device) => device.find_queue_family(Graphics)

swapchain:
    format: @fn(surface) => surface.best_format([BGRA8_SRGB, RGBA8_SRGB])
    present_mode: @fn(surface) => surface.best_present_mode([Mailbox, Fifo])
    image_count: @fn(caps) => clamp(3, caps.min_image_count, caps.max_image_count)

pipeline "main":
    shaders:
        vertex: "shaders/main.vert.spv"
        fragment: "shaders/main.frag.spv"
    multisample:
        samples: @fn(device) => device.best_sample_count([8, 4, 2, 1])
```

Functional defaults (`@fn()`) compute optimal values at runtime based on device capabilities.

### Other DSLs

- **Declarative Scene:** Scene graphs with camera, objects, lights, materials
- **Compute DSL:** `#[compute(local_size = (256, 1, 1))]` annotations
- **Shader DSL:** Type-safe shader definitions with compile-time validation

---

## 11. 3D Rendering

### Architecture

```
Application Layer (Scene, Camera, Controls)
    |
Scene Graph Layer (SceneNode, Transform, Component)
    |
Rendering System (Renderer3D, Pipeline, Materials, Culling, Lighting, Shadows)
    |
Resource Layer (Mesh, Texture, Shader, Buffer managers)
    |
Vulkan Backend (Device, Commands, Swapchain, Descriptors, Render Passes, Pipelines)
```

### Material System

PBR (Physically Based Rendering), Phong, and Unlit materials. Shadow mapping with CSM/VSM/PCF variants.

---

## 12. Widget Systems

### Material Design Widgets (GUI)

Defined in `test/unit/app/ui/gui_widgets_spec.spl`:

- **Card:** Elevated content containers with shadows
- **Chip:** Deletable tags with icons
- **Avatar:** User profile images with initials fallback
- **Badge:** Numeric counters and labels
- **Tooltip:** Contextual help text
- **Divider:** Visual content separators

### TUI (Terminal UI) Widgets

Defined in `test/unit/app/ui/widgets_spec.spl`:

- **Menu:** Keyboard-navigable selections
- **Dialog:** OK/Cancel, Yes/No prompts
- **ProgressBar:** Loading indicators
- **TextInput:** Single-line text entry with cursor
- **ScrollList:** Large lists with automatic scrolling

---

## 13. Test Infrastructure

### GUI Screenshot & Diagram Generation

**Screenshot Capture:**
- `@gui` tag on tests marks them for visual capture
- Before/after screenshots stored in `doc/spec/image/`
- `--refresh-gui-image` CLI flag forces recapture
- ANSI-to-image conversion for TUI tests
- Vulkan framebuffer capture for GPU tests

**Diagram Generation:**
- Sequence diagrams from test method call flows
- Class diagrams from traced calls
- Architecture diagrams from component interactions
- Mermaid format output
- Linked to source tests for bidirectional navigation

**CLI:**
```bash
simple test --tag gui                    # Run GUI tests only
simple test --refresh-gui-image          # Force recapture all screenshots
simple test --seq-diagram               # Generate sequence diagrams
simple test --diagram-all               # Generate all diagram types
```

### Test Coverage

| Component | Tests | File |
|-----------|-------|------|
| Window FFI | 43 | `test/unit/app/io/window_ffi_spec.spl` |
| Graphics2D FFI | 42 | `test/unit/app/io/graphics2d_ffi_spec.spl` |
| Rapier2D FFI | 30+ | `test/unit/app/io/rapier2d_ffi_spec.spl` |
| Vulkan Window | 10+ | `test/unit/app/ui/vulkan_window_spec.spl` |
| Vulkan Renderer | 15+ | `test/unit/app/ui/vulkan_renderer_spec.spl` |
| GUI Widgets | 20+ | `test/unit/app/ui/gui_widgets_spec.spl` |
| TUI Widgets | 15+ | `test/unit/app/ui/widgets_spec.spl` |
| GPU Render Unit | varies | `test/lib_extended/gpu_render_unit_spec.spl` |
| GPU Render Integration | varies | `test/lib_extended/gpu_render_integration_spec.spl` |

---

## 14. Rust Implementation Guide

### Handle Management Pattern (All Components)

All components use the same pattern: global `HashMap<i64, T>` protected by `Mutex`, with atomic counter for unique handles.

```rust
use std::collections::HashMap;
use std::sync::Mutex;

lazy_static! {
    static ref OBJECTS: Mutex<HashMap<i64, ObjectType>> = Mutex::new(HashMap::new());
    static ref NEXT_ID: Mutex<i64> = Mutex::new(1);
}

fn allocate_handle<T>(store: &Mutex<HashMap<i64, T>>, object: T) -> i64 {
    let mut map = store.lock().unwrap();
    let mut next_id = NEXT_ID.lock().unwrap();
    let id = *next_id;
    *next_id += 1;
    map.insert(id, object);
    id
}
```

### Winit Implementation Checklist

- [ ] Add `winit`, `raw-window-handle`, `clipboard` to Cargo.toml
- [ ] Command/event queue architecture (mpsc channels)
- [ ] Window thread runner
- [ ] Event loop management (new, free, poll)
- [ ] Window creation/destruction
- [ ] Window property getters/setters
- [ ] Event conversion and storage (17 event types)
- [ ] Keyboard/mouse event handling
- [ ] Monitor queries, clipboard operations

### Lyon Implementation Checklist

- [ ] Add `lyon`, `lyon_tessellation`, `lyon_path`, `lyon_geom` to Cargo.toml
- [ ] Path builder (new, begin, line_to, curves, close, build)
- [ ] Shape primitives (rectangle, circle, ellipse, polygon, star)
- [ ] Path operations (free, bounds, contains_point)
- [ ] Fill tessellation (basic + fill rules)
- [ ] Stroke tessellation (basic + options: caps, joins, miter)
- [ ] Vertex/index buffer access (size, get_position, get_normal)
- [ ] Transform operations

### Rapier2D Implementation Checklist

- [ ] Add `rapier2d`, `nalgebra` to Cargo.toml
- [ ] Physics world management
- [ ] Rigid body creation/management (Dynamic, Static, Kinematic)
- [ ] Collider shapes (Circle, Box, Capsule, Polygon)
- [ ] Collision detection and events
- [ ] Joint system (Revolute, Prismatic, Fixed, Spring)
- [ ] Raycasting

### Rodio Implementation Checklist

- [ ] Add `rodio` to Cargo.toml
- [ ] Audio engine init/shutdown
- [ ] Sound loading (WAV, MP3, OGG, FLAC)
- [ ] Playback control (play, pause, stop, seek)
- [ ] Volume, speed, loop settings
- [ ] Spatial audio (3D positioning)
- [ ] Audio effects

### Gilrs Implementation Checklist

- [ ] Add `gilrs` to Cargo.toml
- [ ] Gamepad discovery and hotplug
- [ ] Button/axis state reading
- [ ] D-pad support
- [ ] Rumble/force feedback
- [ ] Event queue polling

---

## 15. File Reference

### SFFI Wrappers

| File | Component | Lines |
|------|-----------|-------|
| `src/app/io/window_ffi.spl` | Windowing (Winit) | 750 |
| `src/app/io/graphics2d_ffi.spl` | 2D Graphics (Lyon) | 700 |
| `src/app/io/rapier2d_ffi.spl` | Physics (Rapier2D) | 620 |
| `src/app/io/vulkan_ffi.spl` | GPU Compute (Vulkan) | 301 |
| `src/app/io/audio_ffi.spl` | Audio (Rodio) | 550 |
| `src/app/io/gamepad_ffi.spl` | Gamepad (Gilrs) | 400+ |

### Compiler Backend

| File | Purpose |
|------|---------|
| `src/compiler/backend/vulkan_backend.spl` | Vulkan shader compilation |
| `src/compiler/backend/vulkan_type_mapper.spl` | Type mapping for Vulkan |

### Tests

| File | Tests |
|------|-------|
| `test/unit/app/io/window_ffi_spec.spl` | 43 |
| `test/unit/app/io/graphics2d_ffi_spec.spl` | 42 |
| `test/unit/app/io/rapier2d_ffi_spec.spl` | 30+ |
| `test/unit/app/ui/vulkan_window_spec.spl` | 10+ |
| `test/unit/app/ui/vulkan_renderer_spec.spl` | 15+ |
| `test/unit/app/ui/gui_widgets_spec.spl` | 20+ |
| `test/unit/app/ui/widgets_spec.spl` | 15+ |
| `test/feature/vulkan_spec.spl` | varies |

### Examples

| File | Purpose |
|------|---------|
| `examples/06_io/graphics/window_creation.spl` | Winit event loop demo |
| `examples/06_io/graphics/graphics2d.spl` | Lyon tessellation demo |
| `examples/experiments/physics_rapier2d_demo.spl` | Rapier2D physics demo |
| `examples/06_io/multimedia/audio_playback.spl` | Rodio audio demo |
| `examples/06_io/multimedia/gamepad_input.spl` | Gilrs gamepad demo |

---

## References

- Winit: https://docs.rs/winit/
- Lyon: https://docs.rs/lyon/
- Rapier2D: https://rapier.rs/
- Rodio: https://docs.rs/rodio/
- Gilrs: https://docs.rs/gilrs/
- Vulkan: https://www.vulkan.org/
- SPIR-V: https://www.khronos.org/spir/
- rspirv: https://docs.rs/rspirv/
- ash (Vulkan bindings): https://docs.rs/ash/
- gpu-allocator: https://docs.rs/gpu-allocator/
- SDF Text: https://github.com/Chlumsky/msdfgen
- Dear ImGui (reference): https://github.com/ocornut/imgui
