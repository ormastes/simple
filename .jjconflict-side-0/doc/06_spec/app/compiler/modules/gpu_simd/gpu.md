## Part 2: GPU Compute

### Execution Model (SIMT)

A GPU kernel executes across many GPU threads ("work-items"). Threads are grouped into **thread groups** (CUDA blocks / OpenCL work-groups). A kernel sees:

- `this.index()` / `gpu.global_id()` - global linear index (or tuple for multi-d)
- `this.thread_index()` / `gpu.local_id()` - index within the group
- `this.group_index()` / `gpu.group_id()` - group id

Host call semantics: Calling a GPU kernel from host code enqueues a kernel launch (async by default). Synchronization is via runtime APIs (`ctx.sync()`, `Device.wait()`).

### Device and Context

```simple
use gpu

# Query available devices
let devices = gpu.devices()
for d in devices:
    print "Device: {d.name}, Memory: {d.memory_mb}MB"

# Create compute context
let ctx = gpu.Context.new(device: devices[0])

# Or use default device
let ctx = gpu.Context.default()
```

### GPU Buffers

```simple
# Allocate device buffer
let buf: gpu.Buffer[f32] = ctx.alloc(1024)  # 1024 f32 elements

# Upload data to GPU
let host_data: [f32; 1024] = [...]
buf.upload(host_data)

# Download data from GPU
let result = buf.download()  # Returns [f32; 1024]

# Map buffer for direct access (advanced)
with buf.map() as mapped:
    mapped[0] = 42.0
```

### Compute Kernels

Kernels are functions that run on the GPU. Two annotation styles are supported:

#### Style 1: `#[gpu]` Attribute

```simple
#[gpu]
fn vector_add(a: &[f32], b: &[f32], out: &mut [f32]):
    let idx = gpu.global_id()
    if idx < out.len():
        out[idx] = a[idx] + b[idx]
```

#### Style 2: `@simd` Annotation (with bounds policy)

```simple
@simd
fn vector_add(a: f32[], b: f32[], out: f32[]):
    let i = this.index()
    out[i] = a[i] + b[i]
```

**Key difference:** `@simd` implies a default bounds policy (`@bounds(default=return, strict=true)`) that automatically handles out-of-bounds accesses by returning from the thread. The `#[gpu]` style requires explicit bounds checks.

#### `@simd` Parameters (optional)

```simple
@simd(grid_size=1024, group_size=256, stream=0, dim=1)
fn my_kernel(...):
    ...
```

- `grid_size` - total threads (scalar or tuple)
- `group_size` - threads per group (scalar or tuple)
- `stream` - queue/stream id
- `dim` - explicit dimensionality (1, 2, or 3)

### Launching Kernels

```simple
# Create buffers
let a_buf = ctx.alloc_upload(host_a)
let b_buf = ctx.alloc_upload(host_b)
let out_buf = ctx.alloc[f32](1024)

# Launch kernel
ctx.launch(
    kernel: vector_add,
    global_size: [1024],       # Total work items
    local_size: [256],         # Work group size (optional)
    args: [a_buf, b_buf, out_buf]
)

# Wait for completion
ctx.sync()

# Get results
let result = out_buf.download()
```

### Work Item Intrinsics

Available inside GPU kernel functions:

```simple
gpu.global_id()           # 1D global index
gpu.global_id(dim)        # Multi-dimensional global index
gpu.local_id()            # Local index within work group
gpu.local_id(dim)
gpu.group_id()            # Work group index
gpu.group_id(dim)
gpu.global_size()         # Total number of work items
gpu.local_size()          # Work group size
gpu.num_groups()          # Number of work groups

# Alternative @simd style
this.index()              # global linear index
this.thread_index()       # index within group
this.group_index()        # group id
```

### Shared Memory

Work groups can share fast local memory:

```simple
#[gpu]
fn reduce_sum(input: &[f32], output: &mut [f32], n: u32):
    # Shared memory declaration
    shared let local_data: [f32; 256]

    let gid = gpu.global_id()
    let lid = gpu.local_id()

    # Load to shared memory
    local_data[lid] = if gid < n: input[gid] else: 0.0

    # Synchronize work group
    gpu.barrier()

    # Parallel reduction in shared memory
    let mut stride = gpu.local_size() / 2
    while stride > 0:
        if lid < stride:
            local_data[lid] += local_data[lid + stride]
        gpu.barrier()
        stride /= 2

    # Write result
    if lid == 0:
        output[gpu.group_id()] = local_data[0]
```

### Thread Groups and Barriers

```simple
# Within kernels, thread_group is an implicit object
thread_group.id           # Group ID
thread_group.size         # Group size
thread_group.barrier()    # Synchronize threads in group

# Or use gpu.* functions
gpu.barrier()             # Synchronize all threads in work group
gpu.mem_fence()           # Memory fence (ensure writes visible)
gpu.barrier_and_fence()   # Both barrier and fence
```

### Atomic Operations

```simple
#[gpu]
fn histogram(input: &[u32], bins: &mut [u32]):
    let idx = gpu.global_id()
    if idx < input.len():
        let bin = input[idx]
        gpu.atomic_add(&bins[bin], 1)

# Available atomics:
gpu.atomic_add(ptr, val)
gpu.atomic_sub(ptr, val)
gpu.atomic_min(ptr, val)
gpu.atomic_max(ptr, val)
gpu.atomic_and(ptr, val)
gpu.atomic_or(ptr, val)
gpu.atomic_xor(ptr, val)
gpu.atomic_exchange(ptr, val)
gpu.atomic_compare_exchange(ptr, expected, desired)
```

---


## Part 9: Vulkan Backend

### Overview

The Vulkan backend provides both **compute** and **graphics** capabilities, making it the most versatile GPU backend in Simple. While CUDA excels at compute-only workloads on NVIDIA hardware, Vulkan supports:

- **Cross-platform**: Windows, Linux, macOS (via MoltenVK), Android, iOS
- **Compute shaders**: Equivalent to CUDA kernels but with broader hardware support
- **Graphics pipeline**: Vertex/fragment/geometry shaders for rendering
- **Unified API**: Single backend for both compute and visualization tasks
- **Modern features**: Ray tracing, mesh shaders, descriptor indexing

### 9.1 Vulkan Compute Backend

Vulkan compute shaders use the same `@simd` / `#[gpu]` kernel syntax as CUDA:

```simple
use gpu.vulkan

# Create Vulkan context (auto-selects best device)
let ctx = vulkan.Context.new()

# Or specify device
let device = vulkan.Device.new(device_index: 0)
let ctx = vulkan.Context.new(device: device)

# Allocate buffers (same API as CUDA)
let a_buf = ctx.alloc_upload(host_a)
let b_buf = ctx.alloc_upload(host_b)
let out_buf = ctx.alloc[f32](1024)

# Define compute kernel
#[gpu(backend=:vulkan)]
fn vector_add(a: &[f32], b: &[f32], out: &mut [f32]):
    let idx = gpu.global_id()
    if idx < out.len():
        out[idx] = a[idx] + b[idx]

# Launch kernel (compiled to SPIR-V)
ctx.launch(
    kernel: vector_add,
    global_size: [1024],
    local_size: [256],
    args: [a_buf, b_buf, out_buf]
)

# Wait and retrieve results
ctx.sync()
let result = out_buf.download()
```

**Backend Selection**: The compiler automatically generates SPIR-V for Vulkan kernels. Specify `backend=:vulkan` explicitly or let the runtime choose based on available hardware.

### 9.2 Vulkan Graphics Pipeline

The graphics pipeline API uses Simple's builder pattern with maximum defaults:

#### Window and Surface

```simple
use graphics.vulkan

# Create window (auto-initializes Vulkan)
let window = Window.new(
    title: "My App",
    width: 1920,
    height: 1080
)

# Or with full configuration
let window = Window.new(
    title: "Advanced Graphics",
    width: 3840,
    height: 2160,
    vsync: true,
    msaa: 4,                    # 4x MSAA
    depth_buffer: true,
    validation_layers: true     # Enable debug layers
)
```

#### Shaders

Shaders are defined inline with the `#[vertex]` and `#[fragment]` attributes:

```simple
# Vertex shader
#[vertex]
fn vertex_main(position: vec3[f32], color: vec3[f32]) -> VertexOutput:
    var output: VertexOutput
    output.position = vec4[position.x, position.y, position.z, 1.0]
    output.color = color
    return output

# Fragment shader
#[fragment]
fn fragment_main(color: vec3[f32]) -> vec4[f32]:
    return vec4[color.x, color.y, color.z, 1.0]

# Compile to SPIR-V and create pipeline
let pipeline = Pipeline.new(
    vertex: vertex_main,
    fragment: fragment_main
)
```

Or load pre-compiled SPIR-V:

```simple
let pipeline = Pipeline.new(
    vertex_spirv: "shaders/vert.spv",
    fragment_spirv: "shaders/frag.spv"
)
```

#### Vertex Buffers and Attributes

```simple
# Define vertex structure
struct Vertex:
    position: vec3[f32]
    color: vec3[f32]
    texcoord: vec2[f32]

# Create vertex buffer
let vertices: [Vertex; 3] = [
    Vertex { position: vec3[0.0, -0.5, 0.0], color: vec3[1.0, 0.0, 0.0], texcoord: vec2[0.5, 0.0] },
    Vertex { position: vec3[0.5, 0.5, 0.0], color: vec3[0.0, 1.0, 0.0], texcoord: vec2[1.0, 1.0] },
    Vertex { position: vec3[-0.5, 0.5, 0.0], color: vec3[0.0, 0.0, 1.0], texcoord: vec2[0.0, 1.0] },
]

let vertex_buffer = ctx.create_vertex_buffer(vertices)

# Create index buffer (optional)
let indices: [u16; 3] = [0, 1, 2]
let index_buffer = ctx.create_index_buffer(indices)
```

#### Render Loop

```simple
# Main render loop using while-with context manager
# Loop continues while window.frame() returns a valid frame
while with window.frame() as frame:
    # Clear screen
    frame.clear([0.0, 0.0, 0.0, 1.0])  # RGBA

    # Bind pipeline and draw
    frame.bind(pipeline)
    frame.draw(vertex_buffer, vertex_count: 3)

    # Or indexed draw
    frame.draw_indexed(vertex_buffer, index_buffer, index_count: 3)

# Loop exits when window closes (frame() returns nil)
```

**Alternative (traditional nested approach):**
```simple
while !window.should_close():
    with window.frame() as frame:
        frame.draw(vertex_buffer, vertex_count: 3)
    window.poll_events()
```

The `while with window.frame()` construct:
1. Acquires next swapchain image
2. Begins command buffer
3. Executes drawing commands
4. Ends command buffer on exit
5. Submits to queue
6. Presents to screen

#### Descriptor Sets and Uniforms

```simple
# Define uniform buffer structure
struct ModelViewProj:
    model: mat4[f32]
    view: mat4[f32]
    proj: mat4[f32]

# Declare descriptor set with macro
#[descriptor_set(binding=0)]
struct SceneDescriptors:
    #[binding(0)] mvp: UniformBuffer[ModelViewProj]
    #[binding(1)] albedo: Texture2D
    #[binding(2)] normal: Texture2D
    #[binding(3)] sampler: Sampler

# Create descriptor set
let mvp_data = ModelViewProj { ... }
let mvp_buffer = ctx.create_uniform_buffer(mvp_data)

let albedo = ctx.load_texture("textures/albedo.png")
let normal = ctx.load_texture("textures/normal.png")
let sampler = ctx.create_sampler(
    filter: :linear,
    wrap: :repeat
)

let descriptors = SceneDescriptors.new(
    mvp: mvp_buffer,
    albedo: albedo,
    normal: normal,
    sampler: sampler
)

# Bind descriptors in render loop
while with window.frame() as frame:
    frame.bind(pipeline)
    frame.bind_descriptors(descriptors)
    frame.draw(vertex_buffer, vertex_count: vertex_count)
```

### 9.3 Advanced Graphics Features

#### Depth Testing and Stencil

```simple
let pipeline = Pipeline.new(
    vertex: vertex_main,
    fragment: fragment_main,
    depth_test: true,           # Enable depth testing
    depth_write: true,          # Write to depth buffer
    depth_compare: :less,       # Depth comparison function
    stencil_test: true,         # Enable stencil testing
    stencil_func: :always,
    stencil_op_pass: :replace
)
```

#### Multisampling (MSAA)

```simple
let window = Window.new(
    title: "MSAA Demo",
    width: 1920,
    height: 1080,
    msaa: 4                     # 4x MSAA
)

# Pipeline automatically uses MSAA from window config
let pipeline = Pipeline.new(
    vertex: vertex_main,
    fragment: fragment_main
)
```

#### Multiple Render Passes

```simple
# Define render passes
let shadow_pass = RenderPass.new(
    attachments: [depth_attachment],
    clear_depth: 1.0
)

let main_pass = RenderPass.new(
    attachments: [color_attachment, depth_attachment],
    clear_color: [0.0, 0.0, 0.0, 1.0],
    clear_depth: 1.0
)

# Execute render passes
with window.frame() as frame:
    # Shadow pass
    frame.begin_pass(shadow_pass)
    frame.bind(shadow_pipeline)
    frame.draw(shadow_objects)
    frame.end_pass()

    # Main pass (uses shadow map from previous pass)
    frame.begin_pass(main_pass)
    frame.bind(main_pipeline)
    frame.bind_descriptors(main_descriptors)  # Includes shadow map
    frame.draw(scene_objects)
    frame.end_pass()
```

#### Compute + Graphics Pipeline

Combine compute and graphics in a single frame:

```simple
with window.frame() as frame:
    # Compute pass (particle simulation)
    frame.dispatch_compute(
        kernel: update_particles,
        global_size: [num_particles],
        local_size: [256]
    )

    # Barrier to ensure compute completes
    frame.barrier()

    # Graphics pass (render particles)
    frame.bind(particle_pipeline)
    frame.draw(particle_buffer, vertex_count: num_particles)
```

### 9.4 Texture and Sampling

```simple
# Load texture from file
let texture = ctx.load_texture("assets/brick_wall.png")

# Or create texture from data
let texture = ctx.create_texture_2d(
    width: 512,
    height: 512,
    format: :rgba8,
    data: pixel_data
)

# Create sampler
let sampler = ctx.create_sampler(
    filter: :linear,            # Linear filtering
    mipmap_mode: :linear,       # Trilinear filtering
    wrap: :repeat,              # Repeat wrapping
    anisotropy: 16.0            # 16x anisotropic filtering
)

# Use in shader (automatic descriptor binding)
#[fragment]
fn textured_fragment(texcoord: vec2[f32], tex: Texture2D, samp: Sampler) -> vec4[f32]:
    return tex.sample(samp, texcoord)
```

### 9.5 Memory Management

Vulkan uses explicit memory management with automatic cleanup via RAII:

```simple
# Buffers are automatically freed when they go out of scope
{
    let vertex_buffer = ctx.create_vertex_buffer(vertices)
    # ... use buffer ...
}  # vertex_buffer freed here

# Manual cleanup if needed
vertex_buffer.destroy()

# Memory statistics
let stats = ctx.memory_stats()
print "GPU Memory Used: {stats.used_mb}MB / {stats.total_mb}MB"
```

### 9.6 Synchronization

```simple
# Wait for all GPU operations to complete
ctx.sync()

# Wait for specific fence
let fence = ctx.create_fence()
ctx.submit_with_fence(commands, fence)
fence.wait()

# Semaphores for inter-queue synchronization
let semaphore = ctx.create_semaphore()
ctx.submit_with_signal(compute_commands, semaphore)
ctx.submit_with_wait(graphics_commands, semaphore)
```

### 9.7 Vulkan-Specific Features

#### Ray Tracing (if supported)

```simple
if ctx.device.supports_ray_tracing():
    # Define ray tracing pipeline
    let rt_pipeline = RayTracingPipeline.new(
        ray_gen: ray_gen_shader,
        closest_hit: closest_hit_shader,
        miss: miss_shader
    )

    # Build acceleration structure
    let blas = ctx.build_bottom_level_as(geometry)
    let tlas = ctx.build_top_level_as(instances)

    # Trace rays
    with window.frame() as frame:
        frame.trace_rays(
            pipeline: rt_pipeline,
            width: 1920,
            height: 1080,
            depth: 1
        )
```

#### Mesh Shaders (if supported)

```simple
if ctx.device.supports_mesh_shaders():
    #[mesh]
    fn mesh_shader(group_id: vec3[u32]) -> MeshOutput:
        # Generate mesh procedurally
        ...

    #[fragment]
    fn fragment_shader(...) -> vec4[f32]:
        ...

    let pipeline = Pipeline.new(
        mesh: mesh_shader,
        fragment: fragment_shader
    )
```

### 9.8 Backend Selection and Interoperability

```simple
# Query available backends
let backends = gpu.available_backends()
print backends  # [:vulkan, :cuda, :software]

# Force specific backend
let ctx = gpu.Context.new(backend: :vulkan)

# Use same kernel on multiple backends
#[gpu]
fn my_kernel(data: &mut [f32]):
    let idx = gpu.global_id()
    data[idx] *= 2.0

# Runtime backend selection
let backend = if has_nvidia_gpu(): :cuda else: :vulkan
let ctx = gpu.Context.new(backend: backend)
ctx.launch(kernel: my_kernel, ...)
```

### 9.9 Integration with UI Frameworks

Vulkan backend integrates seamlessly with Simple's UI frameworks:

```simple
# SUI (Simple UI) with Vulkan rendering
use sui
use graphics.vulkan

let app = sui.App.new(
    title: "My UI App",
    width: 1280,
    height: 720,
    backend: :vulkan          # Use Vulkan renderer
)

app.render \frame:
    frame.container(
        background: [0.2, 0.2, 0.2, 1.0],
        children: [
            frame.text("Hello Vulkan!", size: 24),
            frame.button("Click Me", on_click: \: print "Clicked!")
        ]
    )

app.run()
```

**Electron Integration**:

```simple
use electron
use graphics.vulkan

let app = electron.App.new()
let window = app.create_window(
    title: "Vulkan in Electron",
    width: 1920,
    height: 1080,
    webgl_backend: :vulkan    # Use Vulkan for WebGL
)

window.load_file("index.html")
app.run()
```

**VSCode Extension with Vulkan Preview**:

```simple
use vscode
use graphics.vulkan

# Register custom preview provider
vscode.register_preview_provider(
    language: "simple",
    render: \document:
        let canvas = vscode.create_canvas(backend: :vulkan)
        # Render document using Vulkan
        canvas.render(\frame:
            # ... Vulkan rendering code ...
        )
        return canvas
)
```

### 9.10 Performance Considerations

**Vulkan vs CUDA**:
- **Vulkan**: Better for graphics + compute hybrid workloads, cross-platform
- **CUDA**: Better for pure compute on NVIDIA GPUs (more mature tooling)
- **Rule of thumb**: Use CUDA for NVIDIA-only compute, Vulkan for everything else

**Optimization Tips**:
1. **Minimize state changes**: Group draw calls by pipeline/descriptors
2. **Use push constants**: For small, frequently updated uniforms
3. **Prefer staging buffers**: For large uploads/downloads
4. **Enable validation layers**: During development only (significant overhead)
5. **Profile with RenderDoc**: Vulkan-native profiling tool

---

