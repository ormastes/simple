# Unified GPU Interface Plan - CUDA/Vulkan Compatibility

**Date:** 2025-12-26
**Goal:** Create a unified Simple interface that works seamlessly across CUDA (compute) and Vulkan (compute + graphics) backends
**Status:** Planning Phase

## Overview

This plan ensures that drawing and compute interfaces are compatible across CUDA and Vulkan backends, enabling:
- **Portability**: Same Simple code works on NVIDIA (CUDA), AMD/Intel/Apple (Vulkan), and CPU fallback
- **Specialization**: Leverage backend-specific features when needed
- **Gradual Migration**: Easy to start with one backend and add others later
- **ML Integration**: Tensor operations compatible with PyTorch/JAX workflows

## API Compatibility Matrix

### 1. Device Management

| Operation | CUDA | Vulkan | Simple Unified Interface | Notes |
|-----------|------|--------|--------------------------|-------|
| **List devices** | `cudaGetDeviceCount()` | `vkEnumeratePhysicalDevices()` | `gpu.devices()` | Returns array of device info |
| **Select device** | `cudaSetDevice(id)` | Device selection in `vkCreateDevice()` | `gpu.Context.new(device: devices[0])` | Auto-selects best by default |
| **Device properties** | `cudaGetDeviceProperties()` | `vkGetPhysicalDeviceProperties()` | `device.name`, `device.memory_mb`, `device.compute_capability` | Normalized properties |
| **Multi-GPU** | `cudaSetDevice()` per thread | Multiple `VkDevice` instances | `gpu.Context.new(device: d)` | One context per device |
| **Default device** | `cudaSetDevice(0)` | First suitable device | `gpu.Context.default()` | Auto-selects discrete GPU |

**Implementation:**
```simple
# Unified interface - works with both backends
let devices = gpu.devices()  # Backend-agnostic
for d in devices:
    print "Device: {d.name}, Type: {d.type}, Memory: {d.memory_mb}MB"
    print "  Compute: {d.compute_capability}, Graphics: {d.has_graphics}"

# Create context (auto-detects backend)
let ctx = gpu.Context.new(device: devices[0])  # May be CUDA or Vulkan
# Or: let ctx = gpu.Context.default()
```

### 2. Memory Management

| Operation | CUDA | Vulkan | Simple Unified Interface | Notes |
|-----------|------|--------|--------------------------|-------|
| **Allocate buffer** | `cudaMalloc()` | `vkCreateBuffer()` + `vkAllocateMemory()` | `ctx.alloc[T](count)` | Returns `gpu.Buffer[T]` |
| **Upload to GPU** | `cudaMemcpy(..., cudaMemcpyHostToDevice)` | `vkCmdCopyBuffer()` via staging | `buffer.upload(host_data)` | Async by default |
| **Download from GPU** | `cudaMemcpy(..., cudaMemcpyDeviceToHost)` | `vkCmdCopyBuffer()` + map | `buffer.download()` | Async by default |
| **Alloc + upload** | `cudaMalloc()` + `cudaMemcpy()` | `vkCreateBuffer()` + copy | `ctx.alloc_upload(data)` | One-shot convenience |
| **Zero-copy (pinned)** | `cudaMallocHost()` | `VK_MEMORY_PROPERTY_HOST_VISIBLE_BIT` | `ctx.alloc_pinned[T](count)` | For streaming |
| **Mapped memory** | `cudaHostAlloc()` | `vkMapMemory()` | `buffer.map()` context manager | Direct CPU access |
| **Free** | `cudaFree()` | `vkDestroyBuffer()` + `vkFreeMemory()` | `buffer.free()` or auto (RAII) | Auto-freed on drop |

**Implementation:**
```simple
# Unified buffer operations
let buf: gpu.Buffer[f32] = ctx.alloc(1024)  # Allocate 1024 floats
let host_data: [f32; 1024] = [...]
buf.upload(host_data)  # Async transfer

# Or combined
let buf = ctx.alloc_upload(host_data)  # Allocate + upload in one call

# Download results
let result = buf.download()  # Returns [f32; 1024]

# Mapped memory (zero-copy)
let pinned = ctx.alloc_pinned[f32](1024)
with pinned.map() as ptr:
    ptr[0] = 42.0  # Direct write from CPU
```

### 3. Compute Kernels

| Operation | CUDA | Vulkan | Simple Unified Interface | Notes |
|-----------|------|--------|--------------------------|-------|
| **Define kernel** | `__global__ void kernel(...)` | Compute shader in SPIR-V | `#[gpu] fn kernel(...)` or `@simd fn kernel(...)` | Simple syntax compiles to both |
| **Launch kernel** | `kernel<<<grid, block>>>(...)` | `vkCmdDispatch()` | `ctx.launch(kernel, global_size, local_size, args)` | Unified launch API |
| **Thread ID** | `threadIdx.x + blockIdx.x * blockDim.x` | `gl_GlobalInvocationID.x` | `gpu.global_id()` or `this.index()` | Abstracted intrinsics |
| **Shared memory** | `__shared__ float data[256]` | `shared` variable in shader | `shared let data: [f32; 256]` | Local workgroup memory |
| **Synchronization** | `__syncthreads()` | `barrier()` | `gpu.barrier()` | Workgroup barrier |
| **Atomics** | `atomicAdd()`, `atomicCAS()` | `atomicAdd()`, `atomicCompSwap()` | `gpu.atomic_add()`, `gpu.atomic_cas()` | Same semantics |
| **Compilation** | NVCC/NVRTC → PTX/SASS | glslangValidator → SPIR-V | JIT or AOT to backend | Transparent compilation |

**Implementation:**
```simple
# Unified kernel definition - compiles to both CUDA PTX and Vulkan SPIR-V
#[gpu]
fn vector_add(a: &[f32], b: &[f32], out: &mut [f32]):
    let idx = gpu.global_id()
    if idx < out.len():
        out[idx] = a[idx] + b[idx]

# Alternative @simd style (with automatic bounds checking)
@simd
fn vector_add_simd(a: f32[], b: f32[], out: f32[]):
    let i = this.index()  # Global linear index
    out[i] = a[i] + b[i]  # Bounds-checked by default

# Unified launch - same code for CUDA and Vulkan
ctx.launch(
    kernel: vector_add,
    global_size: [1024],
    local_size: [256],
    args: [a_buf, b_buf, out_buf]
)
```

### 4. Graphics Pipeline (Vulkan Only, CUDA: N/A)

| Operation | CUDA | Vulkan | Simple Unified Interface | Notes |
|-----------|------|--------|--------------------------|-------|
| **Window creation** | N/A (no graphics) | `glfwCreateWindow()` + `vkCreateSurface()` | `Window.new(title, width, height)` | Graphics-only |
| **Swapchain** | N/A | `vkCreateSwapchainKHR()` | Auto-managed by `Window` | Hidden from user |
| **Render pass** | N/A | `vkCreateRenderPass()` | Auto-created by `Pipeline` | Hidden from user |
| **Vertex shader** | N/A | GLSL/SPIR-V vertex shader | `#[vertex] fn vertex_main(...)` | Compiles to SPIR-V |
| **Fragment shader** | N/A | GLSL/SPIR-V fragment shader | `#[fragment] fn fragment_main(...)` | Compiles to SPIR-V |
| **Pipeline creation** | N/A | `vkCreateGraphicsPipelines()` | `Pipeline.new(vertex, fragment)` | Smart defaults |
| **Vertex buffers** | N/A | `vkCreateBuffer()` (vertex) | `ctx.create_vertex_buffer(vertices)` | Graphics-specific |
| **Draw call** | N/A | `vkCmdDraw()` | `frame.draw(vertex_buffer, count)` | Render loop API |
| **Present** | N/A | `vkQueuePresentKHR()` | Auto on `frame` drop | Hidden from user |

**Implementation:**
```simple
# Graphics API - Vulkan only (CUDA not supported, falls back to software)
use graphics.vulkan  # Or graphics.opengl, graphics.metal

let window = Window.new(title: "My App", width: 1920, height: 1080)

#[vertex]
fn vertex_main(position: vec3[f32], color: vec3[f32]) -> VertexOutput:
    var output: VertexOutput
    output.position = vec4[position.x, position.y, position.z, 1.0]
    output.color = color
    return output

#[fragment]
fn fragment_main(color: vec3[f32]) -> vec4[f32]:
    return vec4[color.x, color.y, color.z, 1.0]

let pipeline = Pipeline.new(vertex: vertex_main, fragment: fragment_main)

struct Vertex:
    position: vec3[f32]
    color: vec3[f32]

let vertices: [Vertex; 3] = [...]
let vertex_buffer = ctx.create_vertex_buffer(vertices)

# Render loop (Vulkan only)
while with window.frame() as frame:
    frame.clear([0.0, 0.0, 0.0, 1.0])
    frame.bind(pipeline)
    frame.draw(vertex_buffer, vertex_count: 3)
```

### 5. Texture/Sampler Operations

| Operation | CUDA | Vulkan | Simple Unified Interface | Notes |
|-----------|------|--------|--------------------------|-------|
| **Create texture** | `cudaCreateTextureObject()` | `vkCreateImage()` + `vkCreateImageView()` | `ctx.create_texture(width, height, format)` | Compute + graphics |
| **Upload texture** | `cudaMemcpy2D()` | `vkCmdCopyBufferToImage()` | `texture.upload(data)` | 2D/3D data |
| **Sample in kernel** | `tex2D(tex, u, v)` | `texture(sampler2D, uv)` | `texture.sample(u, v)` | Normalized coords |
| **Mipmap generation** | N/A (manual) | `vkCmdBlitImage()` | `texture.generate_mipmaps()` | Graphics feature |
| **Render to texture** | N/A (framebuffer via OpenGL interop) | `vkCreateFramebuffer()` | `ctx.create_render_target(width, height)` | Graphics feature |
| **Load from file** | `stb_image` + upload | `stb_image` + upload | `ctx.load_texture("path.png")` | Convenience |

**Implementation:**
```simple
# Texture operations - work on both CUDA and Vulkan (compute)
let tex = ctx.create_texture(
    width: 1024,
    height: 1024,
    format: :rgba8
)

let image_data: [u8; 1024*1024*4] = [...]
tex.upload(image_data)

# Sample in kernel (both CUDA and Vulkan)
#[gpu]
fn process_texture(tex: &Texture2D, out: &mut [f32]):
    let idx = gpu.global_id()
    let u = (idx % 1024) as f32 / 1024.0
    let v = (idx / 1024) as f32 / 1024.0
    let color = tex.sample(u, v)  # Works on both backends
    out[idx] = color.r

# Graphics-specific: render to texture (Vulkan only)
let render_target = ctx.create_render_target(1024, 1024)
with render_target.frame() as frame:
    frame.draw(...)  # Renders to texture instead of screen
```

### 6. Synchronization

| Operation | CUDA | Vulkan | Simple Unified Interface | Notes |
|-----------|------|--------|--------------------------|-------|
| **Wait for kernel** | `cudaDeviceSynchronize()` | `vkQueueWaitIdle()` | `ctx.sync()` | Block until all work done |
| **Event** | `cudaEventCreate()` + `cudaEventRecord()` | `vkCreateEvent()` | `ctx.create_event()` | GPU-side synchronization |
| **Wait for event** | `cudaEventSynchronize()` | `vkCmdWaitEvents()` | `event.wait()` | Wait on CPU |
| **Async operations** | CUDA streams | Vulkan command buffers | `ctx.launch(...).then(...)` | Future-based |
| **Fence** | Similar to events | `vkCreateFence()` | `ctx.create_fence()` | CPU-GPU sync |
| **Semaphore** | N/A (events) | `vkCreateSemaphore()` | `ctx.create_semaphore()` | GPU-GPU sync |

**Implementation:**
```simple
# Synchronization - unified
ctx.launch(kernel: k1, ...)
ctx.launch(kernel: k2, ...)
ctx.sync()  # Wait for both kernels

# Async with futures
let result = ctx.launch(kernel, ...).then(|_| {
    out_buf.download()
})
await result

# Events for fine-grained control
let event = ctx.create_event()
ctx.launch(kernel1, ...).record(event)
ctx.launch(kernel2, ...).wait(event)  # kernel2 waits for kernel1
```

### 7. Tensor/Dataset Operations (ML Integration)

| Operation | CUDA (via cuBLAS/cuDNN) | Vulkan | Simple Unified Interface | Notes |
|-----------|-------------------------|--------|--------------------------|-------|
| **Tensor creation** | `torch.tensor(...).cuda()` | Custom tensor API | `Tensor.new(shape, dtype, device)` | N-dimensional arrays |
| **Matrix multiply** | `cublasSgemm()` | Custom shader or VkFFT | `tensor_a @ tensor_b` | Operator overload |
| **Convolution** | `cudnnConvolutionForward()` | Custom compute shader | `conv2d(input, kernel)` | ML primitive |
| **Batch operations** | Batched cuBLAS | Multiple dispatches | `Tensor.batch_op(...)` | Efficient batching |
| **Data loading** | `torch.utils.data.DataLoader` | Custom streaming | `DataLoader.new(dataset, batch_size)` | Async prefetch |
| **Zero-copy PyTorch** | `torch.as_tensor(cuda_ptr)` | `torch.utils.dlpack` | `tensor.to_pytorch()` | DLPack interop |
| **Autograd integration** | PyTorch autograd | Manual or JAX | `Tensor.requires_grad = true` | Gradient tracking |

**Implementation:**
```simple
# Tensor API - works with CUDA and Vulkan compute
use ml.tensor

# Create tensor on GPU
let a = Tensor.new(
    shape: [1024, 1024],
    dtype: :f32,
    device: ctx.device
)

# Fill with data
a.fill(1.0)

# Matrix multiplication (uses cuBLAS on CUDA, custom kernel on Vulkan)
let b = Tensor.randn([1024, 512], device: ctx.device)
let c = a @ b  # Unified operator

# Convolution (uses cuDNN on CUDA, custom shader on Vulkan)
let input = Tensor.new(shape: [1, 3, 224, 224], device: ctx.device)
let kernel = Tensor.new(shape: [64, 3, 3, 3], device: ctx.device)
let output = conv2d(input, kernel, stride: 1, padding: 1)

# PyTorch interop (zero-copy)
let torch_tensor = a.to_pytorch()  # Returns torch.Tensor on same device
let simple_tensor = Tensor.from_pytorch(torch_tensor)  # No copy

# Data loading with async prefetch
let dataset = ImageDataset.new("path/to/imagenet/")
let loader = DataLoader.new(
    dataset: dataset,
    batch_size: 32,
    shuffle: true,
    num_workers: 4,  # Parallel loading
    prefetch: 2      # GPU buffer count
)

for batch in loader:
    let images = batch.images  # Already on GPU
    let labels = batch.labels
    # Training code...
```

### 8. Interoperability

| Operation | CUDA | Vulkan | Simple Unified Interface | Notes |
|-----------|------|--------|--------------------------|-------|
| **OpenGL interop** | `cudaGraphicsGLRegisterBuffer()` | `VK_KHR_external_memory_fd` | `ctx.import_gl_buffer(gl_id)` | Share buffers |
| **DirectX interop** | `cudaGraphicsD3D11RegisterResource()` | `VK_KHR_external_memory_win32` | `ctx.import_dx_buffer(dx_ptr)` | Windows only |
| **CPU fallback** | Run kernel on CPU (slow) | Software rasterizer | `ctx.set_backend(:cpu)` | Automatic fallback |
| **Multi-backend** | CUDA + Vulkan (two contexts) | Vulkan + OpenCL | `ctx1 = gpu.Context.new(backend: :cuda)` | Explicit selection |
| **DLPack** | `torch.utils.dlpack.to_dlpack()` | Custom export | `tensor.to_dlpack()` | Zero-copy exchange |
| **ONNX Runtime** | CUDA execution provider | Custom EP | `onnx.run(model, inputs, device: ctx)` | ML model inference |

**Implementation:**
```simple
# Backend selection
let cuda_ctx = gpu.Context.new(backend: :cuda)  # Force CUDA
let vulkan_ctx = gpu.Context.new(backend: :vulkan)  # Force Vulkan
let auto_ctx = gpu.Context.new()  # Auto-detect (prefers CUDA on NVIDIA)

# CPU fallback
let cpu_ctx = gpu.Context.new(backend: :cpu)  # Software fallback
cpu_ctx.launch(kernel, ...)  # Runs on CPU (slow but always works)

# OpenGL interop (for rendering)
let gl_buffer_id = gl.create_buffer(...)
let shared_buf = vulkan_ctx.import_gl_buffer(gl_buffer_id)
# Now both OpenGL and Vulkan can access the same memory

# DLPack for PyTorch/JAX/TensorFlow interop
import torch
let simple_tensor = Tensor.new([1024], device: ctx.device)
let dlpack_capsule = simple_tensor.to_dlpack()
let torch_tensor = torch.from_dlpack(dlpack_capsule)  # Zero-copy
```

## Implementation Strategy

### Phase 1: Unified Compute API (Current - Extend Vulkan)
**Goal:** Make compute operations work identically on CUDA and Vulkan

**Tasks:**
1. ✅ Complete Vulkan device/swapchain/pipeline (Phase 1 done)
2. 📋 Add compute pipeline to Vulkan backend
3. 📋 Unify buffer allocation API (ctx.alloc, upload, download)
4. 📋 Unify kernel launch API (ctx.launch)
5. 📋 Add backend selection (auto-detect, force CUDA/Vulkan/CPU)
6. 📋 Test same kernel code on CUDA and Vulkan
7. 📋 Benchmark performance parity

**Files to Modify:**
- `simple/std_lib/src/gpu/host/async_nogc_mut/` - Unified buffer API
- `simple/std_lib/src/gpu/kernel/` - Unified kernel intrinsics
- `src/compiler/src/codegen/spirv/` - SPIR-V compute backend
- `src/compiler/src/codegen/cuda/` - CUDA PTX backend (if exists)

**Estimated:** 5-7 days

### Phase 2: Graphics Extensions (Vulkan Graphics)
**Goal:** Complete graphics pipeline for Vulkan

**Tasks:**
1. ✅ Vertex/fragment shader compilation (Phase 1 done)
2. 📋 Vertex buffer upload and attribute binding
3. 📋 Index buffer support
4. 📋 Texture loading and sampling
5. 📋 Descriptor sets and uniforms
6. 📋 Render loop with while-with
7. 📋 Multiple render passes
8. 📋 Depth/stencil buffers

**Files to Create/Modify:**
- `simple/std_lib/src/graphics/vulkan/` - Graphics-specific API
- Extend `vulkan_pipeline.spl` with descriptor sets
- Add `vulkan_textures.spl` for texture management
- Add `vulkan_render_loop.spl` for frame management

**Estimated:** 7-10 days

### Phase 3: Tensor Operations (ML Integration)
**Goal:** Add tensor library compatible with PyTorch/JAX

**Tasks:**
1. 📋 Tensor type with shape, dtype, device
2. 📋 Matrix operations (matmul, transpose, reshape)
3. 📋 Convolution operations (conv2d, conv3d)
4. 📋 Reduction operations (sum, mean, max)
5. 📋 DLPack interop (to_dlpack, from_dlpack)
6. 📋 PyTorch zero-copy bridge
7. 📋 DataLoader with async prefetch
8. 📋 Autograd (optional, or use JAX)

**Files to Create:**
- `simple/std_lib/src/ml/tensor/` - Tensor library
- `simple/std_lib/src/ml/nn/` - Neural network layers
- `simple/std_lib/src/ml/data/` - Data loading
- `src/runtime/src/ml/` - DLPack implementation

**Estimated:** 10-14 days

### Phase 4: Optimization and Testing
**Goal:** Ensure performance and correctness

**Tasks:**
1. 📋 Benchmark CUDA vs Vulkan compute
2. 📋 Optimize memory transfers
3. 📋 Add async pipeline (overlap compute + transfer)
4. 📋 Test on multiple GPUs (NVIDIA, AMD, Intel)
5. 📋 Test graphics on mobile (Android Vulkan)
6. 📋 Profile and optimize hot paths
7. 📋 Add comprehensive tests

**Estimated:** 5-7 days

## Success Criteria

### Compute Portability
- [ ] Same kernel code compiles to both CUDA PTX and Vulkan SPIR-V
- [ ] Performance within 10% between CUDA and Vulkan on same hardware
- [ ] Buffer operations (alloc, upload, download) work identically
- [ ] Kernel launch API is backend-agnostic

### Graphics Capability
- [ ] Vulkan graphics pipeline renders triangle
- [ ] Texture loading and sampling works
- [ ] Descriptor sets and uniforms work
- [ ] Render loop with while-with is ergonomic
- [ ] Can render 1000+ objects at 60 FPS

### ML Integration
- [ ] Tensor operations match PyTorch semantics
- [ ] DLPack interop is zero-copy
- [ ] DataLoader prefetches asynchronously
- [ ] Can train simple CNN (ResNet-18)
- [ ] Performance within 20% of native PyTorch

### Cross-Backend Testing
- [ ] All compute tests pass on CUDA and Vulkan
- [ ] Graphics tests pass on Vulkan
- [ ] CPU fallback works for all compute kernels
- [ ] Backend auto-detection selects best available

## Example: Unified Code

```simple
# This code works on CUDA, Vulkan, and CPU backends
use gpu

# Auto-detect best backend
let ctx = gpu.Context.default()  # CUDA on NVIDIA, Vulkan on AMD/Intel/Apple

# Define kernel once
#[gpu]
fn vector_add(a: &[f32], b: &[f32], out: &mut [f32]):
    let idx = gpu.global_id()
    if idx < out.len():
        out[idx] = a[idx] + b[idx]

# Allocate and launch - same API for all backends
let a = ctx.alloc_upload([1.0, 2.0, 3.0, 4.0])
let b = ctx.alloc_upload([5.0, 6.0, 7.0, 8.0])
let out = ctx.alloc[f32](4)

ctx.launch(
    kernel: vector_add,
    global_size: [4],
    local_size: [1],
    args: [a, b, out]
)

ctx.sync()
let result = out.download()  # [6.0, 8.0, 10.0, 12.0]
print("Result: {result}")
```

## Related Documents

- [GPU SIMD Specification](../spec/gpu_simd.md) - Language-level GPU features
- [Vulkan Phase 1 Progress](../report/VULKAN_PHASE_1_PROGRESS.md) - Graphics pipeline status
- [Vulkan Backend Implementation](../report/VULKAN_BACKEND_IMPLEMENTATION_2025-12-26.md) - SPIR-V compute backend
- [PyTorch Integration Plan](PYTORCH_INTEGRATION_PLAN.md) - ML framework integration

---

**Next Step:** Implement Phase 1 - Unified Compute API with Vulkan compute pipeline
