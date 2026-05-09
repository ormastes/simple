# GPU API Reference

Complete API reference for GPU compute support in Simple.

## Table of Contents

1. [Module Overview](#module-overview)
2. [std.gpu Module](#stdgpu-module)
3. [std.gpu.device Module](#stdgpudevice-module)
4. [std.gpu.memory Module](#stdgpumemory-module)
5. [std.gpu.kernels Module](#stdgpukernels-module)
6. [std.gpu.sync Module](#stdgpusync-module)
7. [CUDA FFI (io.cuda_ffi)](#cuda-ffi-iocuda_ffi)
8. [Vulkan FFI (io.vulkan_ffi)](#vulkan-ffi-iovulkan_ffi)
9. [Type Mappers](#type-mappers)
10. [Backend API](#backend-api)

---

## Module Overview

```
std.gpu                    # Main module (re-exports from submodules)
├── device                 # Device detection and management
├── memory                 # Memory allocation and transfer
├── kernels                # Kernel compilation and execution
└── sync                   # Synchronization primitives

io.cuda_ffi                # Low-level CUDA FFI bindings
io.vulkan_ffi              # Low-level Vulkan FFI bindings

compiler.backend
├── cuda_type_mapper       # CUDA type mapping
├── vulkan_type_mapper     # Vulkan/SPIR-V type mapping
├── cuda_backend           # CUDA code generation
├── vulkan_backend         # Vulkan code generation
├── cuda.ptx_builder       # PTX assembly builder
└── vulkan.spirv_builder   # SPIR-V assembly builder
```

---

## std.gpu Module

**Import:** `use std.gpu.*`

### Types

#### GpuBackend
```simple
enum GpuBackend:
    Cuda       # NVIDIA CUDA backend
    Vulkan     # Vulkan compute backend
    None       # No GPU available
```

#### Gpu
```simple
struct Gpu:
    backend: GpuBackend
    device_id: i64
    is_initialized: bool
```

**Methods:**
| Method | Return Type | Description |
|--------|-------------|-------------|
| `is_valid()` | `bool` | Check if device is usable |
| `name()` | `text` | Get device name |
| `total_memory()` | `i64` | Get total memory in bytes |
| `backend_name()` | `text` | Get backend name ("CUDA", "Vulkan", "None") |
| `sync()` | `bool` | Wait for all operations to complete |

### Functions

#### Device Selection
| Function | Return Type | Description |
|----------|-------------|-------------|
| `gpu_default()` | `Gpu` | Get default GPU (auto-selects best) |
| `gpu_cuda(id: i64)` | `Gpu` | Get CUDA device by ID |
| `gpu_vulkan(id: i64)` | `Gpu` | Get Vulkan device by ID |
| `gpu_init()` | `Gpu` | Initialize GPU or panic if unavailable |

#### Device Enumeration
| Function | Return Type | Description |
|----------|-------------|-------------|
| `gpu_available()` | `bool` | Check if any GPU is available |
| `gpu_count()` | `i64` | Get total GPU count across all backends |
| `list_all_gpus()` | `[GpuDeviceEntry]` | List all available GPUs |
| `detect_backends()` | `[GpuBackend]` | Detect available backends |
| `preferred_backend()` | `GpuBackend` | Get preferred backend |

#### Utilities
| Function | Return Type | Description |
|----------|-------------|-------------|
| `gpu_info()` | `text` | Get formatted GPU info string |
| `gpu_test()` | `bool` | Run GPU smoke test |
| `gpu_is_ready()` | `bool` | Check if GPU is available and working |

---

## std.gpu.device Module

**Import:** `use std.gpu.device.*`

### GpuDeviceEntry
```simple
struct GpuDeviceEntry:
    backend: GpuBackend
    device_id: i64
    name: text
    memory: i64
```

---

## std.gpu.memory Module

**Import:** `use std.gpu.memory.*`

### Types

#### GpuBuffer
```simple
struct GpuBuffer:
    backend: GpuBackend
    cuda_ptr: CudaPtr?
    vulkan_buf: VulkanBuffer?
    size: i64
    is_valid: bool
```

**Properties:**
| Property | Type | Description |
|----------|------|-------------|
| `is_valid` | `bool` | Whether buffer is valid |
| `size` | `i64` | Buffer size in bytes |

**Methods:**
| Method | Return Type | Description |
|--------|-------------|-------------|
| `valid()` | `bool` | Check validity |
| `len()` | `i64` | Get size in bytes |
| `raw_ptr()` | `i64` | Get CUDA pointer (0 for Vulkan) |
| `raw_handle()` | `i64` | Get Vulkan handle (0 for CUDA) |

#### GpuArray\<T\>
```simple
struct GpuArray<T>:
    buffer: GpuBuffer
    len: i64
    element_size: i64
```

**Methods:**
| Method | Return Type | Description |
|--------|-------------|-------------|
| `valid()` | `bool` | Check validity |
| `count()` | `i64` | Get element count |
| `size_bytes()` | `i64` | Get size in bytes |
| `copy_from_host(data: [u8])` | `bool` | Copy from host |
| `copy_to_host(data: [u8])` | `bool` | Copy to host |

#### GpuMemoryPool
```simple
struct GpuMemoryPool:
    gpu: Gpu
    chunk_size: i64
    chunks: [GpuBuffer]
    free_offsets: [i64]
```

**Methods:**
| Method | Return Type | Description |
|--------|-------------|-------------|
| `alloc(size: i64)` | `GpuBuffer` | Allocate from pool |
| `clear()` | `bool` | Release all memory |

### Functions

#### Allocation
| Function | Return Type | Description |
|----------|-------------|-------------|
| `gpu_alloc(gpu, size)` | `GpuBuffer` | Allocate raw bytes |
| `gpu_free(buffer)` | `bool` | Free buffer |
| `gpu_alloc_f32(gpu, count)` | `GpuArray<f32>` | Allocate f32 array |
| `gpu_alloc_f64(gpu, count)` | `GpuArray<f64>` | Allocate f64 array |
| `gpu_alloc_i32(gpu, count)` | `GpuArray<i32>` | Allocate i32 array |
| `gpu_alloc_i64(gpu, count)` | `GpuArray<i64>` | Allocate i64 array |
| `gpu_array_alloc<T>(gpu, count, elem_size)` | `GpuArray<T>` | Allocate typed array |
| `gpu_array_free<T>(arr)` | `bool` | Free typed array |
| `gpu_array_from<T>(gpu, data, count, elem_size)` | `GpuArray<T>` | Allocate and initialize |
| `gpu_pool_create(gpu, chunk_size)` | `GpuMemoryPool` | Create memory pool |

#### Data Transfer
| Function | Return Type | Description |
|----------|-------------|-------------|
| `gpu_copy_to(buffer, data)` | `bool` | Copy host to device |
| `gpu_copy_from(data, buffer)` | `bool` | Copy device to host |
| `gpu_copy_buffer(dst, src, size)` | `bool` | Copy device to device |
| `gpu_memset(buffer, value)` | `bool` | Fill buffer (CUDA only) |

---

## std.gpu.kernels Module

**Import:** `use std.gpu.kernels.*`

### Types

#### GpuKernel
```simple
struct GpuKernel:
    name: text
    cuda_module: CudaModule?
    cuda_kernel: CudaKernel?
    vulkan_pipeline: VulkanPipeline?
    vulkan_shader: VulkanShader?
    backend: GpuBackend
    is_valid: bool
```

#### KernelLaunch
```simple
struct KernelLaunch:
    grid: (i64, i64, i64)
    block: (i64, i64, i64)
    shared_mem: i64
```

### Functions

#### Kernel Compilation
| Function | Return Type | Description |
|----------|-------------|-------------|
| `kernel_compile_cuda(ptx, entry)` | `GpuKernel` | Compile PTX to kernel |
| `kernel_compile_vulkan(glsl, entry)` | `GpuKernel` | Compile GLSL to kernel |
| `kernel_destroy(kernel)` | `bool` | Destroy kernel |

#### Launch Configuration
| Function | Return Type | Description |
|----------|-------------|-------------|
| `launch_1d(total, block_size)` | `KernelLaunch` | Create 1D launch config |
| `launch_2d(w, h, bx, by)` | `KernelLaunch` | Create 2D launch config |

#### Kernel Execution
| Function | Return Type | Description |
|----------|-------------|-------------|
| `kernel_run(kernel, launch, buffers)` | `bool` | Execute kernel |
| `gpu_vector_add(gpu, a, b, c, n)` | `bool` | Built-in vector add |
| `gpu_scalar_mul(gpu, arr, scalar, n)` | `bool` | Built-in scalar multiply |

### Built-in PTX/GLSL

| Constant | Description |
|----------|-------------|
| `VECTOR_ADD_PTX` | PTX source for vector addition |
| `SCALAR_MUL_PTX` | PTX source for scalar multiplication |
| `VECTOR_ADD_GLSL` | GLSL source for vector addition |
| `SCALAR_MUL_GLSL` | GLSL source for scalar multiplication |

---

## std.gpu.sync Module

**Import:** `use std.gpu.sync.*`

### Types

#### GpuStream
```simple
struct GpuStream:
    backend: GpuBackend
    cuda_stream: CudaStream?
    is_valid: bool
```

**Methods:**
| Method | Return Type | Description |
|--------|-------------|-------------|
| `valid()` | `bool` | Check validity |
| `sync()` | `bool` | Synchronize stream |
| `destroy()` | `bool` | Destroy stream |

#### GpuEvent
```simple
struct GpuEvent:
    backend: GpuBackend
    vulkan_fence: i64?
    is_valid: bool
```

**Methods:**
| Method | Return Type | Description |
|--------|-------------|-------------|
| `valid()` | `bool` | Check validity |
| `wait(timeout_ns)` | `bool` | Wait with timeout |
| `wait_forever()` | `bool` | Wait indefinitely |
| `reset()` | `bool` | Reset for reuse |
| `destroy()` | `bool` | Destroy event |

#### GpuMemoryScope
```simple
enum GpuMemoryScope:
    Device     # All threads on device
    Workgroup  # Threads in same workgroup
    Subgroup   # Threads in same subgroup
```

### Functions

#### Device Synchronization
| Function | Return Type | Description |
|----------|-------------|-------------|
| `gpu_sync(gpu)` | `bool` | Sync single device |
| `gpu_sync_all()` | `bool` | Sync all devices |

#### Stream Management
| Function | Return Type | Description |
|----------|-------------|-------------|
| `gpu_stream_create(gpu)` | `GpuStream` | Create stream |
| `gpu_stream_destroy(stream)` | `bool` | Destroy stream |
| `gpu_stream_sync(stream)` | `bool` | Synchronize stream |

#### Event Management
| Function | Return Type | Description |
|----------|-------------|-------------|
| `gpu_event_create(gpu)` | `GpuEvent` | Create event/fence |
| `gpu_event_destroy(event)` | `bool` | Destroy event |
| `gpu_event_wait(event, timeout)` | `bool` | Wait for event |
| `gpu_event_reset(event)` | `bool` | Reset event |

#### Scoped Operations
| Function | Return Type | Description |
|----------|-------------|-------------|
| `with_gpu_sync<T>(gpu, fn)` | `T` | Execute with sync |
| `with_device<T>(gpu, fn)` | `T` | Execute on device |

---

## CUDA FFI (io.cuda_ffi)

**Import:** `use io.cuda_ffi.*`

### Types

#### CudaDeviceInfo
```simple
struct CudaDeviceInfo:
    id: i64
    name: text
    total_memory: i64
    compute_capability: (i64, i64)
```

#### CudaPtr
```simple
struct CudaPtr:
    ptr: i64
    size: i64
    is_valid: bool
```

#### CudaModule
```simple
struct CudaModule:
    handle: i64
    is_valid: bool
```

#### CudaKernel
```simple
struct CudaKernel:
    handle: i64
    module: CudaModule
    name: text
    is_valid: bool
```

#### CudaLaunchConfig
```simple
struct CudaLaunchConfig:
    grid: (i64, i64, i64)
    block: (i64, i64, i64)
    shared_mem: i64
```

#### CudaStream
```simple
struct CudaStream:
    handle: i64
    is_valid: bool
```

### Functions

#### Device Management
| Function | Signature | Description |
|----------|-----------|-------------|
| `cuda_available` | `() -> bool` | Check CUDA availability |
| `cuda_device_count` | `() -> i64` | Get device count |
| `cuda_set_device` | `(id: i64) -> bool` | Set current device |
| `cuda_get_device` | `() -> i64` | Get current device |
| `cuda_device_info` | `(id: i64) -> CudaDeviceInfo` | Get device info |

#### Memory Management
| Function | Signature | Description |
|----------|-----------|-------------|
| `cuda_alloc` | `(size: i64) -> CudaPtr` | Allocate device memory |
| `cuda_free` | `(mem: CudaPtr) -> bool` | Free device memory |
| `cuda_copy_to_device` | `(dst: CudaPtr, src: [u8]) -> bool` | Host to device copy |
| `cuda_copy_from_device` | `(dst: [u8], src: CudaPtr) -> bool` | Device to host copy |
| `cuda_copy_device_to_device` | `(dst, src, size) -> bool` | Device to device copy |
| `cuda_memset` | `(mem: CudaPtr, value: i64) -> bool` | Fill memory |

#### Kernel Operations
| Function | Signature | Description |
|----------|-----------|-------------|
| `cuda_compile` | `(ptx: text) -> CudaModule` | Compile PTX |
| `cuda_unload` | `(module: CudaModule) -> bool` | Unload module |
| `cuda_get_kernel` | `(module, name) -> CudaKernel` | Get kernel function |
| `cuda_launch` | `(kernel, config, args) -> bool` | Launch kernel |
| `cuda_launch_config` | `(grid, block) -> CudaLaunchConfig` | Create config |
| `cuda_launch_config_1d` | `(grid, block) -> CudaLaunchConfig` | Create 1D config |
| `cuda_run_1d` | `(kernel, total, block, args) -> bool` | Simple 1D launch |

#### Synchronization
| Function | Signature | Description |
|----------|-----------|-------------|
| `cuda_sync` | `() -> bool` | Synchronize device |
| `cuda_stream_create` | `() -> CudaStream` | Create stream |
| `cuda_stream_destroy` | `(stream) -> bool` | Destroy stream |
| `cuda_stream_sync` | `(stream) -> bool` | Sync stream |

#### Error Handling
| Function | Signature | Description |
|----------|-----------|-------------|
| `cuda_last_error` | `() -> text` | Get and clear last error |
| `cuda_peek_error` | `() -> text` | Peek at last error |

---

## Vulkan FFI (io.vulkan_ffi)

**Import:** `use io.vulkan_ffi.*`

### Types

#### VulkanDeviceType
```simple
enum VulkanDeviceType:
    Discrete     # Dedicated GPU
    Integrated   # Integrated GPU
    Virtual      # Virtual GPU
    Cpu          # Software renderer
    Unknown
```

#### VulkanDeviceInfo
```simple
struct VulkanDeviceInfo:
    id: i64
    name: text
    device_type: VulkanDeviceType
    total_memory: i64
    api_version: (i64, i64, i64)
```

#### VulkanBufferUsage
```simple
enum VulkanBufferUsage:
    Storage        # Storage buffer
    Uniform        # Uniform buffer
    TransferSrc    # Transfer source
    TransferDst    # Transfer destination
```

#### VulkanBuffer
```simple
struct VulkanBuffer:
    handle: i64
    size: i64
    usage: VulkanBufferUsage
    is_valid: bool
```

#### VulkanShader
```simple
struct VulkanShader:
    handle: i64
    is_valid: bool
```

#### VulkanPipeline
```simple
struct VulkanPipeline:
    handle: i64
    shader: VulkanShader
    entry_point: text
    is_valid: bool
```

#### VulkanDescriptorSet
```simple
struct VulkanDescriptorSet:
    handle: i64
    pipeline: VulkanPipeline
    is_valid: bool
```

#### VulkanCommandBuffer
```simple
struct VulkanCommandBuffer:
    handle: i64
    is_valid: bool
```

#### VulkanDispatchConfig
```simple
struct VulkanDispatchConfig:
    workgroups: (i64, i64, i64)
    local_size: (i64, i64, i64)
```

### Functions

#### Instance/Device
| Function | Signature | Description |
|----------|-----------|-------------|
| `vulkan_available` | `() -> bool` | Check Vulkan availability |
| `vulkan_init` | `() -> bool` | Initialize Vulkan |
| `vulkan_shutdown` | `() -> bool` | Shutdown Vulkan |
| `vulkan_device_count` | `() -> i64` | Get device count |
| `vulkan_select_device` | `(id: i64) -> bool` | Select device |
| `vulkan_get_device` | `() -> i64` | Get current device |
| `vulkan_device_info` | `(id: i64) -> VulkanDeviceInfo` | Get device info |

#### Buffer Operations
| Function | Signature | Description |
|----------|-----------|-------------|
| `vulkan_alloc_buffer` | `(size, usage) -> VulkanBuffer` | Allocate buffer |
| `vulkan_alloc_storage` | `(size: i64) -> VulkanBuffer` | Allocate storage buffer |
| `vulkan_free_buffer` | `(buffer) -> bool` | Free buffer |
| `vulkan_copy_to` | `(buffer, data) -> bool` | Copy to buffer |
| `vulkan_copy_from` | `(data, buffer) -> bool` | Copy from buffer |
| `vulkan_copy_buffer` | `(dst, src, size) -> bool` | Copy between buffers |

#### Shader Operations
| Function | Signature | Description |
|----------|-----------|-------------|
| `vulkan_compile_spirv` | `(bytes: [u8]) -> VulkanShader` | Compile SPIR-V |
| `vulkan_compile_glsl` | `(source: text) -> VulkanShader` | Compile GLSL |
| `vulkan_destroy_shader` | `(shader) -> bool` | Destroy shader |

#### Pipeline Operations
| Function | Signature | Description |
|----------|-----------|-------------|
| `vulkan_create_pipeline` | `(shader, entry) -> VulkanPipeline` | Create pipeline |
| `vulkan_create_pipeline_with_push` | `(shader, entry, size) -> VulkanPipeline` | With push constants |
| `vulkan_destroy_pipeline` | `(pipeline) -> bool` | Destroy pipeline |

#### Descriptor Sets
| Function | Signature | Description |
|----------|-----------|-------------|
| `vulkan_create_descriptors` | `(pipeline) -> VulkanDescriptorSet` | Create descriptor set |
| `vulkan_bind_buffer` | `(descriptors, binding, buffer) -> bool` | Bind buffer |
| `vulkan_destroy_descriptors` | `(descriptors) -> bool` | Destroy descriptor set |

#### Command Execution
| Function | Signature | Description |
|----------|-----------|-------------|
| `vulkan_begin_compute` | `() -> VulkanCommandBuffer` | Begin recording |
| `vulkan_cmd_bind_pipeline` | `(cmd, pipeline) -> bool` | Bind pipeline |
| `vulkan_cmd_bind_descriptors` | `(cmd, descriptors) -> bool` | Bind descriptors |
| `vulkan_cmd_push_constants` | `(cmd, pipeline, data) -> bool` | Set push constants |
| `vulkan_cmd_dispatch` | `(cmd, x, y, z) -> bool` | Dispatch compute |
| `vulkan_end_compute` | `(cmd) -> bool` | End recording |
| `vulkan_submit_and_wait` | `(cmd) -> bool` | Submit and wait |

#### Synchronization
| Function | Signature | Description |
|----------|-----------|-------------|
| `vulkan_wait_idle` | `() -> bool` | Wait for device idle |

#### Error Handling
| Function | Signature | Description |
|----------|-----------|-------------|
| `vulkan_last_error` | `() -> text` | Get last error |

#### High-Level API
| Function | Signature | Description |
|----------|-----------|-------------|
| `vulkan_dispatch_1d` | `(total, local) -> VulkanDispatchConfig` | Create 1D dispatch |
| `vulkan_compute` | `(glsl, entry, buffers, dispatch) -> bool` | Run compute shader |

---

## Type Mappers

### CudaTypeMapper

**Import:** `use compiler.backend.cuda_type_mapper.*`

Maps Simple types to CUDA/PTX types.

| Simple Type | CUDA Type |
|-------------|-----------|
| `i64` | `long long` |
| `i32` | `int` |
| `i16` | `short` |
| `i8` | `char` |
| `u64` | `unsigned long long` |
| `u32` | `unsigned int` |
| `f64` | `double` |
| `f32` | `float` |
| `f16` | `half` |
| `bool` | `bool` |

### VulkanTypeMapper

**Import:** `use compiler.backend.vulkan_type_mapper.*`

Maps Simple types to SPIR-V types.

| Simple Type | SPIR-V Type |
|-------------|-------------|
| `i64` | `OpTypeInt 64 1` |
| `i32` | `OpTypeInt 32 1` |
| `u32` | `OpTypeInt 32 0` |
| `f64` | `OpTypeFloat 64` |
| `f32` | `OpTypeFloat 32` |
| `bool` | `OpTypeBool` |

---

## Backend API

### BackendKind

```simple
enum BackendKind:
    Cranelift   # Cranelift code generation
    Llvm        # LLVM code generation
    Wasm        # WebAssembly
    Lean        # Lean 4 verification
    Interpreter # Interpreter backend
    Cuda        # NVIDIA CUDA (PTX)
    Vulkan      # Vulkan compute (SPIR-V)
```

### CodegenTarget

```simple
enum CodegenTarget:
    X86_64
    AArch64
    Wasm32
    Wasm64
    CudaPtx(compute_cap: (i64, i64))
    VulkanSpirv(version: (i64, i64))
```

---

## See Also

- [GPU Programming Guide](../guide/apps/gpu.md) - Tutorial and examples
- [GPU Backend Design](../design/gpu_backend_design.md) - Architecture details

---

## 3D Rendering Engine (std.gpu.engine3d)

The `std.gpu.engine3d` module is a multi-backend 3D rendering engine with automatic backend selection. It sits on top of the GPU compute layer and provides a high-level facade for geometry submission, lighting, textures, shadows, post-processing, and compute.

**Module path:** `src/lib/gc_async_mut/gpu/engine3d/`

### Architecture

The engine uses a layered trait hierarchy:

```
Engine3D (facade)
    └── RenderBackend3D  (= RenderBackend3DCore + RenderBackend3DAdv)
            ├── RenderBackend3DCore   — 32 required methods
            └── RenderBackend3DAdv   — 42 optimized methods (emulatable from Core)
    └── Engine3DExtended (optional)  — 20 Chrome WebGPU extension methods
```

- **`RenderBackend3DCore`** (`backend_core.spl`) — the minimum interface every backend must implement. Covers identity, lifecycle, view, clear, submit_triangle, lighting, render state, render targets, pixel transfer, readback, and extended texture ops.
- **`RenderBackend3DAdv`** (`backend_adv.spl`) — optimized paths. Every method is emulatable via `backend_emu.spl` using only Core methods, so minimal backends get full Adv behavior for free.
- **`RenderBackend3D`** (`backend.spl`) — combined trait = Core + Adv. Full backends implement this directly.
- **`Engine3DExtended`** (`backend.spl`) — optional Chrome WebGPU parity extensions: MSAA, ray tracing, variable rate shading, mesh shaders, and bind groups.
- **`Engine3D`** (`engine.spl`) — public facade. Selects the best backend at init time and delegates all operations.

### Backends

| Backend | File | Description |
|---------|------|-------------|
| CPU (rasterizer) | `backend_cpu.spl` | Default software rasterizer, always available |
| Software | `backend_software.spl` | Pure-software fallback |
| Emulation | `backend_emu.spl` | Stateless Core→Adv emulation layer |
| CUDA | `backend_cuda.spl` | NVIDIA CUDA compute path |
| Vulkan | `backend_vulkan.spl` | Vulkan (SPIR-V) |
| ROCm | `backend_rocm.spl` | AMD ROCm |
| Metal | `backend_metal.spl` | Apple Metal |
| OpenGL | `backend_opengl.spl` | OpenGL |
| Intel | `backend_intel.spl` | Intel GPU |
| WebGPU | `backend_webgpu.spl` | Chrome WebGPU (browser + native) |
| Qualcomm | `backend_qualcomm.spl` | Qualcomm Adreno |
| Baremetal | `backend_baremetal.spl` | No-alloc baremetal target |
| VirtioGPU | `backend_virtio_gpu.spl` | VirtIO GPU (QEMU/VM) |

### Quick Start

```simple
use std.gpu.engine3d.engine.{Engine3D}
use std.gpu.engine3d.types3d.{Vertex3D, Material3DParams, LightParams3D}

var engine = Engine3D.create(800, 600)

engine.begin_frame()
engine.clear(0xFF111111)

val v0 = Vertex3D(x: 0.0, y: 0.5, z: 0.0, nx: 0.0, ny: 0.0, nz: 1.0, u: 0.5, v: 0.0, color: 0xFFFF0000)
val v1 = Vertex3D(x: -0.5, y: -0.5, z: 0.0, nx: 0.0, ny: 0.0, nz: 1.0, u: 0.0, v: 1.0, color: 0xFF00FF00)
val v2 = Vertex3D(x: 0.5, y: -0.5, z: 0.0, nx: 0.0, ny: 0.0, nz: 1.0, u: 1.0, v: 1.0, color: 0xFF0000FF)
val mat = Material3DParams(albedo: 0xFFFFFFFF, roughness: 0.5, metallic: 0.0, texture_id: -1, shader_type: 0)
val identity = [1.0f32, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0, 1.0]
engine.submit_triangle(v0, v1, v2, mat, identity)

engine.end_frame()
engine.present()

val pixels = engine.read_pixels()
engine.shutdown()
```

### Core Type Reference

#### Vertex and Geometry Types

| Type | Module | Fields |
|------|--------|--------|
| `Vertex3D` | `types3d` | `x, y, z: f32` position; `nx, ny, nz: f32` normal; `u, v: f32` UV; `color: u32` ARGB |
| `Material3DParams` | `types3d` | `albedo: u32`; `roughness, metallic: f32`; `texture_id: i32`; `shader_type: i32` |
| `LightParams3D` | `types3d` | `x, y, z: f32` position; `color: u32`; `intensity: f32`; `light_type: i32` |

#### Texture Types

| Type | Module | Key Fields |
|------|--------|-----------|
| `TextureDescriptor3D` | `texture3d` | `dimension, format, width, height, depth_or_layers, mip_level_count, sample_count, usage: i32` |
| `SamplerDescriptor3D` | `texture3d` | `min_filter, mag_filter, mip_filter, address_u, address_v, address_w: i32`; `lod_bias, min_lod, max_lod: f32`; `compare_func: i32` |
| `TextureView3D` | `texture3d` | `texture_id, dimension, format, base_mip, mip_count, base_layer, layer_count: i32` |

#### Shader and Pipeline Types

| Type | Module | Key Fields |
|------|--------|-----------|
| `ShaderModule3D` | `shader3d` | `vertex_src, fragment_src: text`; `compute_src: text` |
| `VertexAttribute3D` | `shader3d` | `location, format, offset: i32` |
| `VertexBufferLayout3D` | `shader3d` | `stride: i32`; `attributes: [VertexAttribute3D]` |
| `RenderPipelineDescriptor3D` | `shader3d` | `shader_id, vertex_layout_id: i32`; `depth_test, cull_mode, blend_mode: i32`; `topology: i32` |
| `ComputePipelineDescriptor3D` | `shader3d` | `shader_id: i32`; `entry_point: text` |

#### Bind Group Types

| Type | Module | Key Fields |
|------|--------|-----------|
| `BindGroupLayoutEntry3D` | `bind_group3d` | `binding, visibility, binding_type, buffer_size: i32` |
| `BindGroupEntry3D` | `bind_group3d` | `binding, buffer_id, texture_id, sampler_id, offset, size: i32` |
| `BindGroup3D` | `bind_group3d` | `id, layout_id: i32`; `entries: [BindGroupEntry3D]` |

### Resource Management (ResourcePool3D)

`ResourcePool3D` (`resource_pool.spl`) tracks all GPU resources with frame-age garbage collection. Each handle carries an `id` (pool index) and a `gpu_id` (backend resource ID).

```simple
use std.gpu.engine3d.resource_pool.{ResourcePool3D, TextureHandle3D, BufferHandle3D, ShaderHandle3D, PipelineHandle3D}

# Textures
val tex: TextureHandle3D = engine.load_texture(256, 256, pixels)
val tex3d: TextureHandle3D = engine.load_texture_3d(64, 64, 64, voxels)
val cube: TextureHandle3D = engine.load_cubemap(512, faces)
val depth: TextureHandle3D = engine.load_depth_texture(800, 600)
engine.unload_texture(tex)

# Shaders and pipelines
val sh: ShaderHandle3D = engine.load_shader(vert_src, frag_src)
val pl: PipelineHandle3D = engine.load_pipeline(sh, true, 0, 1)
engine.unload_shader(sh)

# Buffers
val buf: BufferHandle3D = engine.load_buffer(4096)
engine.unload_buffer(buf)

# GC resources unused for more than N frames
engine.gc_resources(3)

# Keep a resource alive for this frame
engine.touch_resource(tex.id)
```

Handle fields:
- `TextureHandle3D` — `id, gpu_id, width, height, depth, format, mip_levels, last_used_frame: i32`
- `BufferHandle3D` — `id, gpu_id, size, usage, last_used_frame: i32`
- `ShaderHandle3D` — `id, gpu_id: i32`; `vertex_src, fragment_src: text`
- `PipelineHandle3D` — `id, gpu_id, shader_id: i32`; `depth_test: bool`; `blend_mode, cull_mode: i32`

### Chrome WebGPU Texture System

**Dimension constants** (`TEX_DIM_*`):

| Constant | Value | Use |
|----------|-------|-----|
| `TEX_DIM_2D` | 0 | Standard 2D texture |
| `TEX_DIM_3D` | 1 | Volume (3D) texture |
| `TEX_DIM_CUBE` | 2 | Cubemap |
| `TEX_DIM_2D_ARRAY` | 3 | 2D texture array |
| `TEX_DIM_CUBE_ARRAY` | 4 | Cubemap array |

**Format constants** (`TEX_FMT_*`):

| Constant | Use |
|----------|-----|
| `TEX_FMT_RGBA8_UNORM` | Standard RGBA |
| `TEX_FMT_RGBA8_SRGB` | sRGB RGBA |
| `TEX_FMT_BGRA8_UNORM` | Swapped BGRA |
| `TEX_FMT_RGBA16_FLOAT` | HDR half-float |
| `TEX_FMT_RGBA32_FLOAT` | HDR full-float |
| `TEX_FMT_DEPTH32_FLOAT` | Depth buffer |
| `TEX_FMT_DEPTH24_PLUS_STENCIL8` | Depth + stencil |
| `TEX_FMT_BC1_UNORM` | BC1 compressed (DXT1) |
| `TEX_FMT_BC3_UNORM` | BC3 compressed (DXT5) |
| `TEX_FMT_BC7_UNORM` | BC7 compressed |
| `TEX_FMT_ETC2_RGB8` | ETC2 (mobile) |
| `TEX_FMT_ASTC_4X4` | ASTC 4x4 |

**Usage flags** (`TEX_USAGE_*`): `TEXTURE_BINDING` (1), `STORAGE_BINDING` (2), `RENDER_ATTACHMENT` (4), `COPY_SRC` (8), `COPY_DST` (16).

### Color Utilities (color3d.spl)

**Import:** `use std.gpu.engine3d.color3d.{rgba3d, rgb3d, srgb_to_linear, linear_to_srgb, luminance3d, tonemap_reinhard}`

Colors are packed `u32` in ARGB layout: `0xAARRGGBB`.

| Function | Signature | Description |
|----------|-----------|-------------|
| `rgba3d` | `(r, g, b, a: i32) -> u32` | Pack RGBA bytes into ARGB u32 |
| `rgb3d` | `(r, g, b: i32) -> u32` | Pack RGB (alpha=255) |
| `srgb_to_linear` | `(color: u32) -> [f32]` | Convert packed sRGB to linear `[r,g,b,a]` |
| `linear_to_srgb` | `(linear: [f32]) -> u32` | Convert linear float array to packed sRGB |
| `luminance3d` | `(color: u32) -> f32` | BT.709 relative luminance |
| `luminance_linear` | `(linear: [f32]) -> f32` | Luminance from linear float array |
| `tonemap_reinhard` | `(hdr: [f32], exposure: f32) -> u32` | Reinhard HDR→LDR tonemapping |
| `pack_hdr_color` | `(r, g, b, a: f32) -> [f32]` | Pack HDR as float array (no clamp) |

### Compositor (compositor3d.spl)

Multi-pass rendering via ordered `RenderPass3D` layers merged by `Compositor3D`.

```simple
use std.gpu.engine3d.compositor3d.{RenderPass3D, Compositor3D}

var comp = Compositor3D.create(800, 600)

var bg = RenderPass3D.create("background", 800, 600)
bg.set_z_order(0)

var fg = RenderPass3D.create("foreground", 800, 600)
fg.set_z_order(1)

comp.add_pass(bg)
comp.add_pass(fg)
comp.sort_passes()

# After rendering each pass into pass.pixels:
val final_pixels = comp.composite()
```

`RenderPass3D` fields: `name: text`; `color_target_id, depth_target_id, z_order: i32`; `clear_color: u32`; `clear_depth: f32`; `enabled: bool`; `width, height: i32`; `pixels: [u32]`.

`Compositor3D` methods: `add_pass`, `remove_pass`, `sort_passes`, `composite() -> [u32]`, `pass_count() -> i32`, `output_width/height() -> i32`.

### SIMD Acceleration (simd_kernels3d.spl)

**Import:** `use std.gpu.engine3d.simd_kernels3d.{SimdLevel3D, detect_simd_level_3d, simd_mat4_mul, simd_transform_vertices, simd_normalize_batch}`

```simple
enum SimdLevel3D:
    None_     # Scalar fallback
    Sse42     # SSE 4.2
    Avx2      # AVX2 (256-bit)
    Avx512    # AVX-512
    Neon      # ARM NEON
```

| Function | Signature | Description |
|----------|-----------|-------------|
| `detect_simd_level_3d` | `() -> SimdLevel3D` | Runtime CPU feature detection |
| `simd_mat4_mul` | `(result: [f32], a: [f32], b: [f32])` | 4x4 matrix multiply (column-major) |
| `simd_transform_vertices` | `(verts: [f32], count: i32, mvp: [f32])` | Batch vertex transform by MVP matrix |
| `simd_normalize_batch` | `(vecs: [f32], count: i32)` | Batch normalize 3D vectors |

Falls back to scalar loops when no SIMD instructions are available.
