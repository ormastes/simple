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

- [GPU Programming Guide](../guide/gpu_programming.md) - Tutorial and examples
- [GPU Backend Design](../design/gpu_backend_design.md) - Architecture details
