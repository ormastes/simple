---
name: cuda
description: CUDA, GPU computing, Vulkan SPIR-V, and SIMD development in Simple
---

# CUDA/GPU/SIMD Skill - Simple Language

## When to Use This Skill

Use this skill when working with GPU computing in Simple:
- Writing GPU kernels (CUDA, Vulkan, compute shaders)
- Using SIMD vector operations (SSE/AVX/NEON)
- Managing GPU memory (alloc, upload, download, shared)
- Launching kernels with grid/block configuration
- Translating C/CUDA code to Simple GPU idioms
- Configuring GPU backends (PTX, SPIR-V, native)

---

## GPU Kernel Syntax

### Kernel Declaration

```simple
# CUDA kernel — @gpu_kernel decorator
@gpu_kernel
fn vector_add(a: GpuArray<f32>, b: GpuArray<f32>, out: GpuArray<f32>, n: i32):
    val idx = gpu_global_id_x() + gpu_block_id_x() * gpu_block_dim_x()
    if idx < n:
        out[idx] = a[idx] + b[idx]

# Attribute syntax (equivalent)
#[gpu]
fn vector_scale(data: GpuArray<f32>, scale: f32, n: i32):
    val idx = gpu_global_id_x()
    if idx < n:
        data[idx] = data[idx] * scale

# Vulkan compute kernel
@vulkan_kernel
fn compute_shader(input: GpuBuffer<f32>, output: GpuBuffer<f32>):
    val gid = gpu_global_id_x()
    output[gid] = input[gid] * 2.0

# SIMD kernel with bounds policy
@simd
fn simd_scale(a: [f32], scale: f32):
    val i = this.index()
    a[i] = a[i] * scale
```

### Kernel Launch

```simple
# CUDA triple-chevron syntax
vector_add<<<grid: (num_blocks, 1, 1), block: (256, 1, 1)>>>(a, b, out, n)

# Context-based launch API
val config = GpuLaunchConfig.simple(num_blocks: 4, threads_per_block: 256)
ctx.launch(kernel: vector_add, config: config, args: [a, b, out, n])

# 2D grid launch (for matrix operations)
val config_2d = GpuLaunchConfig.grid_2d(
    grid_x: (cols + 15) / 16, grid_y: (rows + 15) / 16,
    block_x: 16, block_y: 16
)
```

---

## GPU Intrinsics

All GPU intrinsics require kernel context (only callable inside `@gpu_kernel` or `#[gpu]` functions).

### Thread ID Accessors

```simple
# 1D indexing (most common)
gpu_global_id_x()       # Global thread index X
gpu_local_id_x()        # Thread index within block X
gpu_block_id_x()        # Block index X
gpu_block_dim_x()       # Block dimension X
gpu_grid_dim_x()        # Grid dimension X

# Multi-dimensional (Y, Z variants)
gpu_global_id_y()       # Global thread index Y
gpu_block_id_y()        # Block index Y
gpu_block_dim_y()       # Block dimension Y
gpu_global_id_z()       # Global thread index Z

# Computed global index (common pattern)
val global_idx = gpu_block_id_x() * gpu_block_dim_x() + gpu_local_id_x()

# SIMD-style accessors (inside @simd kernels)
this.index()            # Global linear index
this.thread_index()     # Local thread index within group
this.group_index()      # Group ID
```

### Synchronization

```simple
gpu_syncthreads()       # Synchronize threads in block (__syncthreads)
gpu_barrier()           # Thread barrier
gpu_mem_fence()         # Memory fence
gpu_barrier_and_fence() # Combined barrier + memory fence

# Barrier scopes (enum GpuBarrierScope)
# - Workgroup   thread block / workgroup level
# - Device      device-wide barrier
# - Subgroup    warp / subgroup level
```

### Atomic Operations

```simple
gpu_atomic_add(ptr, value)               # Atomic addition
gpu_atomic_sub(ptr, value)               # Atomic subtraction
gpu_atomic_min(ptr, value)               # Atomic minimum
gpu_atomic_max(ptr, value)               # Atomic maximum
gpu_atomic_and(ptr, value)               # Atomic bitwise AND
gpu_atomic_or(ptr, value)                # Atomic bitwise OR
gpu_atomic_xor(ptr, value)               # Atomic bitwise XOR
gpu_atomic_exchange(ptr, value)          # Atomic exchange (returns old)
gpu_atomic_cas(ptr, expected, desired)   # Compare-and-swap
```

### Shared Memory

```simple
# Allocate shared memory (per-block)
val shared = gpu_shared_mem<f32>(256)

# Typical shared memory pattern
@gpu_kernel
fn reduce_sum(input: GpuArray<f32>, output: GpuArray<f32>, n: i32):
    val tid = gpu_local_id_x()
    val gid = gpu_block_id_x() * gpu_block_dim_x() + tid
    val shared = gpu_shared_mem<f32>(256)

    # Load to shared memory
    if gid < n:
        shared[tid] = input[gid]
    else:
        shared[tid] = 0.0
    gpu_syncthreads()

    # Reduction in shared memory
    var stride = gpu_block_dim_x() / 2
    while stride > 0:
        if tid < stride:
            shared[tid] = shared[tid] + shared[tid + stride]
        gpu_syncthreads()
        stride = stride / 2

    # Write result
    if tid == 0:
        output[gpu_block_id_x()] = shared[0]
```

---

## GPU API Layers (3 Tiers)

### Tier 1: Runtime API (`std.gpu_runtime`) — Interpreter Compatible

**Location:** `src/lib/nogc_sync_mut/gpu_runtime/`

High-level queries and tensor operations. Works in interpreter mode.

```simple
use std.gpu_runtime.*

# Device queries
val available = gpu_available()        # -> bool
val backend = gpu_backend_name()       # -> text ("cuda", "vulkan", "none")
val count = gpu_device_count()         # -> i32
gpu_ctx_info()                         # Print device info

# Tensor operations (handle-based)
val t1 = gpu_tensor_zeros(rows: 4, cols: 4)
val t2 = gpu_tensor_ones(rows: 4, cols: 4)
val gpu_t = gpu_tensor_to_cuda(t1, device: 0)
val is_gpu = gpu_tensor_is_cuda(gpu_t)   # -> bool
val numel = gpu_tensor_numel(gpu_t)      # -> i64

# Allocation helpers
val zeros = gpu_alloc_zeros(rows: 1024, cols: 1024, use_gpu: true, device_id: 0)
val ones = gpu_alloc_ones(rows: 512, cols: 512, use_gpu: true, device_id: 0)

# Stream operations
val stream = gpu_stream_create(device: 0)
gpu_stream_sync(stream)
val done = gpu_stream_query(stream)    # -> bool (non-blocking check)
```

### Tier 2: Full API (`std.gpu`) — Compiler Required, Type-Safe

**Location:** `src/lib/gc_async_mut/gpu.spl`

Structured types with `Result<T, GpuError>` error handling. Requires compiled mode.

```simple
use std.gpu.*

# Device management
val device = GpuDevice.default()?          # First available GPU
val device2 = GpuDevice.get(1)?            # Specific device
val count = GpuDevice.count()
val name = device.name()                   # "NVIDIA GeForce RTX 4090"
val (major, minor) = device.compute_capability()

# Context
val ctx = GpuContext.create(device)?
ctx.synchronize()?
ctx.destroy()?

# Memory management
val gpu_mem = gpu_alloc(size: 1024 * 4)?   # Allocate 4KB
gpu_upload(gpu_mem, host_ptr, size: 1024 * 4)?
gpu_download(gpu_mem, host_ptr, size: 1024 * 4)?
gpu_memset(gpu_mem, value: 0, size: 1024 * 4)?
gpu_free(gpu_mem)?

# Module & kernel launch
val module = GpuModule.load_ptx(ptx_code)?
val module2 = GpuModule.load_file("kernel.ptx")?
val config = GpuLaunchConfig.simple(num_blocks: 4, threads_per_block: 256)
gpu_launch(module, func_name: "vector_add", config: config, args_ptr: args)?
gpu_sync()?
module.unload()?

# Launch configurations
val simple = GpuLaunchConfig.simple(4, 256)
val grid2d = GpuLaunchConfig.grid_2d(32, 32, 16, 16)
val grid3d = GpuLaunchConfig.grid_3d(8, 8, 8, 4, 4, 4)
val total = config.total_threads()
```

### Tier 3: Low-Level FFI (`std.cuda`) — Direct Driver API

**Location:** `src/compiler/70.backend/backend/cuda/cuda_ffi.spl`

Direct CUDA runtime FFI bindings. For advanced use cases only.

```simple
# Device management
extern fn rt_cuda_init() -> i64
extern fn rt_cuda_device_get(device_id: i64) -> i64
extern fn rt_cuda_device_count() -> i64
extern fn rt_cuda_device_name(device: i64) -> text
extern fn rt_cuda_device_compute_capability(device: i64) -> i64

# Context management
extern fn rt_cuda_ctx_create(device: i64) -> i64
extern fn rt_cuda_ctx_destroy(ctx: i64) -> i64
extern fn rt_cuda_ctx_synchronize() -> i64

# Memory management
extern fn rt_cuda_mem_alloc(size: i64) -> i64
extern fn rt_cuda_mem_free(ptr: i64) -> i64
extern fn rt_cuda_memcpy_htod(dst: i64, src: i64, size: i64) -> i64
extern fn rt_cuda_memcpy_dtoh(dst: i64, src: i64, size: i64) -> i64
extern fn rt_cuda_memcpy_dtod(dst: i64, src: i64, size: i64) -> i64
extern fn rt_cuda_memset(ptr: i64, value: i64, size: i64) -> i64

# Module & kernel
extern fn rt_cuda_module_load(path: text) -> i64
extern fn rt_cuda_module_load_data(ptx: text) -> i64
extern fn rt_cuda_module_get_function(module: i64, func_name: text) -> i64
extern fn rt_cuda_launch_kernel(module: i64, func_name: text,
    grid_x: i64, grid_y: i64, grid_z: i64,
    block_x: i64, block_y: i64, block_z: i64,
    args_ptr: i64) -> i64
extern fn rt_cuda_sync() -> i64

# Error handling
extern fn rt_cuda_get_error_string(error_code: i64) -> text
```

---

## SIMD Features

**Location:** `src/lib/nogc_sync_mut/simd.spl`

### Platform Detection

```simple
use std.simd.*

fn has_sse() -> bool         # 128-bit SSE (x86)
fn has_avx() -> bool         # 256-bit AVX (x86)
fn has_avx2() -> bool        # 256-bit integer AVX2 (x86)
fn has_neon() -> bool        # 128-bit ARM NEON
fn simd_width() -> i64       # Returns 128, 256, 512, or 0
```

### Vector Types

```simple
# 128-bit vectors (SSE/NEON)
struct Vec4f:                # 4x f32
    x: f32, y: f32, z: f32, w: f32
    static fn splat(value: f32) -> Vec4f
    static fn from_array(arr: [f32]) -> Vec4f
    static fn zero() -> Vec4f
    fn to_array() -> [f32]

struct Vec4i:                # 4x i32
    x: i32, y: i32, z: i32, w: i32
    static fn splat(value: i32) -> Vec4i
    static fn from_array(arr: [i32]) -> Vec4i
    static fn zero() -> Vec4i
    fn to_array() -> [i32]

struct Vec4d:                # 4x f64 (AVX required, no NEON)
    x: f64, y: f64, z: f64, w: f64
    static fn splat(value: f64) -> Vec4d
    static fn from_array(arr: [f64]) -> Vec4d
    static fn zero() -> Vec4d
    fn to_array() -> [f64]

# 256-bit vectors (AVX2 required)
struct Vec8f:                # 8x f32
    e0: f32, e1: f32, ..., e7: f32
    static fn splat(value: f32) -> Vec8f
    static fn from_array(arr: [f32]) -> Vec8f
    static fn zero() -> Vec8f
    fn to_array() -> [f32]

struct Vec8i:                # 8x i32
    e0: i32, e1: i32, ..., e7: i32
    static fn splat(value: i32) -> Vec8i
    static fn from_array(arr: [i32]) -> Vec8i
    static fn zero() -> Vec8i
    fn to_array() -> [i32]
```

### SIMD Intrinsics

```simple
# f32x4 operations (SSE/NEON)
fn simd_add_f32x4(a: Vec4f, b: Vec4f) -> Vec4f
fn simd_sub_f32x4(a: Vec4f, b: Vec4f) -> Vec4f
fn simd_mul_f32x4(a: Vec4f, b: Vec4f) -> Vec4f
fn simd_div_f32x4(a: Vec4f, b: Vec4f) -> Vec4f
fn simd_fma_f32x4(a: Vec4f, b: Vec4f, c: Vec4f) -> Vec4f  # a*b + c

# f32x8 operations (AVX2)
fn simd_add_f32x8(a: Vec8f, b: Vec8f) -> Vec8f
fn simd_sub_f32x8(a: Vec8f, b: Vec8f) -> Vec8f
fn simd_mul_f32x8(a: Vec8f, b: Vec8f) -> Vec8f
fn simd_div_f32x8(a: Vec8f, b: Vec8f) -> Vec8f
fn simd_fma_f32x8(a: Vec8f, b: Vec8f, c: Vec8f) -> Vec8f

# f64x4 operations (AVX2)
fn simd_add_f64x4(a: Vec4d, b: Vec4d) -> Vec4d
fn simd_mul_f64x4(a: Vec4d, b: Vec4d) -> Vec4d
fn simd_fma_f64x4(a: Vec4d, b: Vec4d, c: Vec4d) -> Vec4d

# i32x4 operations (SSE/NEON)
fn simd_add_i32x4(a: Vec4i, b: Vec4i) -> Vec4i
fn simd_sub_i32x4(a: Vec4i, b: Vec4i) -> Vec4i
fn simd_mul_i32x4(a: Vec4i, b: Vec4i) -> Vec4i

# i32x8 operations (AVX2)
fn simd_add_i32x8(a: Vec8i, b: Vec8i) -> Vec8i
fn simd_sub_i32x8(a: Vec8i, b: Vec8i) -> Vec8i
fn simd_mul_i32x8(a: Vec8i, b: Vec8i) -> Vec8i
```

### SIMD Example: Dot Product

```simple
use std.simd.*

fn dot_product_simd(a: [f32], b: [f32], n: i64) -> f32:
    var sum = Vec4f.zero()
    var i = 0
    while i + 4 <= n:
        val va = Vec4f.from_array(a[i..i+4])
        val vb = Vec4f.from_array(b[i..i+4])
        sum = simd_fma_f32x4(va, vb, sum)
        i = i + 4
    # Horizontal sum
    val arr = sum.to_array()
    var result = arr[0] + arr[1] + arr[2] + arr[3]
    # Scalar tail
    while i < n:
        result = result + a[i] * b[i]
        i = i + 1
    result
```

---

## Backend Configuration

### Backend Targets

| Backend | Output | Decorator | Use Case |
|---------|--------|-----------|----------|
| CUDA | PTX assembly | `@gpu_kernel` | NVIDIA GPUs |
| Vulkan | SPIR-V binary | `@vulkan_kernel` | Cross-platform GPU |
| Native | AVX2/NEON instructions | `@simd` | CPU SIMD |
| C | Scalar C code | `@simd` (fallback) | Portable, no SIMD HW |

### Compile Commands

```bash
# GPU kernel compilation
bin/simple compile --backend=cuda kernel.spl -o kernel.ptx
bin/simple compile --backend=vulkan shader.spl -o shader.spv

# SIMD compilation (auto-detects platform)
bin/simple compile --backend=native --simd=avx2 math.spl
bin/simple compile --backend=native --simd=neon math.spl   # ARM

# Full project with GPU support
bin/simple build --gpu=cuda
bin/simple build --gpu=vulkan
```

### SDN Configuration

```sdn
# project.sdn — GPU settings
gpu:
    backend: "cuda"           # cuda, vulkan, auto
    device: 0
    memory_limit: "8GB"
    compute_capability: "8.6"
    default_block_size: 256
    data_type: "f32"          # f32, f16, bf16
```

### Environment Variables

- `SIMPLE_GPU_BACKEND` — Override backend selection
- `SIMPLE_GPU_DEVICE` — Override device ID
- `CUDA_VISIBLE_DEVICES` — Control visible GPUs (NVIDIA standard)
- `SIMPLE_GPU_DEBUG` — Enable GPU debug output

---

## Bounds Policy (`@bounds`)

Controls out-of-bounds behavior in GPU kernels:

```simple
# Default: out-of-bounds access returns from thread (safe)
@simd(bounds=default=return, strict=true)
fn safe_kernel(data: [f32]):
    val i = this.index()
    data[i] = data[i] * 2.0    # Auto-returns if i >= len

# No bounds checking (faster, unsafe)
@simd(bounds=unchecked)
fn fast_kernel(data: [f32]):
    val i = this.index()
    data[i] = data[i] * 2.0    # UB if out of bounds
```

---

## Memory Spaces

```simple
# Memory space qualifiers in CUDA type mapper
# Global   — __global__    device global memory (large, slow)
# Shared   — __shared__    block shared memory (fast, limited ~48KB)
# Local    —               thread-local / register
# Constant — __constant__  constant memory (cached, read-only)
```

### Memory Transfer Pattern

```simple
use std.gpu.*

# Host -> Device -> Compute -> Device -> Host
val host_data = [1.0, 2.0, 3.0, 4.0]
val gpu_ptr = gpu_alloc(size: 4 * 4)?         # 4 floats * 4 bytes
gpu_upload(gpu_ptr, host_data.ptr(), size: 16)?

val config = GpuLaunchConfig.simple(1, 256)
gpu_launch(module, "scale_kernel", config, args)?
gpu_sync()?

var result = [0.0, 0.0, 0.0, 0.0]
gpu_download(gpu_ptr, result.ptr(), size: 16)?
gpu_free(gpu_ptr)?
```

---

## Best Practices

### DO

- Use `Result<T, GpuError>` with `?` for all GPU operations
- Check `gpu_available()` before GPU code paths
- Use `GpuLaunchConfig.simple()` for 1D problems
- Coalesce memory accesses (sequential threads access sequential memory)
- Use shared memory for data reused across threads in a block
- Always `gpu_syncthreads()` between shared memory write and read
- Use `@simd` with `Vec4f`/`Vec8f` for CPU fallback paths
- Check platform with `has_avx2()`/`has_neon()` before SIMD
- Free GPU memory in reverse allocation order
- Use Tier 2 (Full API) for most code, Tier 3 (FFI) only when needed

### DON'T

- Don't access shared memory across blocks (undefined behavior)
- Don't assume warp size (use `gpu_block_dim_x()` for portability)
- Don't mix CUDA and Vulkan in the same compilation unit
- Don't call GPU intrinsics outside kernel context
- Don't forget `gpu_sync()` before reading results back
- Don't use `Vec8f`/`Vec8i` without checking `has_avx2()`
- Don't allocate GPU memory in a loop without freeing

---

## C/CUDA to Simple Translation Guide

### Vector Add

**C/CUDA:**
```c
__global__ void vector_add(float *a, float *b, float *c, int n) {
    int idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx < n) c[idx] = a[idx] + b[idx];
}
// Launch: vector_add<<<(n+255)/256, 256>>>(a, b, c, n);
```

**Simple:**
```simple
@gpu_kernel
fn vector_add(a: GpuArray<f32>, b: GpuArray<f32>, c: GpuArray<f32>, n: i32):
    val idx = gpu_block_id_x() * gpu_block_dim_x() + gpu_local_id_x()
    if idx < n:
        c[idx] = a[idx] + b[idx]

# Launch
val blocks = (n + 255) / 256
vector_add<<<grid: (blocks, 1, 1), block: (256, 1, 1)>>>(a, b, c, n)
```

### Matrix Multiply with Shared Memory

**Simple:**
```simple
@gpu_kernel
fn matmul_shared(a: GpuArray<f32>, b: GpuArray<f32>, c: GpuArray<f32>,
                 m: i32, n: i32, k: i32):
    val TILE = 16
    val row = gpu_block_id_y() * TILE + gpu_local_id_y()
    val col = gpu_block_id_x() * TILE + gpu_local_id_x()
    val tx = gpu_local_id_x()
    val ty = gpu_local_id_y()

    val tile_a = gpu_shared_mem<f32>(TILE * TILE)
    val tile_b = gpu_shared_mem<f32>(TILE * TILE)
    var sum = 0.0

    var t = 0
    while t < k:
        # Load tiles
        if row < m and (t + tx) < k:
            tile_a[ty * TILE + tx] = a[row * k + t + tx]
        else:
            tile_a[ty * TILE + tx] = 0.0
        if col < n and (t + ty) < k:
            tile_b[ty * TILE + tx] = b[(t + ty) * n + col]
        else:
            tile_b[ty * TILE + tx] = 0.0
        gpu_syncthreads()

        # Compute
        var i = 0
        while i < TILE:
            sum = sum + tile_a[ty * TILE + i] * tile_b[i * TILE + tx]
            i = i + 1
        gpu_syncthreads()
        t = t + TILE

    if row < m and col < n:
        c[row * n + col] = sum
```

---

## Key Files

| File | Purpose |
|------|---------|
| `src/compiler/70.backend/gpu_intrinsics.spl` | GPU intrinsic recognition & validation |
| `src/compiler/70.backend/backend/gpu_codegen_types.spl` | GpuCodegen trait, barrier/atomic types |
| `src/compiler/70.backend/backend/common/gpu_codegen.spl` | GPU codegen interface |
| `src/compiler/70.backend/backend/cuda_backend.spl` | CUDA → PTX compiler |
| `src/compiler/70.backend/backend/cuda/ptx_builder.spl` | PTX assembly builder |
| `src/compiler/70.backend/backend/cuda/cuda_ffi.spl` | CUDA driver FFI bindings |
| `src/compiler/70.backend/backend/cuda/cuda_launcher.spl` | Kernel launcher |
| `src/compiler/70.backend/backend/cuda_type_mapper.spl` | MIR → CUDA type mapping |
| `src/compiler/70.backend/backend/vulkan_backend.spl` | Vulkan → SPIR-V compiler |
| `src/lib/gc_async_mut/gpu.spl` | High-level GPU memory & device API |
| `src/lib/gc_async_mut/io/cuda_ffi.spl` | CUDA wrapper functions |
| `src/lib/nogc_sync_mut/simd.spl` | SIMD vector types & intrinsics |
| `src/lib/nogc_sync_mut/gpu_runtime/` | Runtime API (interpreter compatible) |
| `src/compiler/00.common/simd_types.spl` | SIMD element/vector type defs |
| `src/compiler/35.semantics/simd_check.spl` | SIMD type checking & validation |
| `doc/guide/backend/gpu_programming.md` | GPU programming guide |
| `doc/spec/gpu_simd/gpu.md` | GPU/SIMD specification |

## See Also

- `/deeplearning` — ML pipelines with `~>`, dimension checking, training loops
- `/sffi` — FFI wrapper patterns for external C/CUDA libraries
- `/coding` — Simple language rules and coding standards
- `/architecture` — Compiler pipeline (70.backend layer)
