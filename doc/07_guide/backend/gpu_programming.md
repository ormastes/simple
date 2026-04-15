# GPU Programming

**Version:** 0.5.0
**Status:** CUDA (Production), Vulkan (Development), SIMD (Planned)

---

## Overview

Simple supports GPU compute programming through CUDA and Vulkan backends. Write compute kernels in Simple syntax, compile to GPU code, and run on NVIDIA or cross-platform GPUs.

**Two APIs available:**
- **Runtime API** (`std.gpu_runtime`) -- Works today with the interpreter, no compiler needed
- **Full API** (`std.gpu`) -- Requires the compiler, type-safe generics, RAII

---

## Quick Start: Runtime API (Works Now)

```simple
use std.gpu_runtime.{gpu_available, gpu_alloc_zeros, gpu_tensor_is_cuda}

fn main():
    if not gpu_available():
        print "No GPU available"
        return

    val tensor = gpu_alloc_zeros(1000, 1000, use_gpu: true, device_id: 0)
    print "On GPU: {gpu_tensor_is_cuda(tensor)}"
```

```bash
bin/simple examples/gpu/runtime_example.spl
```

---

## Runtime API Reference

### Detection

| Function | Returns | Description |
|----------|---------|-------------|
| `gpu_available()` | `bool` | Check if GPU is available |
| `gpu_backend_name()` | `text` | Backend name ("CUDA" or "CPU") |
| `gpu_device_count()` | `i32` | Number of GPUs |
| `gpu_ctx_info()` | -- | Print GPU information |

### Tensor Operations

| Function | Returns | Description |
|----------|---------|-------------|
| `gpu_tensor_zeros(rows, cols)` | `i64` | Create zero tensor (CPU) |
| `gpu_tensor_ones(rows, cols)` | `i64` | Create ones tensor (CPU) |
| `gpu_tensor_to_cuda(handle, device)` | `i64` | Move tensor to GPU |
| `gpu_tensor_is_cuda(handle)` | `bool` | Check if on GPU |
| `gpu_tensor_numel(handle)` | `i64` | Get element count |

### Allocation Helpers

| Function | Returns | Description |
|----------|---------|-------------|
| `gpu_alloc_zeros(rows, cols, use_gpu, device)` | `i64` | Allocate zeros |
| `gpu_alloc_ones(rows, cols, use_gpu, device)` | `i64` | Allocate ones |

### Stream Operations (Async)

| Function | Returns | Description |
|----------|---------|-------------|
| `gpu_stream_create(device)` | `i64` | Create async stream |
| `gpu_stream_sync(handle)` | -- | Wait for stream completion |
| `gpu_stream_query(handle)` | `bool` | Check if stream complete |
| `gpu_async_upload_batch(...)` | `i64` | Async upload to GPU |

---

## Full API: CUDA Kernels (Compiler Required)

### Kernel Syntax

```simple
@gpu_kernel
fn vector_add(a: GpuArray<f32>, b: GpuArray<f32>, out: GpuArray<f32>, n: i32):
    val idx = gpu_thread_id_x() + gpu_block_id_x() * gpu_block_dim_x()
    if idx < n:
        out[idx] = a[idx] + b[idx]
```

### Device and Memory Management

```simple
use std.gpu.{Context, GpuArray}

fn main():
    val ctx = Context.default()

    # Allocate on GPU
    val a = ctx.alloc_zeros<f32>(1024)
    val b = ctx.alloc_ones<f32>(1024)
    val out = ctx.alloc_zeros<f32>(1024)

    # Launch kernel
    val grid = (1024 / 256, 1, 1)
    val block = (256, 1, 1)
    vector_add<<<grid, block>>>(a, b, out, 1024)

    # Automatic cleanup via RAII
```

### GPU Intrinsics

| Intrinsic | Description |
|-----------|-------------|
| `gpu_thread_id_x/y/z()` | Thread index in block |
| `gpu_block_id_x/y/z()` | Block index in grid |
| `gpu_block_dim_x/y/z()` | Block dimensions |
| `gpu_grid_dim_x/y/z()` | Grid dimensions |
| `gpu_syncthreads()` | Synchronize threads in block |
| `gpu_shared_mem<T>(size)` | Shared memory allocation |

### Shared Memory

```simple
@gpu_kernel
fn reduce_sum(input: GpuArray<f32>, output: GpuArray<f32>, n: i32):
    val shared = gpu_shared_mem<f32>(256)
    val tid = gpu_thread_id_x()
    val idx = gpu_block_id_x() * gpu_block_dim_x() + tid

    shared[tid] = if idx < n: input[idx] else: 0.0

    gpu_syncthreads()

    # Parallel reduction
    var stride = gpu_block_dim_x() / 2
    while stride > 0:
        if tid < stride:
            shared[tid] = shared[tid] + shared[tid + stride]
        gpu_syncthreads()
        stride = stride / 2

    if tid == 0:
        output[gpu_block_id_x()] = shared[0]
```

### Atomic Operations

| Operation | Signature |
|-----------|-----------|
| `gpu_atomic_add` | `(ptr: GpuPtr<T>, val: T) -> T` |
| `gpu_atomic_sub` | `(ptr: GpuPtr<T>, val: T) -> T` |
| `gpu_atomic_min` | `(ptr: GpuPtr<T>, val: T) -> T` |
| `gpu_atomic_max` | `(ptr: GpuPtr<T>, val: T) -> T` |
| `gpu_atomic_cas` | `(ptr: GpuPtr<T>, compare: T, val: T) -> T` |

---

## Vulkan Compute

### Setup

```bash
# Linux
sudo apt install vulkan-tools libvulkan-dev spirv-tools glslang-tools

# macOS (MoltenVK)
brew install vulkan-tools molten-vk spirv-tools glslang

# Verify
vulkaninfo --summary
```

### Vulkan Kernel

```simple
@vulkan_kernel
fn saxpy(a: f32, x: Buffer<f32>, y: Buffer<f32>, result: Buffer<f32>):
    val idx = vulkan_global_id_x()
    result[idx] = a * x[idx] + y[idx]
```

### Vulkan API

```simple
use std.gpu.vulkan.{VulkanContext, Buffer}

fn main():
    val ctx = VulkanContext.create()?

    val x = ctx.create_buffer<f32>(1024)?
    val y = ctx.create_buffer<f32>(1024)?
    val result = ctx.create_buffer<f32>(1024)?

    # Upload data
    x.upload([1.0, 2.0, 3.0, ...])
    y.upload([4.0, 5.0, 6.0, ...])

    # Dispatch compute shader
    ctx.dispatch(saxpy, args: (2.0, x, y, result), groups: (1024 / 64, 1, 1))
    ctx.wait()

    # Download results
    val output = result.download()
```

### CUDA vs Vulkan

| Feature | CUDA | Vulkan Compute |
|---------|------|---------------|
| Platform | NVIDIA only | Cross-platform |
| Shared memory | `gpu_shared_mem<T>()` | `vulkan_shared<T>()` |
| Thread sync | `gpu_syncthreads()` | `vulkan_barrier()` |
| Atomic ops | Full | Full |
| Performance | Best on NVIDIA | Competitive |
| Setup | CUDA toolkit | Vulkan SDK + SPIR-V tools |
| Debug tools | CUDA-GDB, nsight | RenderDoc, validation layers |

---

## GPU Configuration

### SDN Config Format

GPU settings use the three-level SDN configuration system:

```sdn
# gpu.sdn (project level)
gpu:
    backend: "cuda"
    device: 0
    memory_limit: "8GB"
    compute_capability: "8.6"
    default_block_size: 256
```

### Config Levels

| Level | File | Scope |
|-------|------|-------|
| User | `~/.simple/gpu.sdn` | All projects |
| Project | `project_root/gpu.sdn` | This project |
| Local | `project_root/gpu_local.sdn` | This machine only (gitignored) |

Priority: Local > Project > User

### Key Settings

| Setting | Values | Default | Description |
|---------|--------|---------|-------------|
| `backend` | `cuda`, `vulkan`, `auto` | `auto` | GPU backend |
| `device` | `0`, `1`, ... | `0` | Default GPU device |
| `memory_limit` | `"4GB"`, `"8GB"` | `"8GB"` | Max GPU memory |
| `data_type` | `f32`, `f16`, `bf16` | `f32` | Default data type |
| `default_block_size` | 64-1024 | 256 | CUDA block size |

### Preset Configurations

```sdn
# Development (fast iteration)
gpu:
    backend: "auto"
    data_type: "f32"
    memory_limit: "4GB"

# Training (maximum performance)
gpu:
    backend: "cuda"
    data_type: "bf16"
    memory_limit: "24GB"
    default_block_size: 512

# Inference (portable)
gpu:
    backend: "vulkan"
    data_type: "f16"
    memory_limit: "2GB"
```

### Environment Variables

| Variable | Description |
|----------|-------------|
| `SIMPLE_GPU_BACKEND` | Override backend selection |
| `SIMPLE_GPU_DEVICE` | Override device ID |
| `CUDA_VISIBLE_DEVICES` | Control visible NVIDIA GPUs |
| `SIMPLE_GPU_DEBUG` | Enable GPU debug output |

---

## Acceleration Modes

For deep learning workloads, Simple supports three execution modes:

| Mode | Description | Performance |
|------|-------------|-------------|
| **PureSimple** | All computation in Simple | Baseline |
| **PyTorchFFI** | Delegate to PyTorch via FFI | 10-100x faster |
| **Auto** | Automatic selection by operation size | Best of both |

### Configuration

```sdn
# acceleration.sdn
acceleration:
    mode: "auto"
    threshold: 1000        # Elements below threshold use PureSimple
    pytorch_path: "/usr/lib/libtorch"
```

### Auto Mode Behavior

| Operation | Elements < threshold | Elements >= threshold |
|-----------|---------------------|----------------------|
| Matrix multiply | PureSimple | PyTorchFFI |
| Convolution | PureSimple | PyTorchFFI |
| Element-wise | PureSimple | PureSimple |
| Reduction | PureSimple | PyTorchFFI |

---

## SIMD API (Planned)

### Platform Detection

```simple
use std.simd.{simd_supported, SimdLevel}

fn main():
    match simd_supported():
        SimdLevel.AVX512: print "AVX-512 available"
        SimdLevel.AVX2: print "AVX2 available"
        SimdLevel.SSE42: print "SSE4.2 available"
        SimdLevel.NEON: print "ARM NEON available"
        SimdLevel.None: print "No SIMD"
```

### Vector Types

```simple
use std.simd.{f32x8, i32x8}

fn simd_add(a: List<f32>, b: List<f32>) -> List<f32>:
    val result = List<f32>.with_capacity(a.len())
    var i = 0
    while i + 8 <= a.len():
        val va = f32x8.load(a, i)
        val vb = f32x8.load(b, i)
        val vr = va + vb
        vr.store(result, i)
        i = i + 8
    # Handle remainder
    while i < a.len():
        result.add(a[i] + b[i])
        i = i + 1
    result
```

### Planned Operations

| Category | Operations |
|----------|------------|
| Arithmetic | `+`, `-`, `*`, `/`, `abs`, `sqrt` |
| Comparison | `eq`, `lt`, `gt`, `min`, `max` |
| Load/Store | `load`, `store`, `gather`, `scatter` |
| Reduction | `sum`, `product`, `min_element`, `max_element` |
| Bitwise | `and`, `or`, `xor`, `shift_left`, `shift_right` |

---

## Usage Patterns

### Async Batch Processing

```simple
use std.gpu_runtime.{gpu_stream_create, gpu_async_upload_batch, gpu_stream_sync}

fn process_batches(num_batches: i64):
    val stream = gpu_stream_create(0)

    for i in 0..num_batches:
        val batch = gpu_async_upload_batch(32, 32, device_id: 0, stream_handle: stream)
        # Do CPU work while GPU processes...
        gpu_stream_sync(stream)
        print "Batch {i + 1} complete"
```

### Multi-GPU

```simple
use std.gpu_runtime.{gpu_device_count, gpu_alloc_zeros}

fn multi_gpu():
    val num_gpus = gpu_device_count()
    print "Using {num_gpus} GPUs"

    val gpu0_data = gpu_alloc_zeros(100, 100, use_gpu: true, device_id: 0)
    val gpu1_data = gpu_alloc_zeros(100, 100, use_gpu: true, device_id: 1)
```

### Training Loop

```simple
fn train(epochs: i64, batches: i64):
    val stream = gpu_stream_create(0)

    for epoch in 0..epochs:
        for batch in 0..batches:
            val data = gpu_async_upload_batch(64, 64, device_id: 0, stream_handle: stream)
            # Forward pass, backward pass, optimizer step...
            gpu_stream_sync(stream)
```

---

## Performance Tips

1. **Minimize host-device transfers** -- Keep data on GPU as long as possible
2. **Use async streams** -- Overlap computation and data transfer
3. **Choose block size carefully** -- 256 is a good default; benchmark for your workload
4. **Coalesce memory access** -- Adjacent threads should access adjacent memory
5. **Use shared memory** -- For data reused within a thread block
6. **Prefer bf16/f16** -- Half-precision is 2x faster on modern GPUs for training
7. **Batch operations** -- Larger batches amortize kernel launch overhead

---

## Troubleshooting

| Issue | Cause | Fix |
|-------|-------|-----|
| `gpu_available()` returns false | No GPU or driver issue | Install CUDA toolkit or Vulkan SDK |
| Out of memory | Allocation exceeds GPU RAM | Reduce batch size or use `memory_limit` config |
| Slow performance | Small kernel launches | Increase batch size, use async streams |
| Vulkan validation error | API misuse | Enable `SIMPLE_GPU_DEBUG=1`, check validation layers |
| CUDA version mismatch | Toolkit/driver incompatible | Match CUDA toolkit to driver version |
| Kernel launch failure | Invalid grid/block dims | Block size must be multiple of 32, max 1024 |

---

## Related Documentation

- Backend overview: `doc/07_guide/backend/backends.md`
- Vulkan details: `doc/07_guide/backend/vulkan.md`
- Deep learning: `doc/07_guide/deep_learning/deep_learning.md`
- GPU config: Uses SDN format (see `doc/07_guide/quick_reference/syntax_quick_reference.md`)
