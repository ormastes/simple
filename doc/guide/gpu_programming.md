# GPU Programming Guide

This guide covers GPU compute programming in Simple, supporting both NVIDIA CUDA and Vulkan backends.

## Table of Contents

1. [Getting Started](#getting-started)
2. [CUDA vs Vulkan](#cuda-vs-vulkan)
3. [Device Management](#device-management)
4. [Memory Management](#memory-management)
5. [Writing Kernels](#writing-kernels)
6. [Kernel Execution](#kernel-execution)
7. [Synchronization](#synchronization)
8. [Performance Optimization](#performance-optimization)
9. [Error Handling](#error-handling)
10. [Examples](#examples)

---

## Getting Started

### Prerequisites

- **CUDA**: NVIDIA GPU with CUDA Toolkit installed (for CUDA backend)
- **Vulkan**: Vulkan SDK installed (for Vulkan backend)

### Quick Start

```simple
use std.gpu.*

# Get the default GPU (auto-selects best available)
val gpu = gpu_default()

if gpu.is_valid():
    print "Using GPU: {gpu.name()}"
    print "Backend: {gpu.backend_name()}"
    print "Memory: {gpu.total_memory() / 1024 / 1024} MB"
else:
    print "No GPU available"
```

### Checking GPU Availability

```simple
use std.gpu.*

# Check if any GPU is available
if gpu_available():
    print "GPU count: {gpu_count()}"

    # List all available GPUs
    for device in list_all_gpus():
        print "  [{device.backend}:{device.device_id}] {device.name}"

# Check specific backends
use io.cuda_ffi.cuda_available
use io.vulkan_ffi.vulkan_available

if cuda_available():
    print "CUDA is available"
if vulkan_available():
    print "Vulkan is available"
```

---

## CUDA vs Vulkan

### When to Use CUDA

- **NVIDIA GPUs only**: CUDA is proprietary to NVIDIA
- **Maximum performance**: CUDA often has better optimization for NVIDIA hardware
- **Extensive ecosystem**: cuBLAS, cuDNN, cuFFT libraries
- **Easier debugging**: CUDA has better debugging tools (cuda-gdb, Nsight)
- **PTX assembly**: Fine-grained control over GPU code

### When to Use Vulkan

- **Cross-platform**: Works on AMD, Intel, NVIDIA, and mobile GPUs
- **No vendor lock-in**: Open standard by Khronos Group
- **Graphics integration**: If you also need graphics rendering
- **Lower-level control**: More explicit resource management

### Feature Comparison

| Feature | CUDA | Vulkan |
|---------|------|--------|
| Vendor Support | NVIDIA only | AMD, Intel, NVIDIA, Mobile |
| Ease of Use | Easier | More verbose |
| Performance | Excellent on NVIDIA | Good on all vendors |
| Debugging | Excellent | Limited |
| Shared Memory | Native support | Workgroup memory |
| Atomic Operations | Full support | Full support |
| Dynamic Parallelism | Yes | Limited |

### Recommendation

- Use **CUDA** if targeting NVIDIA GPUs exclusively
- Use **Vulkan** for cross-platform or AMD/Intel GPU support
- The unified `std.gpu` API abstracts most differences

---

## Device Management

### Selecting a Device

```simple
use std.gpu.*

# Auto-select best GPU
val gpu = gpu_default()

# Explicitly select CUDA device 0
val cuda_gpu = gpu_cuda(0)

# Explicitly select Vulkan device 0
val vulkan_gpu = gpu_vulkan(0)

# Check validity
if gpu.is_valid():
    print "Device ready: {gpu.name()}"
```

### Multi-GPU Support

```simple
use std.gpu.*

# Enumerate all GPUs
val devices = list_all_gpus()

for device in devices:
    val gpu = match device.backend:
        case Cuda: gpu_cuda(device.device_id)
        case Vulkan: gpu_vulkan(device.device_id)
        case None: gpu_default()

    if gpu.is_valid():
        # Use this GPU...
        print "Working on {gpu.name()}"
```

### Device Information

```simple
use std.gpu.*

val gpu = gpu_default()
print "Name: {gpu.name()}"
print "Memory: {gpu.total_memory()} bytes"
print "Backend: {gpu.backend_name()}"

# Detailed CUDA info
use io.cuda_ffi.*
if cuda_available():
    val info = cuda_device_info(0)
    val (major, minor) = info.compute_capability
    print "CUDA Compute Capability: {major}.{minor}"

# Detailed Vulkan info
use io.vulkan_ffi.*
if vulkan_available():
    vulkan_init()
    val info = vulkan_device_info(0)
    val (major, minor, patch) = info.api_version
    print "Vulkan API Version: {major}.{minor}.{patch}"
```

---

## Memory Management

### Basic Allocation

```simple
use std.gpu.*

val gpu = gpu_default()

# Allocate raw bytes
val buffer = gpu_alloc(gpu, 1024)  # 1024 bytes
if buffer.is_valid:
    print "Allocated {buffer.len()} bytes"

# Always free when done
gpu_free(buffer)
```

### Typed Arrays

```simple
use std.gpu.*

val gpu = gpu_default()

# Allocate typed arrays
val floats = gpu_alloc_f32(gpu, 1000)   # 1000 floats (4000 bytes)
val doubles = gpu_alloc_f64(gpu, 500)   # 500 doubles (4000 bytes)
val ints = gpu_alloc_i32(gpu, 2000)     # 2000 ints (8000 bytes)

# Check allocation
if floats.valid():
    print "Allocated {floats.count()} floats ({floats.size_bytes()} bytes)"

# Cleanup
gpu_array_free(floats)
gpu_array_free(doubles)
gpu_array_free(ints)
```

### Data Transfer

```simple
use std.gpu.*

val gpu = gpu_default()
val buffer = gpu_alloc(gpu, 16)

# Host to device
val host_data: [u8] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
gpu_copy_to(buffer, host_data)

# Device to host
var result: [u8] = []
for i in 0..16:
    result.push(0)
gpu_copy_from(result, buffer)

# Device to device
val buffer2 = gpu_alloc(gpu, 16)
gpu_copy_buffer(buffer2, buffer, 16)

gpu_free(buffer)
gpu_free(buffer2)
```

### Memory Pool

For many small allocations, use a memory pool:

```simple
use std.gpu.*

val gpu = gpu_default()
var pool = gpu_pool_create(gpu, 1024 * 1024)  # 1 MB chunks

# Allocate from pool (faster than individual allocations)
val buf1 = pool.alloc(256)
val buf2 = pool.alloc(512)
val buf3 = pool.alloc(128)

# Release all at once
pool.clear()
```

---

## Writing Kernels

### Kernel Syntax

```simple
# Define a GPU kernel function
kernel fn vector_add(a: [f32]_gpu, b: [f32]_gpu, c: [f32]_gpu, n: i64):
    val idx = gpu_global_id(0)
    if idx < n:
        c[idx] = a[idx] + b[idx]
```

### GPU Intrinsics

| Intrinsic | Description | Arguments |
|-----------|-------------|-----------|
| `gpu_global_id(dim)` | Global thread ID | dim: 0, 1, or 2 |
| `gpu_local_id(dim)` | Local thread ID within block | dim: 0, 1, or 2 |
| `gpu_block_id(dim)` | Block/workgroup ID | dim: 0, 1, or 2 |
| `gpu_block_dim(dim)` | Block dimensions | dim: 0, 1, or 2 |
| `gpu_grid_dim(dim)` | Grid dimensions | dim: 0, 1, or 2 |
| `gpu_sync()` | Synchronize threads | none |
| `gpu_barrier()` | Thread barrier | none |
| `gpu_mem_fence()` | Memory fence | none |

### Shared Memory

```simple
kernel fn reduce_sum(input: [f32]_gpu, output: [f32]_gpu, n: i64):
    shared val cache: [f32; 256]  # Shared memory declaration

    val tid = gpu_local_id(0)
    val gid = gpu_global_id(0)

    # Load to shared memory
    cache[tid] = if gid < n: input[gid] else: 0.0
    gpu_sync()

    # Parallel reduction
    var stride = 128
    while stride > 0:
        if tid < stride:
            cache[tid] = cache[tid] + cache[tid + stride]
        gpu_sync()
        stride = stride / 2

    # Write result
    if tid == 0:
        output[gpu_block_id(0)] = cache[0]
```

### Atomic Operations

```simple
kernel fn histogram(data: [i32]_gpu, bins: [i32]_gpu, n: i64):
    val idx = gpu_global_id(0)
    if idx < n:
        val bin = data[idx]
        gpu_atomic_add(&bins[bin], 1)
```

Available atomic operations:
- `gpu_atomic_add(ptr, val)` - Atomic add
- `gpu_atomic_sub(ptr, val)` - Atomic subtract
- `gpu_atomic_min(ptr, val)` - Atomic minimum
- `gpu_atomic_max(ptr, val)` - Atomic maximum
- `gpu_atomic_and(ptr, val)` - Atomic bitwise AND
- `gpu_atomic_or(ptr, val)` - Atomic bitwise OR
- `gpu_atomic_xor(ptr, val)` - Atomic bitwise XOR
- `gpu_atomic_exchange(ptr, val)` - Atomic exchange
- `gpu_atomic_cas(ptr, expected, desired)` - Compare-and-swap

---

## Kernel Execution

### Launch Configuration

```simple
use std.gpu.*
use std.gpu.kernels.*

# 1D launch
val launch_1d = launch_1d(total_elements: 10000, block_size: 256)
# Grid: (40, 1, 1), Block: (256, 1, 1)

# 2D launch
val launch_2d = launch_2d(width: 1920, height: 1080, block_x: 16, block_y: 16)
# Grid: (120, 68, 1), Block: (16, 16, 1)

# Custom launch
val custom = KernelLaunch(
    grid: (100, 100, 1),
    block: (32, 32, 1),
    shared_mem: 4096
)
```

### Running Kernels

```simple
use std.gpu.*

val gpu = gpu_default()

# Using built-in kernels
val a = gpu_alloc(gpu, 1024)
val b = gpu_alloc(gpu, 1024)
val c = gpu_alloc(gpu, 1024)

# Initialize a and b...
gpu_copy_to(a, data_a)
gpu_copy_to(b, data_b)

# Run vector add
val success = gpu_vector_add(gpu, a, b, c, 256)

# Synchronize and read results
gpu.sync()
gpu_copy_from(result, c)

gpu_free(a)
gpu_free(b)
gpu_free(c)
```

### Custom Kernel Compilation

```simple
use std.gpu.kernels.*

# Compile CUDA kernel from PTX
val cuda_kernel = kernel_compile_cuda(my_ptx_source, "my_kernel")

# Compile Vulkan kernel from GLSL
val vulkan_kernel = kernel_compile_vulkan(my_glsl_source, "main")

# Run the kernel
val launch = launch_1d(n, 256)
kernel_run(cuda_kernel, launch, [buffer_a, buffer_b, buffer_c])

# Cleanup
kernel_destroy(cuda_kernel)
```

---

## Synchronization

### Device Synchronization

```simple
use std.gpu.*

val gpu = gpu_default()

# Wait for all operations on this device
gpu.sync()

# Wait for all devices
gpu_sync_all()
```

### CUDA Streams

```simple
use std.gpu.*

val gpu = gpu_cuda(0)

# Create stream for async operations
val stream = gpu_stream_create(gpu)

# ... launch kernels on stream ...

# Wait for stream to complete
gpu_stream_sync(stream)

# Cleanup
gpu_stream_destroy(stream)
```

### Scoped Synchronization

```simple
use std.gpu.sync.*

val gpu = gpu_default()

# Execute with guaranteed sync before and after
with_gpu_sync(gpu, fn():
    # GPU operations here
    gpu_vector_add(gpu, a, b, c, n)
)

# Execute on a specific device
with_device(gpu, fn():
    # Operations on this device
    pass
)
```

---

## Performance Optimization

### Memory Coalescing

Access memory in coalesced patterns for best performance:

```simple
# Good: Coalesced access (threads access consecutive addresses)
kernel fn coalesced(data: [f32]_gpu):
    val idx = gpu_global_id(0)
    data[idx] = data[idx] * 2.0  # Thread 0 -> data[0], Thread 1 -> data[1], etc.

# Bad: Strided access (poor memory coalescing)
kernel fn strided(data: [f32]_gpu, stride: i64):
    val idx = gpu_global_id(0)
    data[idx * stride] = 0.0  # Scattered access pattern
```

### Occupancy

Choose block sizes that maximize GPU occupancy:

```simple
# Common good block sizes:
# - 256 threads (1D): Good default
# - 128 threads (1D): Better for register-heavy kernels
# - 16x16 (2D): Good for image processing
# - 8x8x8 (3D): Good for volume processing

val launch = launch_1d(n, 256)  # 256 is usually a good choice
```

### Shared Memory Usage

Use shared memory to reduce global memory access:

```simple
kernel fn matrix_mul_tiled(A: [f32]_gpu, B: [f32]_gpu, C: [f32]_gpu, N: i64):
    shared val As: [f32; 16 * 16]
    shared val Bs: [f32; 16 * 16]

    val tx = gpu_local_id(0)
    val ty = gpu_local_id(1)
    val row = gpu_block_id(1) * 16 + ty
    val col = gpu_block_id(0) * 16 + tx

    var sum: f32 = 0.0

    # Tile loop
    for tile in 0..(N / 16):
        # Load tile to shared memory
        As[ty * 16 + tx] = A[row * N + tile * 16 + tx]
        Bs[ty * 16 + tx] = B[(tile * 16 + ty) * N + col]
        gpu_sync()

        # Compute partial sum
        for k in 0..16:
            sum = sum + As[ty * 16 + k] * Bs[k * 16 + tx]
        gpu_sync()

    C[row * N + col] = sum
```

### Minimize Transfers

Batch operations to minimize host-device transfers:

```simple
# Bad: Many small transfers
for i in 0..1000:
    gpu_copy_to(buffer, small_data[i])
    run_kernel(buffer)
    gpu_copy_from(result[i], buffer)

# Good: Batch transfers
gpu_copy_to(buffer, all_data)  # One large transfer
for i in 0..1000:
    run_kernel(buffer, offset: i * chunk_size)
gpu_copy_from(all_results, buffer)  # One large transfer
```

### Async Operations

Use streams for overlapping computation and transfer:

```simple
use std.gpu.*

val stream1 = gpu_stream_create(gpu)
val stream2 = gpu_stream_create(gpu)

# Overlap transfer and compute
# Stream 1: Transfer batch A, compute batch A
# Stream 2: Transfer batch B, compute batch B
# While stream 1 computes, stream 2 transfers (and vice versa)
```

---

## Error Handling

### Checking Operations

```simple
use std.gpu.*

val gpu = gpu_default()
val buffer = gpu_alloc(gpu, 1024)

if not buffer.is_valid:
    print "Allocation failed!"
    print "Error: {cuda_last_error()}"  # or vulkan_last_error()
```

### CUDA Errors

```simple
use io.cuda_ffi.*

# Get and clear last error
val error = cuda_last_error()
if error.len() > 0 and error != "Success":
    print "CUDA Error: {error}"

# Peek without clearing
val peek = cuda_peek_error()
```

### Vulkan Errors

```simple
use io.vulkan_ffi.*

val error = vulkan_last_error()
if error.len() > 0:
    print "Vulkan Error: {error}"
```

---

## Examples

### SAXPY (Single-precision A*X Plus Y)

```simple
use std.gpu.*

fn saxpy_example():
    val gpu = gpu_default()
    if not gpu.is_valid():
        print "No GPU available"
        return

    val n: i64 = 1000000
    val a: f32 = 2.0

    # Allocate GPU buffers
    val x = gpu_alloc_f32(gpu, n)
    val y = gpu_alloc_f32(gpu, n)

    # Initialize (in real code, copy from host)
    # ...

    # Run SAXPY: y = a * x + y
    gpu_scalar_mul(gpu, x.buffer, a, n)
    gpu_vector_add(gpu, x.buffer, y.buffer, y.buffer, n)

    gpu.sync()

    # Read results back
    # ...

    gpu_array_free(x)
    gpu_array_free(y)
```

### Matrix Multiplication

```simple
use std.gpu.*
use std.gpu.kernels.*

fn matmul_example():
    val gpu = gpu_default()
    val N: i64 = 1024
    val size = N * N * 4  # f32

    val A = gpu_alloc(gpu, size)
    val B = gpu_alloc(gpu, size)
    val C = gpu_alloc(gpu, size)

    # Load matrices...

    # Compile and run custom kernel
    val kernel = kernel_compile_cuda(MATMUL_PTX, "matmul")
    val launch = launch_2d(N, N, 16, 16)
    kernel_run(kernel, launch, [A, B, C])

    gpu.sync()
    kernel_destroy(kernel)

    gpu_free(A)
    gpu_free(B)
    gpu_free(C)
```

### Image Processing

```simple
use std.gpu.*

fn grayscale_example():
    val gpu = gpu_default()
    val width: i64 = 1920
    val height: i64 = 1080

    val rgb = gpu_alloc(gpu, width * height * 3)
    val gray = gpu_alloc(gpu, width * height)

    # Load image...

    # Run grayscale kernel
    val kernel = kernel_compile_vulkan(GRAYSCALE_GLSL, "main")
    val launch = launch_2d(width, height, 16, 16)
    kernel_run(kernel, launch, [rgb, gray])

    vulkan_wait_idle()
    kernel_destroy(kernel)

    # Read result...

    gpu_free(rgb)
    gpu_free(gray)
```

---

## See Also

- [GPU API Reference](../api/gpu_api.md) - Complete API documentation
- [GPU Backend Design](../design/gpu_backend_design.md) - Architecture details
- [Dimension Errors Guide](dimension_errors_guide.md) - Debugging dimension mismatches
