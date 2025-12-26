# Vulkan FFI API Reference

**Version:** 1.0
**Date:** 2025-12-26
**Status:** Phase 3 Complete - All Functions Implemented

## Overview

This document provides the complete API reference for the Vulkan backend FFI (Foreign Function Interface) layer. These functions bridge the Simple language runtime with the Vulkan GPU compute backend.

All functions use a handle-based API with u64 handles for resource management, ensuring thread-safety and memory safety. Functions return i32 status codes (0 = success, negative = error) or u64 handles.

## Table of Contents

1. [System Functions](#system-functions)
2. [Device Management](#device-management)
3. [Buffer Management](#buffer-management)
4. [Kernel Management](#kernel-management)
5. [Error Codes](#error-codes)
6. [Type Reference](#type-reference)
7. [Usage Examples](#usage-examples)
8. [Thread Safety](#thread-safety)

---

## System Functions

### `rt_vk_available`

Check if Vulkan is available on the system.

**Signature:**
```c
extern "C" i32 rt_vk_available();
```

**Parameters:** None

**Returns:**
- `1` - Vulkan is available and functional
- `0` - Vulkan is not available (missing drivers, no compatible GPU)

**Example:**
```simple
if !rt_vk_available():
    println("Vulkan not available, using CPU fallback")
    return
```

**Notes:**
- Always call this before attempting to create devices
- Checks for compatible Vulkan drivers and GPU devices
- Returns immediately, does not create any resources

---

## Device Management

### `rt_vk_device_create`

Create a Vulkan device context.

**Signature:**
```c
extern "C" u64 rt_vk_device_create();
```

**Parameters:** None

**Returns:**
- `u64` device handle (non-zero on success, 0 on failure)

**Example:**
```simple
device = rt_vk_device_create()
if device == 0:
    error("Failed to create Vulkan device")
```

**Notes:**
- Automatically selects the best available GPU (discrete > integrated)
- Creates compute and transfer queues
- Enables validation layers in debug builds
- Device must be freed with `rt_vk_device_free` when done

**Performance:** ~10-50ms (first call initializes Vulkan instance)

---

### `rt_vk_device_free`

Destroy a Vulkan device and release all associated resources.

**Signature:**
```c
extern "C" i32 rt_vk_device_free(u64 device_handle);
```

**Parameters:**
- `device_handle` - Device handle from `rt_vk_device_create`

**Returns:**
- `0` - Success
- `-1` - Invalid handle

**Example:**
```simple
rt_vk_device_free(device)
```

**Notes:**
- Waits for all pending GPU operations to complete
- Frees all buffers and kernels associated with this device
- Handle becomes invalid after this call
- Safe to call with handle 0 (no-op)

**Performance:** ~1-10ms (depends on pending work)

---

### `rt_vk_device_sync`

Wait for all pending GPU operations to complete.

**Signature:**
```c
extern "C" i32 rt_vk_device_sync(u64 device_handle);
```

**Parameters:**
- `device_handle` - Device handle from `rt_vk_device_create`

**Returns:**
- `0` - Success
- `-1` - Invalid handle
- `-2` - Synchronization error

**Example:**
```simple
rt_vk_kernel_launch(kernel, buffers, 3, 1024, 1, 1, 256, 1, 1)
rt_vk_device_sync(device)  # Wait for kernel to finish
rt_vk_buffer_download(output_buf, output_ptr, size)
```

**Notes:**
- Blocks until all queued work completes
- Required before reading results from GPU
- Automatically called by `rt_vk_device_free`

**Performance:** Depends on queued work (typically <1ms for small kernels)

---

## Buffer Management

### `rt_vk_buffer_alloc`

Allocate a device-local GPU buffer.

**Signature:**
```c
extern "C" u64 rt_vk_buffer_alloc(u64 device_handle, u64 size_bytes);
```

**Parameters:**
- `device_handle` - Device handle from `rt_vk_device_create`
- `size_bytes` - Buffer size in bytes (must be > 0)

**Returns:**
- `u64` buffer handle (non-zero on success, 0 on failure)

**Example:**
```simple
# Allocate 4KB buffer for 1024 f32 values
buffer = rt_vk_buffer_alloc(device, 1024 * 4)
if buffer == 0:
    error("Failed to allocate GPU buffer")
```

**Notes:**
- Buffer is uninitialized (contains garbage data)
- Use `rt_vk_buffer_upload` to copy data to GPU
- Buffer must be freed with `rt_vk_buffer_free`
- Aligned to device requirements automatically

**Performance:** ~100µs (cached allocation pool)

**Limits:**
- Minimum size: 1 byte
- Maximum size: Device-dependent (typically 4GB-16GB)

---

### `rt_vk_buffer_free`

Free a GPU buffer.

**Signature:**
```c
extern "C" i32 rt_vk_buffer_free(u64 buffer_handle);
```

**Parameters:**
- `buffer_handle` - Buffer handle from `rt_vk_buffer_alloc`

**Returns:**
- `0` - Success
- `-1` - Invalid handle

**Example:**
```simple
rt_vk_buffer_free(buffer)
```

**Notes:**
- Does NOT wait for pending operations (call `rt_vk_device_sync` first)
- Safe to call with handle 0 (no-op)
- Handle becomes invalid after this call

**Performance:** ~10µs (returns memory to pool)

---

### `rt_vk_buffer_upload`

Copy data from CPU memory to GPU buffer.

**Signature:**
```c
extern "C" i32 rt_vk_buffer_upload(
    u64 buffer_handle,
    u64 data_ptr,      // *const u8 as u64
    u64 size_bytes
);
```

**Parameters:**
- `buffer_handle` - Destination buffer from `rt_vk_buffer_alloc`
- `data_ptr` - Source pointer (CPU memory) cast to u64
- `size_bytes` - Number of bytes to copy (must be ≤ buffer size)

**Returns:**
- `0` - Success
- `-1` - Invalid buffer handle
- `-2` - Invalid data pointer (null)
- `-3` - Size exceeds buffer capacity

**Example:**
```simple
data = [1.0, 2.0, 3.0, 4.0]  # f32 array
data_ptr = ptr_of(data)
rt_vk_buffer_upload(buffer, data_ptr, 16)  # 4 * sizeof(f32)
```

**Notes:**
- Uses staging buffer + copy command for efficiency
- Asynchronous - returns before transfer completes
- Call `rt_vk_device_sync` before using buffer in kernel

**Performance:** ~1-100µs + (size_bytes / bandwidth)
- Typical bandwidth: 10-20 GB/s

---

### `rt_vk_buffer_download`

Copy data from GPU buffer to CPU memory.

**Signature:**
```c
extern "C" i32 rt_vk_buffer_download(
    u64 buffer_handle,
    u64 data_ptr,      // *mut u8 as u64
    u64 size_bytes
);
```

**Parameters:**
- `buffer_handle` - Source buffer from `rt_vk_buffer_alloc`
- `data_ptr` - Destination pointer (CPU memory) cast to u64
- `size_bytes` - Number of bytes to copy (must be ≤ buffer size)

**Returns:**
- `0` - Success
- `-1` - Invalid buffer handle
- `-2` - Invalid data pointer (null)
- `-3` - Size exceeds buffer capacity

**Example:**
```simple
results = allocate_array(f32, 1024)
rt_vk_device_sync(device)  # Wait for kernel to finish
rt_vk_buffer_download(output_buf, ptr_of(results), 4096)
```

**Notes:**
- Uses staging buffer + copy command for efficiency
- Blocks until transfer completes (includes implicit sync)
- Always call `rt_vk_device_sync` before download

**Performance:** ~1-100µs + (size_bytes / bandwidth)
- Typical bandwidth: 10-20 GB/s

---

## Kernel Management

### `rt_vk_kernel_compile`

Compile SPIR-V bytecode to executable GPU kernel.

**Signature:**
```c
extern "C" u64 rt_vk_kernel_compile(
    u64 device_handle,
    u64 spirv_ptr,     // *const u8 as u64
    u64 spirv_len      // Length in bytes
);
```

**Parameters:**
- `device_handle` - Device handle from `rt_vk_device_create`
- `spirv_ptr` - Pointer to SPIR-V bytecode cast to u64
- `spirv_len` - Length of SPIR-V bytecode in bytes

**Returns:**
- `u64` kernel handle (non-zero on success, 0 on failure)

**Example:**
```simple
# SPIR-V bytecode from compiler
spirv_code = compile_to_spirv(kernel_source)
kernel = rt_vk_kernel_compile(device, ptr_of(spirv_code), len(spirv_code))
if kernel == 0:
    error("Failed to compile kernel")
```

**Notes:**
- Validates SPIR-V structure (magic number, version)
- Creates shader module and compute pipeline
- Uses `spirv_reflect` to extract buffer bindings automatically
- Kernel must be freed with `rt_vk_kernel_free`
- Cached by pipeline cache for faster recompilation

**Performance:** ~1-50ms (first compilation, ~100µs cached)

**Errors:**
- Invalid SPIR-V magic number
- Unsupported SPIR-V version
- Missing entry point
- Invalid descriptor layout

---

### `rt_vk_kernel_free`

Free a compiled GPU kernel.

**Signature:**
```c
extern "C" i32 rt_vk_kernel_free(u64 kernel_handle);
```

**Parameters:**
- `kernel_handle` - Kernel handle from `rt_vk_kernel_compile`

**Returns:**
- `0` - Success
- `-1` - Invalid handle

**Example:**
```simple
rt_vk_kernel_free(kernel)
```

**Notes:**
- Does NOT wait for pending launches (call `rt_vk_device_sync` first)
- Safe to call with handle 0 (no-op)
- Handle becomes invalid after this call

**Performance:** ~10µs

---

### `rt_vk_kernel_launch`

Execute a GPU kernel with 3D work group configuration.

**Signature:**
```c
extern "C" i32 rt_vk_kernel_launch(
    u64 kernel_handle,
    u64 buffers_ptr,   // *const u64 as u64 (array of buffer handles)
    u64 buffer_count,
    i32 global_size_x,
    i32 global_size_y,
    i32 global_size_z,
    i32 local_size_x,
    i32 local_size_y,
    i32 local_size_z
);
```

**Parameters:**
- `kernel_handle` - Kernel from `rt_vk_kernel_compile`
- `buffers_ptr` - Pointer to array of buffer handles cast to u64
- `buffer_count` - Number of buffers in array
- `global_size_x/y/z` - Total work items per dimension
- `local_size_x/y/z` - Work group size per dimension

**Returns:**
- `0` - Success
- `-1` - Invalid kernel handle
- `-2` - Invalid buffer handle in array
- `-3` - Invalid work group configuration
- `-4` - Buffer count mismatch with kernel requirements

**Example:**
```simple
# Launch 1024x768 kernel with 16x16 work groups
buffers = [input_buf, output_buf]
rt_vk_kernel_launch(
    kernel, ptr_of(buffers), 2,
    1024, 768, 1,  # global size
    16, 16, 1      # local size (work group)
)
```

**Notes:**
- Asynchronous - returns before kernel completes
- Call `rt_vk_device_sync` before reading results
- Global size must be multiple of local size per dimension
- Local size must respect device limits (typically 1024 total)

**Performance:** ~10-100µs launch overhead

**Limits:**
- Max global size: 2^31-1 per dimension
- Max local size: Device-dependent (256-1024 per dimension)
- Max total local size: Device-dependent (typically 1024)

---

### `rt_vk_kernel_launch_1d`

Execute a GPU kernel with 1D work group configuration (convenience wrapper).

**Signature:**
```c
extern "C" i32 rt_vk_kernel_launch_1d(
    u64 kernel_handle,
    u64 buffers_ptr,   // *const u64 as u64
    u64 buffer_count,
    i32 global_size
);
```

**Parameters:**
- `kernel_handle` - Kernel from `rt_vk_kernel_compile`
- `buffers_ptr` - Pointer to array of buffer handles
- `buffer_count` - Number of buffers in array
- `global_size` - Total number of work items

**Returns:** Same as `rt_vk_kernel_launch`

**Example:**
```simple
# Launch simple vector addition with 1024 elements
buffers = [input_a, input_b, output]
rt_vk_kernel_launch_1d(kernel, ptr_of(buffers), 3, 1024)
```

**Notes:**
- Automatically selects optimal local size (typically 256)
- Rounds up global size to multiple of local size
- Equivalent to `rt_vk_kernel_launch(k, b, c, g, 1, 1, auto, 1, 1)`

**Performance:** Same as `rt_vk_kernel_launch`

---

## Error Codes

All functions returning `i32` use the following error code convention:

| Code | Name | Description |
|------|------|-------------|
| `0` | Success | Operation completed successfully |
| `-1` | InvalidHandle | Handle does not exist or has been freed |
| `-2` | InvalidParameter | Null pointer or invalid value |
| `-3` | OutOfBounds | Size exceeds buffer capacity |
| `-4` | ValidationError | SPIR-V validation failed |
| `-5` | OutOfMemory | GPU memory allocation failed |
| `-6` | DeviceError | GPU device error (reset, lost) |
| `-7` | CompilationError | Kernel compilation failed |
| `-8` | ExecutionError | Kernel execution failed |

**Error Handling Example:**
```simple
result = rt_vk_buffer_upload(buffer, data_ptr, size)
match result:
    0 -> continue
    -1 -> error("Invalid buffer handle")
    -2 -> error("Invalid data pointer")
    -3 -> error("Size exceeds buffer capacity")
    _ -> error("Unknown error: " + str(result))
```

---

## Type Reference

### Handle Types

All handles are opaque `u64` values:

```simple
type DeviceHandle = u64   # From rt_vk_device_create
type BufferHandle = u64   # From rt_vk_buffer_alloc
type KernelHandle = u64   # From rt_vk_kernel_compile
```

**Handle Validity:**
- `0` - Invalid/null handle
- Non-zero - Valid handle (until freed)

### Pointer Casting

The FFI layer requires casting pointers to `u64`:

```simple
# Array pointer
data = [1.0, 2.0, 3.0, 4.0]
ptr = ptr_of(data)  # Returns u64

# Buffer handle array
buffers = [buf1, buf2, buf3]
buffers_ptr = ptr_of(buffers)  # Returns u64
```

---

## Usage Examples

### Complete Vector Addition

```simple
import gpu

fn vector_add_gpu(a: []f32, b: []f32) -> []f32:
    # Check Vulkan availability
    if !rt_vk_available():
        error("Vulkan not available")

    # Create device
    device = rt_vk_device_create()
    if device == 0:
        error("Failed to create device")

    # Allocate buffers
    size = len(a) * 4  # sizeof(f32)
    buf_a = rt_vk_buffer_alloc(device, size)
    buf_b = rt_vk_buffer_alloc(device, size)
    buf_out = rt_vk_buffer_alloc(device, size)

    # Upload data
    rt_vk_buffer_upload(buf_a, ptr_of(a), size)
    rt_vk_buffer_upload(buf_b, ptr_of(b), size)

    # Compile kernel
    spirv = compile_kernel(vector_add_source)
    kernel = rt_vk_kernel_compile(device, ptr_of(spirv), len(spirv))

    # Launch kernel
    buffers = [buf_a, buf_b, buf_out]
    rt_vk_kernel_launch_1d(kernel, ptr_of(buffers), 3, len(a))

    # Download results
    result = allocate_array(f32, len(a))
    rt_vk_device_sync(device)
    rt_vk_buffer_download(buf_out, ptr_of(result), size)

    # Cleanup
    rt_vk_buffer_free(buf_a)
    rt_vk_buffer_free(buf_b)
    rt_vk_buffer_free(buf_out)
    rt_vk_kernel_free(kernel)
    rt_vk_device_free(device)

    return result
```

### Resource Management with Context

```simple
class GpuContext:
    device: u64

    fn __init__():
        self.device = rt_vk_device_create()
        if self.device == 0:
            error("Failed to create GPU device")

    fn __del__():
        if self.device != 0:
            rt_vk_device_sync(self.device)
            rt_vk_device_free(self.device)

    fn alloc_buffer(size: u64) -> u64:
        return rt_vk_buffer_alloc(self.device, size)

    fn compile_kernel(spirv: []u8) -> u64:
        return rt_vk_kernel_compile(self.device, ptr_of(spirv), len(spirv))

    fn sync():
        rt_vk_device_sync(self.device)

# Usage
with GpuContext() as ctx:
    buffer = ctx.alloc_buffer(4096)
    # ... use buffer ...
    # Automatic cleanup on exit
```

### Error Handling Pattern

```simple
fn safe_buffer_upload(buffer: u64, data: []f32) -> Result<(), str>:
    ptr = ptr_of(data)
    size = len(data) * 4

    result = rt_vk_buffer_upload(buffer, ptr, size)

    return match result:
        0 -> Ok(())
        -1 -> Err("Invalid buffer handle")
        -2 -> Err("Invalid data pointer")
        -3 -> Err("Data size exceeds buffer capacity")
        _ -> Err("Unknown upload error: " + str(result))
```

---

## Thread Safety

### Thread-Safe Operations

The following operations are thread-safe and can be called from multiple threads:

- ✅ `rt_vk_available()` - Read-only system check
- ✅ `rt_vk_device_create()` - Creates independent device contexts
- ✅ `rt_vk_buffer_alloc()` - Allocates from thread-safe pool
- ✅ `rt_vk_kernel_compile()` - Uses internal locking

### Non-Thread-Safe Operations

The following operations require external synchronization:

- ⚠️ `rt_vk_kernel_launch*()` - Do not launch same kernel from multiple threads
- ⚠️ `rt_vk_buffer_upload/download()` - Do not access same buffer concurrently
- ⚠️ `rt_vk_device_sync()` - Blocks entire device queue

### Recommended Pattern

Use one device per thread, or synchronize access:

```simple
# Option 1: One device per thread (recommended)
thread_local device: u64 = 0

fn get_device() -> u64:
    if device == 0:
        device = rt_vk_device_create()
    return device

# Option 2: Shared device with mutex
import sync

device_lock = Mutex::new(0)

fn with_device<T>(f: fn(u64) -> T) -> T:
    lock = device_lock.lock()
    device = *lock
    if device == 0:
        device = rt_vk_device_create()
        *lock = device
    return f(device)
```

---

## Performance Tips

1. **Batch Operations:** Minimize CPU-GPU round trips by batching kernel launches
2. **Persistent Buffers:** Reuse buffers across multiple kernel launches
3. **Async Transfers:** Upload data while previous kernel is running
4. **Pipeline Cache:** Keep device alive to benefit from shader cache
5. **Work Group Size:** Use 256 for 1D, 16x16 for 2D (matches GPU architecture)

**Example - Batched Processing:**
```simple
# Good: One device, multiple kernels
device = rt_vk_device_create()
for kernel_data in batch:
    launch_kernel(device, kernel_data)
rt_vk_device_sync(device)
rt_vk_device_free(device)

# Bad: Creating device per kernel (100x slower)
for kernel_data in batch:
    device = rt_vk_device_create()
    launch_kernel(device, kernel_data)
    rt_vk_device_free(device)
```

---

## See Also

- [Vulkan Backend User Guide](../guides/vulkan_backend.md) - Getting started and examples
- [Vulkan Backend Architecture](../architecture/vulkan_backend.md) - Implementation details
- [GPU Kernel Specification](../spec/gpu_simd.md) - Language-level GPU features

---

**Last Updated:** 2025-12-26
**Implementation Status:** Phase 3 Complete - All FFI functions implemented and tested
