# CUDA Unified Interface Implementation Plan

**Date:** 2026-02-09
**Goal:** Implement comprehensive CUDA support with streams, async operations, and unified API
**Status:** Planning
**Based On:**
- `doc/plan/UNIFIED_GPU_INTERFACE_PLAN.md`
- `doc/guide/gpu_configuration.md`
- `doc/api/gpu_api.md`

---

## Executive Summary

This plan builds on the existing PyTorch FFI work to create a **unified, easy-to-use CUDA interface** with:

1. **Context-based API** - `ctx.alloc()`, `ctx.launch()` instead of low-level handles
2. **CUDA Streams** - Async execution with overlap
3. **Config file support** - `dl.config.sdn` for easy device selection
4. **Fallback chain** - PyTorch → Pure CUDA → Vulkan → CPU
5. **Zero-copy interop** - DLPack for PyTorch/JAX/TensorFlow

**Key Insight:** The "easier way" is the **context-based unified API** where users don't manage raw handles - they work with a `GpuContext` that handles device selection, memory, and streams automatically.

---

## Current Status

### ✅ Already Complete

1. **Device Management** (Basic)
   - `Device` enum with `CPU`, `CUDA(id)`
   - Config file loading (`dl.config.sdn`)
   - Device selection via `dl.device(Device.CUDA(1))`

2. **PyTorch FFI** (Device Layer Only)
   - Tier 1: C++ bridge with real PyTorch calls
   - Tier 2: Rust wrapper
   - Tier 3: SFFI bindings
   - Tier 4: Simple API with `.cuda(id)`, `.cpu()`, `.is_cuda()`
   - Functions: zeros, ones, randn, add, mul, matmul, relu, sigmoid, tanh

3. **Configuration System**
   - `load_local_config()` - Load from `./dl.config.sdn`
   - Global `dl` instance with defaults
   - Helper functions: `cuda()`, `cpu()`, `gpu()`

### ⚠️ Missing (This Plan)

1. **CUDA Streams** - No async execution
2. **Context API** - Still using raw FFI handles
3. **Memory Management** - No unified alloc/upload/download
4. **Kernel Launch** - No kernel execution (only PyTorch ops)
5. **Synchronization** - No events, fences, barriers
6. **Direct CUDA FFI** - Only through PyTorch (dependency)

---

## The "Easier Way": Context-Based API

### Before (Current PyTorch FFI - Handle-Based)

```simple
use lib.torch.{TorchTensorWrapper, torch_cuda_available}

fn main():
    # Check CUDA
    if not torch_cuda_available():
        print "No CUDA"
        return

    # Create tensors (returns handles)
    val t1 = TorchTensorWrapper.tensor_zeros([1000, 1000])
    val t2 = TorchTensorWrapper.tensor_ones([1000, 1000])

    # Move to GPU (creates new handles)
    val t1_gpu = t1.cuda(1)
    val t2_gpu = t2.cuda(1)

    # Operations (creates more handles)
    val result = t1_gpu.add(t2_gpu.handle)  # Need to pass handle

    # Move back to CPU
    val result_cpu = result.cpu()

    # Manual memory management (drop() called automatically)
```

**Problems:**
- Handle management is manual
- No async operations (everything blocks)
- No stream overlap (compute + transfer)
- PyTorch dependency (can't use pure CUDA)
- Verbose (need to check availability, move devices, etc.)

### After (Unified Context API)

```simple
use std.gpu.{Context, GpuBackend}

fn main():
    # Auto-detect best backend (CUDA on NVIDIA, Vulkan on AMD, CPU fallback)
    val ctx = Context.default()

    # Or explicit:
    # val ctx = Context.new(backend: GpuBackend.Cuda, device: 1)

    # Allocate and upload in one call (async by default)
    val a = ctx.alloc_upload([1.0, 2.0, 3.0, 4.0])
    val b = ctx.alloc_upload([5.0, 6.0, 7.0, 8.0])
    val out = ctx.alloc[f32](4)

    # Launch kernel (async)
    ctx.launch(
        kernel: vector_add,
        global_size: [4],
        local_size: [1],
        args: [a, b, out]
    )

    # Download (blocks until kernel completes)
    val result = out.download()  # [6.0, 8.0, 10.0, 12.0]

    # Memory auto-freed when ctx goes out of scope
```

**Benefits:**
- Single context manages everything
- Backend-agnostic (same code for CUDA/Vulkan/CPU)
- Async by default (no blocking)
- Auto memory management (RAII)
- Concise and clear

---

## Architecture Overview

### Three-Layer Design

```
┌─────────────────────────────────────────────────────────────┐
│ Layer 3: Unified API (std.gpu.*)                           │
│ - Context.new(backend, device)                             │
│ - ctx.alloc[T](count), ctx.alloc_upload(data)             │
│ - ctx.launch(kernel, ...), ctx.sync()                     │
│ - GpuArray[T], GpuStream, GpuEvent                        │
└────────────────┬────────────────────────────────────────────┘
                 │
     ┌───────────┴────────────┐
     ▼                        ▼
┌─────────────────┐     ┌──────────────────┐
│ Layer 2: CUDA   │     │ Layer 2: Vulkan  │
│ - CudaContext   │     │ - VulkanContext  │
│ - cudaMalloc    │     │ - vkCreateBuffer │
│ - cudaLaunch    │     │ - vkCmdDispatch  │
│ - cudaStream    │     │ - VkCommandPool  │
└────────┬────────┘     └─────────┬────────┘
         │                        │
         ▼                        ▼
┌─────────────────┐     ┌──────────────────┐
│ Layer 1: CUDA   │     │ Layer 1: Vulkan  │
│ FFI (io.cuda)   │     │ FFI (io.vulkan)  │
│ - extern fn     │     │ - extern fn      │
│   rt_cuda_*     │     │   rt_vulkan_*    │
└─────────────────┘     └──────────────────┘
```

### Fallback Chain

```
User Code
    ↓
┌─────────────┐
│ Context.new │
└─────────────┘
    ↓
    ├─→ PyTorch available? → Use PyTorch FFI (existing)
    ├─→ CUDA available? → Use Direct CUDA FFI (new)
    ├─→ Vulkan available? → Use Vulkan Compute (planned)
    └─→ CPU fallback → Pure Simple kernels (always works)
```

---

## Implementation Phases

### Phase 1: CUDA Streams (PyTorch Extension) - 2-4 hours

**Goal:** Add stream support to existing PyTorch FFI

**Why First:** Streams are critical for async operations and already have PyTorch C++ API support.

#### Files to Modify

**1. C++ Bridge** (`.build/rust/ffi_torch/src/`)

Add stream types and functions:

```cpp
// bridge.h
struct TorchStream {
#ifdef HAS_TORCH
    c10::Stream inner;
    TorchStream(c10::Stream s);
#else
    TorchStream();
#endif
    ~TorchStream();
};

std::unique_ptr<TorchStream> torch_stream_create(int32_t device_id);
void torch_stream_sync(const TorchStream& s);
std::unique_ptr<TorchTensor> torch_torchtensor_cuda_stream(
    const TorchTensor& h,
    int32_t device_id,
    const TorchStream& stream
);
```

**2. Rust Wrapper** (lib.rs)

Export stream functions:

```rust
#[repr(C)]
pub struct SimpleTorchStream {
    inner: UniquePtr<ffi::TorchStream>,
}

#[no_mangle]
pub extern "C" fn rt_torch_stream_create(device_id: i32) -> *mut SimpleTorchStream {
    let stream = ffi::torch_stream_create(device_id);
    Box::into_raw(Box::new(SimpleTorchStream { inner: stream }))
}

#[no_mangle]
pub extern "C" fn rt_torch_stream_sync(handle: *const SimpleTorchStream) {
    if !handle.is_null() {
        unsafe {
            let s = &*handle;
            ffi::torch_stream_sync(&s.inner);
        }
    }
}
```

**3. FFI Bindings** (src/lib/torch/ffi.spl)

```simple
extern fn rt_torch_stream_create(device_id: i32) -> i64
extern fn rt_torch_stream_sync(handle: i64)
extern fn rt_torch_stream_free(handle: i64)

extern fn rt_torch_torchtensor_cuda_stream(
    handle: i64,
    device_id: i32,
    stream: i64
) -> i64
```

**4. Simple API** (src/lib/torch/mod.spl)

```simple
class TorchStream:
    """CUDA stream for async operations."""
    handle: i64
    owns_handle: bool

    static fn create(device_id: i32) -> TorchStream:
        val handle = rt_torch_stream_create(device_id)
        TorchStream(handle: handle, owns_handle: true)

    fn sync():
        """Wait for all operations in this stream to complete."""
        rt_torch_stream_sync(self.handle)

    fn drop():
        if self.owns_handle:
            rt_torch_stream_free(self.handle)

# Add to TorchTensorWrapper:
fn cuda_stream(device_id: i32, stream: TorchStream) -> TorchTensorWrapper:
    """Move tensor to GPU using specific stream (async)."""
    val result_handle = rt_torch_torchtensor_cuda_stream(
        self.handle,
        device_id,
        stream.handle
    )
    TorchTensorWrapper(handle: result_handle, owns_handle: true)

export TorchStream
```

#### Test Example

```simple
use lib.torch.{TorchTensorWrapper, TorchStream, torch_cuda_available}

fn test_async_streams():
    if not torch_cuda_available():
        print "CUDA not available"
        return

    # Create two streams for parallel execution
    val stream1 = TorchStream.create(1)
    val stream2 = TorchStream.create(1)

    # Create tensors
    val t1 = TorchTensorWrapper.tensor_zeros([1000, 1000])
    val t2 = TorchTensorWrapper.tensor_ones([1000, 1000])

    # Move to GPU on different streams (parallel transfer)
    val gpu1 = t1.cuda_stream(1, stream1)
    val gpu2 = t2.cuda_stream(1, stream2)

    # Operations on each stream (parallel compute)
    val r1 = gpu1.relu()
    val r2 = gpu2.sigmoid()

    # Wait for both streams
    stream1.sync()
    stream2.sync()

    print "Both streams completed"
```

**Estimated Time:** 2-4 hours

---

### Phase 2: Context API Foundation - 3-5 hours

**Goal:** Create unified Context type and basic memory management

#### Files to Create

**1. std/gpu/context.spl** (~300 lines)

```simple
use std.gpu.device.{GpuBackend, Gpu}
use std.gpu.memory.{GpuBuffer, GpuArray}
use lib.torch.{TorchStream}

class Context:
    """Unified GPU context managing device, memory, and streams.

    Automatically selects best available backend and provides
    backend-agnostic API for all operations.
    """

    backend: GpuBackend
    device: Gpu
    default_stream: TorchStream?

    static fn default() -> Context:
        """Auto-detect best backend and device."""
        val backends = detect_backends()
        if backends.contains(GpuBackend.Cuda):
            return Context.new(backend: GpuBackend.Cuda, device: 0)
        elif backends.contains(GpuBackend.Vulkan):
            return Context.new(backend: GpuBackend.Vulkan, device: 0)
        else:
            return Context.new(backend: GpuBackend.None, device: -1)

    static fn new(backend: GpuBackend, device: i32) -> Context:
        """Create context for specific backend and device."""
        val gpu = match backend:
            case GpuBackend.Cuda: gpu_cuda(device)
            case GpuBackend.Vulkan: gpu_vulkan(device)
            case GpuBackend.None: Gpu(backend: GpuBackend.None, device_id: -1, is_initialized: false)

        val stream = match backend:
            case GpuBackend.Cuda: Some(TorchStream.create(device))
            case _: nil

        Context(backend: backend, device: gpu, default_stream: stream)

    # Memory allocation
    fn alloc[T](count: i64) -> GpuArray[T]:
        """Allocate uninitialized array on device."""
        gpu_array_alloc[T](self.device, count, sizeof[T]())

    fn alloc_upload[T](data: [T]) -> GpuArray[T]:
        """Allocate and upload data to device (async)."""
        val arr = self.alloc[T](data.len())
        arr.copy_from_host(data)
        arr

    fn alloc_zeros[T](count: i64) -> GpuArray[T]:
        """Allocate zero-initialized array."""
        val arr = self.alloc[T](count)
        gpu_memset(arr.buffer, 0)
        arr

    # Synchronization
    fn sync():
        """Wait for all operations to complete."""
        match self.default_stream:
            case Some(s): s.sync()
            case nil: self.device.sync()

    # Stream creation
    fn create_stream() -> TorchStream:
        """Create new stream for async operations."""
        match self.backend:
            case GpuBackend.Cuda:
                TorchStream.create(self.device.device_id)
            case _:
                panic("Streams not supported on this backend")

    fn drop():
        """Free all resources."""
        match self.default_stream:
            case Some(s): s.drop()
            case nil: ()

export Context
```

**2. std/gpu/memory.spl** (~200 lines)

```simple
use std.gpu.device.{Gpu, GpuBackend}

class GpuArray[T]:
    """Typed GPU array with automatic memory management."""

    buffer: GpuBuffer
    count: i64
    element_size: i64

    fn copy_from_host(data: [T]) -> bool:
        """Copy data from host to device (async)."""
        val bytes = data.len() * self.element_size
        gpu_copy_to(self.buffer, data.as_bytes())

    fn download() -> [T]:
        """Copy data from device to host (blocks until complete)."""
        var result: [T; self.count]
        gpu_copy_from(result.as_bytes(), self.buffer)
        result

    fn copy_to(other: GpuArray[T]) -> bool:
        """Copy device to device."""
        gpu_copy_buffer(other.buffer, self.buffer, self.size_bytes())

    fn size_bytes() -> i64:
        self.count * self.element_size

    fn drop():
        gpu_array_free[T](self)

export GpuArray
```

**3. std/gpu/device.spl** (~150 lines)

```simple
enum GpuBackend:
    Cuda
    Vulkan
    None

struct Gpu:
    backend: GpuBackend
    device_id: i64
    is_initialized: bool

    fn sync() -> bool:
        match self.backend:
            case GpuBackend.Cuda: cuda_device_sync(self.device_id)
            case GpuBackend.Vulkan: vulkan_device_sync(self.device_id)
            case GpuBackend.None: true

fn detect_backends() -> [GpuBackend]:
    """Detect available GPU backends."""
    var backends: [GpuBackend]

    # Check CUDA (via PyTorch or direct)
    if torch_cuda_available():
        backends.push(GpuBackend.Cuda)

    # Check Vulkan (future)
    # if vulkan_available():
    #     backends.push(GpuBackend.Vulkan)

    # CPU always available
    backends

fn gpu_cuda(device_id: i64) -> Gpu:
    Gpu(backend: GpuBackend.Cuda, device_id: device_id, is_initialized: true)

export GpuBackend, Gpu, detect_backends, gpu_cuda
```

#### Integration with Config System

**Update src/lib/src/dl/config.spl:**

```simple
use std.gpu.{Context, GpuBackend}

fn create_context_from_config() -> Context:
    """Create GPU context from global DL config."""
    match dl.default_device:
        case Device.CPU:
            Context.new(backend: GpuBackend.None, device: -1)
        case Device.CUDA(id):
            Context.new(backend: GpuBackend.Cuda, device: id)

export create_context_from_config
```

**Estimated Time:** 3-5 hours

---

### Phase 3: Async Pipeline (Stream Overlap) - 2-3 hours

**Goal:** Enable compute/transfer overlap with multiple streams

#### Pattern: Producer-Consumer Streams

```simple
use std.gpu.{Context}

fn async_training_loop():
    val ctx = Context.default()

    # Create streams for overlap
    val compute_stream = ctx.create_stream()
    val transfer_stream = ctx.create_stream()

    # Pipeline: upload batch N, compute batch N-1, download batch N-2
    var batch_data = load_batch(0)
    var gpu_batch = ctx.alloc_upload(batch_data)

    for i in 1..num_batches:
        # Stream 1: Upload next batch (async)
        val next_data = load_batch(i)
        val next_gpu = ctx.alloc_upload(next_data)

        # Stream 2: Compute current batch (async, parallel with upload)
        val result = train_step(gpu_batch)

        # Wait for compute to finish, download results
        compute_stream.sync()
        val output = result.download()

        # Move to next iteration
        gpu_batch = next_gpu

    ctx.sync()
```

**Key Functions:**

```simple
# Add to Context
fn launch_async(kernel: fn, args: [GpuArray], stream: TorchStream):
    """Launch kernel on specific stream (non-blocking)."""
    # Implementation uses stream parameter for async execution

fn pipeline(stages: [(fn, TorchStream)]):
    """Execute pipeline of operations on different streams."""
    for (stage_fn, stream) in stages:
        launch_async(stage_fn, stream)
```

**Estimated Time:** 2-3 hours

---

### Phase 4: Direct CUDA FFI (No PyTorch Dependency) - 5-7 hours

**Goal:** Add native CUDA support without requiring PyTorch

**Why:** PyTorch is a 2GB+ dependency. For simple GPU operations, direct CUDA is lighter.

#### Architecture

```
Simple Code
    ↓
std.gpu.Context
    ↓
    ├─→ Has PyTorch? → Use lib.torch.* (existing)
    └─→ Has CUDA? → Use io.cuda.* (new, direct CUDA runtime)
```

#### Files to Create

**1. Rust CUDA FFI Wrapper** (`.build/rust/ffi_cuda/`)

```rust
// lib.rs
use cuda_driver_sys::*;

#[no_mangle]
pub extern "C" fn rt_cuda_init() -> bool {
    unsafe { cuInit(0) == CUDA_SUCCESS }
}

#[no_mangle]
pub extern "C" fn rt_cuda_device_count() -> i32 {
    let mut count: i32 = 0;
    unsafe {
        if cuDeviceGetCount(&mut count) == CUDA_SUCCESS {
            count
        } else {
            0
        }
    }
}

#[no_mangle]
pub extern "C" fn rt_cuda_malloc(size: usize) -> *mut c_void {
    let mut ptr: *mut c_void = std::ptr::null_mut();
    unsafe {
        if cudaMalloc(&mut ptr, size) == cudaSuccess {
            ptr
        } else {
            std::ptr::null_mut()
        }
    }
}

#[no_mangle]
pub extern "C" fn rt_cuda_free(ptr: *mut c_void) {
    unsafe { cudaFree(ptr); }
}

#[no_mangle]
pub extern "C" fn rt_cuda_memcpy_h2d(dst: *mut c_void, src: *const c_void, size: usize) -> bool {
    unsafe {
        cudaMemcpy(dst, src, size, cudaMemcpyHostToDevice) == cudaSuccess
    }
}

#[no_mangle]
pub extern "C" fn rt_cuda_stream_create() -> cudaStream_t {
    let mut stream: cudaStream_t = std::ptr::null_mut();
    unsafe {
        if cudaStreamCreate(&mut stream) == cudaSuccess {
            stream
        } else {
            std::ptr::null_mut()
        }
    }
}

#[no_mangle]
pub extern "C" fn rt_cuda_stream_sync(stream: cudaStream_t) -> bool {
    unsafe { cudaStreamSynchronize(stream) == cudaSuccess }
}
```

**2. Simple FFI Bindings** (src/app/io/cuda_ffi.spl)

```simple
# CUDA Runtime FFI (Two-Tier SFFI Pattern)

# Device Management
extern fn rt_cuda_init() -> bool
extern fn rt_cuda_device_count() -> i32
extern fn rt_cuda_device_get(device_id: i32) -> i64

# Memory Management
extern fn rt_cuda_malloc(size: i64) -> i64
extern fn rt_cuda_free(ptr: i64)
extern fn rt_cuda_memcpy_h2d(dst: i64, src: [u8]) -> bool
extern fn rt_cuda_memcpy_d2h(dst: [u8], src: i64) -> bool

# Stream Management
extern fn rt_cuda_stream_create() -> i64
extern fn rt_cuda_stream_destroy(stream: i64)
extern fn rt_cuda_stream_sync(stream: i64) -> bool

export rt_cuda_*
```

**3. High-Level CUDA API** (src/lib/gpu/cuda.spl)

```simple
use app.io.cuda_ffi.*

class CudaDevice:
    device_id: i32

    static fn count() -> i32:
        rt_cuda_device_count()

    static fn get(device_id: i32) -> CudaDevice:
        CudaDevice(device_id: device_id)

    fn alloc(size: i64) -> CudaBuffer:
        val ptr = rt_cuda_malloc(size)
        CudaBuffer(ptr: ptr, size: size, device: self)

    fn sync() -> bool:
        rt_cuda_device_sync()

class CudaBuffer:
    ptr: i64
    size: i64
    device: CudaDevice

    fn upload(data: [u8]) -> bool:
        rt_cuda_memcpy_h2d(self.ptr, data)

    fn download() -> [u8]:
        var result: [u8; self.size]
        rt_cuda_memcpy_d2h(result, self.ptr)
        result

    fn drop():
        rt_cuda_free(self.ptr)

class CudaStream:
    handle: i64

    static fn create() -> CudaStream:
        val handle = rt_cuda_stream_create()
        CudaStream(handle: handle)

    fn sync() -> bool:
        rt_cuda_stream_sync(self.handle)

    fn drop():
        rt_cuda_stream_destroy(self.handle)

export CudaDevice, CudaBuffer, CudaStream
```

**4. Update Context to Use Direct CUDA**

```simple
# In std/gpu/context.spl
use std.gpu.cuda.{CudaDevice, CudaBuffer, CudaStream}

fn detect_backends() -> [GpuBackend]:
    var backends: [GpuBackend]

    # Check direct CUDA first (lighter than PyTorch)
    if rt_cuda_init() and CudaDevice.count() > 0:
        backends.push(GpuBackend.Cuda)

    # Fallback to PyTorch if available
    elif torch_cuda_available():
        backends.push(GpuBackend.CudaViaT Torch)

    backends
```

**Cargo.toml for CUDA FFI:**

```toml
[dependencies]
cuda-driver-sys = "0.3"
cuda-runtime-sys = "0.3"

[build-dependencies]
bindgen = "0.69"
```

**Estimated Time:** 5-7 hours

---

### Phase 5: Kernel Execution (Optional) - 7-10 hours

**Goal:** Add ability to write and launch custom CUDA kernels

#### Simple Kernel Syntax

```simple
# Define kernel in Simple
#[gpu]
fn vector_add(a: &[f32], b: &[f32], out: &mut [f32]):
    val idx = gpu.global_id()
    if idx < out.len():
        out[idx] = a[idx] + b[idx]

# Launch kernel
fn main():
    val ctx = Context.default()
    val a = ctx.alloc_upload([1.0, 2.0, 3.0, 4.0])
    val b = ctx.alloc_upload([5.0, 6.0, 7.0, 8.0])
    val out = ctx.alloc[f32](4)

    ctx.launch(
        kernel: vector_add,
        global_size: [4],
        local_size: [1],
        args: [a, b, out]
    )

    val result = out.download()
```

**Implementation Requirements:**

1. **Compiler Support** - Compile `#[gpu]` functions to PTX
2. **Runtime Loader** - Load PTX and create kernel objects
3. **Launch API** - `ctx.launch()` with grid/block dimensions
4. **Intrinsics** - `gpu.global_id()`, `gpu.local_id()`, `gpu.barrier()`

**Files:**

- `src/compiler/codegen/cuda/` - CUDA PTX code generator
- `src/compiler/mir_data.spl` - Add GPU MIR instructions
- `src/lib/gpu/kernels.spl` - Kernel compilation and launch

**Estimated Time:** 7-10 hours (complex, involves compiler changes)

---

## Complete Example: Async Training Pipeline

### With New Unified API

```simple
use std.gpu.{Context}
use std.src.dl.config.{load_local_config, create_context_from_config}
use lib.pure.nn.{Sequential, Linear, ReLU}

fn train_model():
    # Load config from dl.config.sdn (device: "cuda:1")
    load_local_config()

    # Create context from config (uses 2nd GPU)
    val ctx = create_context_from_config()

    # Create model
    val model = Sequential.create([
        Linear.create(784, 256),
        ReLU.create(),
        Linear.create(256, 10)
    ])

    # Create streams for async pipeline
    val upload_stream = ctx.create_stream()
    val compute_stream = ctx.create_stream()
    val download_stream = ctx.create_stream()

    # Training loop with 3-way overlap
    for epoch in 0..num_epochs:
        var batch_iter = data_loader.iter()

        # Prime pipeline with first batch
        var current_batch = batch_iter.next()
        var gpu_batch = ctx.alloc_upload(current_batch.data)

        for batch in batch_iter:
            # ASYNC: Upload next batch (stream 1)
            val next_gpu = ctx.alloc_upload(batch.data)

            # ASYNC: Compute current batch (stream 2, parallel with upload)
            val output = model.forward(gpu_batch)
            val loss = compute_loss(output, current_batch.labels)
            model.backward(loss)
            model.update()

            # ASYNC: Download previous results (stream 3)
            val metrics = compute_stream.sync_and_download(output)

            # Log metrics (CPU work while GPU busy)
            log_metrics(epoch, metrics)

            # Next iteration
            current_batch = batch
            gpu_batch = next_gpu

        # Wait for all streams
        ctx.sync()

        print "Epoch {epoch} complete"

    # Model stays on GPU, context auto-frees on drop

fn main():
    train_model()
```

**Key Features:**
- ✅ Config file support (`dl.config.sdn`)
- ✅ Auto device selection from config
- ✅ CUDA streams for async pipeline
- ✅ 3-way overlap (upload, compute, download)
- ✅ Automatic memory management
- ✅ Backend-agnostic (works on CUDA/Vulkan/CPU)

---

## Timeline Summary

| Phase | Description | Time | Status |
|-------|-------------|------|--------|
| 0 | Device management (PyTorch FFI) | Done | ✅ Complete |
| 1 | CUDA streams (PyTorch extension) | 2-4h | 📋 Next |
| 2 | Context API foundation | 3-5h | 📋 Next |
| 3 | Async pipeline (stream overlap) | 2-3h | 📋 Next |
| 4 | Direct CUDA FFI (optional) | 5-7h | 📋 Optional |
| 5 | Kernel execution (optional) | 7-10h | 📋 Optional |

**Critical Path (Phases 1-3):** 7-12 hours
**Full Implementation (Phases 1-5):** 19-29 hours

---

## Success Criteria

### Phase 1 (Streams)
- [ ] Create CUDA streams
- [ ] Async tensor transfers
- [ ] Stream synchronization
- [ ] Multi-stream example works

### Phase 2 (Context API)
- [ ] `Context.default()` auto-detects GPU
- [ ] `ctx.alloc()`, `ctx.alloc_upload()` work
- [ ] Config file integration works
- [ ] Memory auto-freed on drop

### Phase 3 (Async Pipeline)
- [ ] Upload/compute overlap
- [ ] 3-way pipeline (upload/compute/download)
- [ ] Performance improvement over sequential
- [ ] Training loop example works

### Phase 4 (Direct CUDA - Optional)
- [ ] CUDA runtime FFI works
- [ ] No PyTorch dependency
- [ ] Memory allocation via native CUDA
- [ ] Streams via native CUDA

### Phase 5 (Kernels - Optional)
- [ ] `#[gpu]` attribute compiles to PTX
- [ ] `ctx.launch()` executes kernels
- [ ] Custom kernels work
- [ ] Intrinsics (`gpu.global_id()`) work

---

## Dependencies

### Required Now
- ✅ PyTorch C++ (libtorch) - Already required
- ✅ CUDA Toolkit - Already required

### Required for Phase 4
- CUDA Driver API (cuda-driver-sys crate)
- CUDA Runtime API (cuda-runtime-sys crate)

### Optional
- Vulkan SDK (for Vulkan backend)
- SPIR-V tools (for Vulkan compute)

---

## Migration Path

### Step 1: Keep PyTorch API (Backward Compatible)

Old code continues to work:

```simple
use lib.torch.{TorchTensorWrapper}

val t = TorchTensorWrapper.tensor_zeros([100, 100])
val gpu = t.cuda(1)
```

### Step 2: New Code Uses Context API

New code is simpler:

```simple
use std.gpu.{Context}

val ctx = Context.default()
val t = ctx.alloc_zeros[f32](100 * 100)
```

### Step 3: Eventually Deprecate Low-Level PyTorch API

After context API is stable, mark old API as deprecated:

```simple
#[deprecated("Use std.gpu.Context instead")]
fn cuda(device_id: i32) -> TorchTensorWrapper
```

---

## Next Steps

1. **Review Plan** - Get user approval
2. **Phase 1: Streams** - Extend PyTorch FFI with stream support
3. **Phase 2: Context** - Implement unified Context API
4. **Phase 3: Async** - Add async pipeline support
5. **Test & Document** - Create examples and tests
6. **(Optional) Phase 4** - Add direct CUDA FFI
7. **(Optional) Phase 5** - Add kernel execution

---

## Questions for User

1. **Priority:** Do you want Phases 1-3 only (context API + streams), or also Phase 4 (direct CUDA)?
2. **Timeline:** Should we implement all critical phases (1-3) now, or do Phase 1 first and test?
3. **Kernel Support:** Is custom kernel execution (Phase 5) needed now, or can it wait?
4. **Config Integration:** Should the context auto-load from `dl.config.sdn`, or explicit creation only?

---

## Related Documents

- `doc/plan/UNIFIED_GPU_INTERFACE_PLAN.md` - Full unified API spec
- `doc/guide/gpu_configuration.md` - Config file guide
- `doc/api/gpu_api.md` - Complete API reference
- `doc/design/gpu_backend_design.md` - Backend architecture
- `doc/report/pytorch_ffi_device_management_2026-02-09.md` - Current device implementation
