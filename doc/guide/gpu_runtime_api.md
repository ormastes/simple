# GPU Runtime API - Programming Before Compiler

**Use GPU now, without waiting for compiler!**

This guide shows how to write GPU programs using the **runtime-compatible API** that works with the Simple interpreter today.

---

## Quick Start (Works Now!)

```simple
use std.gpu_runtime.{gpu_available, gpu_alloc_zeros, gpu_tensor_is_cuda}

fn main():
    if not gpu_available():
        print "No GPU available"
        return

    # Allocate 1000x1000 matrix on GPU
    val tensor = gpu_alloc_zeros(1000, 1000, use_gpu: true, device_id: 0)

    print "Allocated on GPU: {gpu_tensor_is_cuda(tensor)}"
```

**Run:**
```bash
bin/simple examples/gpu/runtime_example.spl
```

---

## API Overview

### Detection Functions

| Function | Returns | Description |
|----------|---------|-------------|
| `gpu_available()` | `bool` | Check if GPU is available |
| `gpu_backend_name()` | `text` | Get backend name ("CUDA" or "CPU") |
| `gpu_device_count()` | `i32` | Number of GPUs |
| `gpu_ctx_info()` | - | Print GPU information |

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
| `gpu_alloc_zeros(rows, cols, use_gpu, device)` | `i64` | Alloc zeros (CPU or GPU) |
| `gpu_alloc_ones(rows, cols, use_gpu, device)` | `i64` | Alloc ones (CPU or GPU) |
| `gpu_ctx_alloc_zeros(rows, cols, device)` | `i64` | Alloc zeros on GPU |
| `gpu_ctx_alloc_ones(rows, cols, device)` | `i64` | Alloc ones on GPU |

### Stream Operations

| Function | Returns | Description |
|----------|---------|-------------|
| `gpu_stream_create(device)` | `i64` | Create async stream |
| `gpu_stream_sync(handle)` | - | Wait for stream |
| `gpu_stream_query(handle)` | `bool` | Check if complete |
| `gpu_async_upload_batch(...)` | `i64` | Async upload |
| `gpu_async_wait(handle)` | - | Wait for async ops |

---

## Pattern 1: Basic GPU Usage

```simple
use std.gpu_runtime.{gpu_available, gpu_alloc_zeros, gpu_tensor_numel}

fn process_on_gpu():
    if not gpu_available():
        print "No GPU, using CPU"
        return

    # Allocate on GPU 0
    val data = gpu_alloc_zeros(100, 100, use_gpu: true, device_id: 0)

    print "Allocated {gpu_tensor_numel(data)} elements on GPU"

    # Use data...
```

---

## Pattern 2: Async Streams

```simple
use std.gpu_runtime.{gpu_stream_create, gpu_async_upload_batch, gpu_stream_sync}

fn async_processing():
    val stream = gpu_stream_create(0)

    # Queue uploads (async)
    val batch1 = gpu_async_upload_batch(10, 10, device_id: 0, stream_handle: stream)
    val batch2 = gpu_async_upload_batch(10, 10, device_id: 0, stream_handle: stream)
    val batch3 = gpu_async_upload_batch(10, 10, device_id: 0, stream_handle: stream)

    # Do other work while uploads happen...

    # Wait for all uploads
    gpu_stream_sync(stream)
    print "All uploads complete"
```

---

## Pattern 3: Training Loop

```simple
use std.gpu_runtime.{gpu_stream_create, gpu_async_upload_batch, gpu_stream_sync}

fn train(num_epochs: i64, num_batches: i64):
    val stream = gpu_stream_create(0)

    for epoch in 0..num_epochs:
        print "Epoch {epoch + 1}"

        for batch_idx in 0..num_batches:
            # Upload batch (async)
            val batch = gpu_async_upload_batch(
                64, 64,  # 64x64 matrix
                device_id: 0,
                stream_handle: stream
            )

            # Train on GPU (forward, backward, optimize)
            # ...

            # Wait for this batch
            gpu_stream_sync(stream)

            print "  Batch {batch_idx + 1} done"
```

---

## Pattern 4: Multi-GPU

```simple
use std.gpu_runtime.{gpu_device_count, gpu_alloc_zeros}

fn multi_gpu_processing():
    val num_gpus = gpu_device_count()
    print "Using {num_gpus} GPUs"

    # Allocate on different GPUs
    val gpu0_data = gpu_alloc_zeros(100, 100, use_gpu: true, device_id: 0)
    val gpu1_data = gpu_alloc_zeros(100, 100, use_gpu: true, device_id: 1)

    # Process in parallel...
```

---

## Comparison: Runtime vs Full API

### Runtime API (Works Today)

```simple
use std.gpu_runtime.{gpu_alloc_zeros, gpu_tensor_is_cuda}

val tensor = gpu_alloc_zeros(100, 100, use_gpu: true, device_id: 0)
val is_gpu = gpu_tensor_is_cuda(tensor)
```

**Pros:**
- ✅ Works with runtime interpreter (no compiler)
- ✅ Can program GPU today
- ✅ Simpler syntax (no classes)

**Cons:**
- ❌ Handle-based (less ergonomic)
- ❌ No type-safe generics
- ❌ No RAII (manual cleanup)
- ❌ Limited features

---

### Full API (Requires Compiler)

```simple
use std.gpu.{Context}

val ctx = Context.default()
val arr = ctx.alloc_zeros[f32](100 * 100)
# Automatic cleanup when arr goes out of scope
```

**Pros:**
- ✅ Type-safe generics (`GpuArray[f32]`)
- ✅ RAII (automatic cleanup)
- ✅ Ergonomic API
- ✅ Backend abstraction
- ✅ Config integration

**Cons:**
- ❌ Requires full compiler (not yet ready)
- ❌ More complex syntax

---

## Migration Path

**Today:** Use runtime API
```simple
use std.gpu_runtime.{gpu_alloc_zeros}
val handle = gpu_alloc_zeros(100, 100, true, 0)
```

**When Compiler Ready:** Migrate to full API
```simple
use std.gpu.{Context}
val ctx = Context.default()
val arr = ctx.alloc_zeros[f32](100 * 100)
```

**Migration is straightforward:**
- Replace handle functions with Context methods
- Add type parameters where needed
- Remove manual cleanup (RAII handles it)

---

## Limitations (Runtime API)

### No Separate impl Blocks

**Don't Use:**
```simple
struct Foo:
    x: i32

impl Foo:  # ❌ Runtime parser error
    fn method():
        ()
```

**Use Instead:**
```simple
# Functions only (no structs with impl)
fn foo_method(x: i32):
    ()
```

---

### No Complex Generics

**Don't Use:**
```simple
class GpuArray[T]:  # ❌ May not work in runtime
    data: [T]
```

**Use Instead:**
```simple
# Handle-based approach
fn gpu_alloc_zeros(rows: i64, cols: i64, ...) -> i64:
    # Returns handle (i64)
```

---

### Handle-Based Memory

**Runtime API uses handles (i64):**
```simple
val handle = gpu_alloc_zeros(...)  # Returns i64 handle
val elements = gpu_tensor_numel(handle)  # Pass handle
```

**You're responsible for:**
- Tracking handles
- Not using invalid handles
- Cleanup (if needed)

---

## Examples

### Example 1: Simple Matrix Allocation

```simple
use std.gpu_runtime.{gpu_available, gpu_alloc_zeros, gpu_tensor_is_cuda, gpu_tensor_numel}

fn main():
    if not gpu_available():
        print "No GPU available"
        return

    # Allocate 1000x1000 matrix on GPU 0
    val matrix = gpu_alloc_zeros(1000, 1000, use_gpu: true, device_id: 0)

    print "Matrix elements: {gpu_tensor_numel(matrix)}"
    print "On GPU: {gpu_tensor_is_cuda(matrix)}"
    print "✓ Success"
```

---

### Example 2: Async Batch Processing

```simple
use std.gpu_runtime.{gpu_stream_create, gpu_async_upload_batch, gpu_stream_sync}

fn process_batches(num_batches: i64):
    val stream = gpu_stream_create(0)

    for i in 0..num_batches:
        # Upload batch (async, non-blocking)
        val batch = gpu_async_upload_batch(
            32, 32,
            device_id: 0,
            stream_handle: stream
        )

        # Do other work here (parallel with upload)...

        # Process batch on GPU
        # ... (forward pass, etc.)

        # Wait for this batch to finish
        gpu_stream_sync(stream)

        print "Batch {i + 1} complete"
```

---

### Example 3: Check GPU Info

```simple
use std.gpu_runtime.{gpu_ctx_info}

fn main():
    gpu_ctx_info()
```

**Output:**
```
GPU Backend: CUDA
CUDA Available: true
Device Count: 1
Status: Ready
```

---

## Running Examples

```bash
# Basic example
bin/simple examples/gpu/runtime_example.spl

# Your own code
bin/simple your_gpu_program.spl
```

---

## FAQ

### Q: Why two APIs (runtime vs full)?

**A:** The full API requires the compiler (not ready yet). The runtime API works **today** with the interpreter, letting you program GPU immediately.

---

### Q: Will runtime API be deprecated?

**A:** When the compiler is ready, the full API will be preferred. But the runtime API will continue to work for simple cases.

---

### Q: Can I mix both APIs?

**A:** No, choose one:
- Runtime API: `use std.gpu_runtime.*`
- Full API: `use std.gpu.*` (compiler required)

---

### Q: What if I don't have a GPU?

**A:** The API detects this and falls back to CPU automatically:
```simple
if not gpu_available():
    print "Using CPU fallback"
```

---

### Q: Does this work on all platforms?

**A:** Currently CUDA only (NVIDIA GPUs on Linux). Future: Vulkan (cross-platform), DirectML (Windows), Metal (macOS).

---

## Summary

**Use `std.gpu_runtime` to program GPU today:**

```simple
use std.gpu_runtime.{gpu_available, gpu_alloc_zeros, gpu_stream_create, gpu_stream_sync}

fn main():
    if gpu_available():
        val stream = gpu_stream_create(0)
        val data = gpu_alloc_zeros(100, 100, true, 0)
        gpu_stream_sync(stream)
        print "GPU programming works!"
```

**No compiler needed. Start programming GPU now!** 🚀

---

## Related Documentation

- Full API (compiler): `doc/guide/gpu_quick_start.md`
- Implementation details: `doc/report/gpu_unified_interface_complete_2026-02-09.md`
- Examples: `examples/gpu/runtime_example.spl`
- API reference: This document
