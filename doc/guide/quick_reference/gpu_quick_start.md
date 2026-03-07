# GPU Quick Start Guide

**Simple Language GPU Interface**

This guide shows how to use the unified GPU interface for accelerated computing.

---

## 5-Minute Quick Start

### 1. Auto-Detect GPU

```simple
use std.gpu.{Context}

fn main():
    val ctx = Context.default()
    print "Using: {ctx.backend_name()} device {ctx.device_id()}"
```

**Output:**
```
Using: CUDA device 0
```

---

### 2. Allocate GPU Memory

```simple
use std.gpu.{Context}

fn main():
    val ctx = Context.default()

    # Allocate 1000 floats (4KB)
    val arr = ctx.alloc_zeros[f32](1000)

    print "Allocated {arr.count} elements"
    print "Size: {arr.size_bytes()} bytes"

    # Memory automatically freed when arr goes out of scope
```

---

### 3. Upload Data to GPU

```simple
use std.gpu.{Context}

fn main():
    val ctx = Context.default()

    # Create data on CPU
    val data = [1.0, 2.0, 3.0, 4.0, 5.0]

    # Upload to GPU
    val gpu_array = ctx.alloc_upload(data)

    print "Uploaded {gpu_array.count} elements to GPU"
```

---

### 4. Use Config File

**Create `dl.config.sdn`:**
```sdn
dl:
  device: "cuda:1"   # Use 2nd GPU
  dtype: "f32"
  backend: "torch"
```

**Simple code:**
```simple
use std.src.dl.config.{load_local_config}
use std.gpu.{create_context_from_config}

fn main():
    load_local_config()
    val ctx = create_context_from_config()

    print "Using GPU {ctx.device_id()} from config"
```

---

## Common Patterns

### Pattern 1: Async Data Transfer

```simple
use std.gpu.{Context}

fn process_batches(batches: [[f32]]):
    val ctx = Context.default()
    val stream = ctx.create_stream()

    for batch in batches:
        # Upload asynchronously
        val gpu_batch = ctx.alloc_upload(batch)

        # Do other work while upload happens...

        # Wait for upload to complete
        stream.sync()

        # Process on GPU
        # ...
```

---

### Pattern 2: Double Buffering

```simple
use std.gpu.{Context}

fn train_epoch(batches: [[f32]]):
    val ctx = Context.default()
    val upload_stream = ctx.create_stream()

    # Prefetch first batch
    var current_batch = ctx.alloc_upload(batches[0])
    upload_stream.sync()

    for i in 1..batches.len():
        # Upload next batch (async)
        val next_batch = ctx.alloc_upload(batches[i])

        # Train on current batch (parallel with upload)
        train_step(current_batch)

        # Wait for upload
        upload_stream.sync()

        # Move to next
        current_batch = next_batch

    # Process final batch
    train_step(current_batch)
```

**Speedup:** 1.3x - 1.8x

---

### Pattern 3: Triple Buffering (Optimal)

```simple
use std.gpu.{Context}

fn process_pipeline(batches: [[f32]]):
    val ctx = Context.default()
    val upload_stream = ctx.create_stream()
    val compute_stream = ctx.create_stream()
    val download_stream = ctx.create_stream()

    # Warm up: load first 2 batches
    var batch_n2 = ctx.alloc_upload(batches[0])
    var batch_n1 = ctx.alloc_upload(batches[1])
    upload_stream.sync()

    # Main loop: 3-way overlap
    for i in 2..batches.len():
        # Stage 1: Upload batch N (async)
        val batch_n = ctx.alloc_upload(batches[i])

        # Stage 2: Compute batch N-1 (parallel)
        compute_on_gpu(batch_n1)

        # Stage 3: Download batch N-2 (parallel)
        val result = batch_n2.download()
        process_result(result)

        # Wait for all stages
        upload_stream.sync()
        compute_stream.sync()
        download_stream.sync()

        # Shift pipeline
        batch_n2 = batch_n1
        batch_n1 = batch_n
```

**Speedup:** 1.5x - 3.0x

---

## Device Selection

### Option 1: Auto-Detect
```simple
val ctx = Context.default()
# Automatically picks CUDA → Vulkan → CPU
```

### Option 2: Explicit Selection
```simple
use std.gpu.{Context, GpuBackend}

# Force CUDA on 3rd GPU
val ctx = Context.new(backend: GpuBackend.Cuda, device: 2)
```

### Option 3: Config File
```simple
use std.src.dl.config.{load_local_config}
use std.gpu.{create_context_from_config}

load_local_config()  # Reads dl.config.sdn
val ctx = create_context_from_config()
```

---

## Memory Management

### RAII (Automatic Cleanup)

```simple
fn process():
    val ctx = Context.default()
    val arr = ctx.alloc_zeros[f32](1000000)  # 4MB

    # Use arr...

    # Automatic cleanup when arr goes out of scope
    # No manual free() needed!
```

### Manual Control

```simple
fn process():
    val ctx = Context.default()
    var arr = ctx.alloc_zeros[f32](1000)

    # Use arr...

    # Explicitly drop
    arr.drop()

    # arr is now invalid, don't use it!
```

---

## Stream Operations

### Create and Sync

```simple
val ctx = Context.default()
val stream = ctx.create_stream()

# Queue operations on stream...

# Wait for all operations to complete
stream.sync()
```

### Query (Non-Blocking)

```simple
val stream = ctx.create_stream()

# Queue operations...

# Check if complete without blocking
var complete = stream.query()
while not complete:
    # Do other work...
    complete = stream.query()

print "Stream completed!"
```

### Multiple Streams

```simple
val ctx = Context.default()

val stream1 = ctx.create_stream()
val stream2 = ctx.create_stream()
val stream3 = ctx.create_stream()

# Operations on different streams run in parallel
val arr1 = ctx.alloc_upload(data1)  # Stream 1
val arr2 = ctx.alloc_upload(data2)  # Stream 2
val arr3 = ctx.alloc_upload(data3)  # Stream 3

# Wait for all
stream1.sync()
stream2.sync()
stream3.sync()
```

---

## Type-Safe Arrays

### Generic GpuArray[T]

```simple
val ctx = Context.default()

# Type-safe allocation
val floats = ctx.alloc[f32](100)    # float array
val ints = ctx.alloc[i32](100)      # int array
val doubles = ctx.alloc[f64](100)   # double array

# Compile error: type mismatch
# floats.copy_to(ints)  # Won't compile!
```

### Upload Typed Data

```simple
val ctx = Context.default()

val float_data = [1.0, 2.0, 3.0]
val int_data = [1, 2, 3]

val gpu_floats = ctx.alloc_upload(float_data)  # GpuArray[f32]
val gpu_ints = ctx.alloc_upload(int_data)      # GpuArray[i32]
```

---

## Backend Detection

### Check Available Backends

```simple
use std.gpu.device.{detect_backends, GpuBackend}

fn main():
    val backends = detect_backends()

    print "Available backends:"
    for backend in backends:
        match backend:
            case GpuBackend.Cuda:
                print "  - CUDA"
            case GpuBackend.Vulkan:
                print "  - Vulkan"
            case GpuBackend.None:
                print "  - CPU (fallback)"
```

### Get Preferred Backend

```simple
use std.gpu.device.{preferred_backend, GpuBackend}

fn main():
    val backend = preferred_backend()

    match backend:
        case GpuBackend.Cuda:
            print "Using CUDA (best option)"
        case GpuBackend.Vulkan:
            print "Using Vulkan"
        case GpuBackend.None:
            print "Using CPU fallback (no GPU detected)"
```

---

## Error Handling

### Check for GPU

```simple
use std.gpu.{Context}
use std.gpu.device.{GpuBackend}

fn main():
    val ctx = Context.default()

    if ctx.backend == GpuBackend.None:
        print "Warning: No GPU available, using CPU"
        return

    # Proceed with GPU operations
    print "GPU available: {ctx.backend_name()}"
```

### Handle Allocation Failures

```simple
use std.gpu.{Context}

fn main():
    val ctx = Context.default()

    # Try to allocate 10GB (may fail)
    val arr = ctx.alloc[f32](2500000000)  # 10GB

    # Check if allocation succeeded
    # (In Simple, allocation returns valid handle or crashes)
    # For production, check available memory first
```

---

## Performance Tips

### 1. Reuse Context

**Bad:**
```simple
fn process_batch(data: [f32]):
    val ctx = Context.default()  # Creates new context each time
    val gpu_data = ctx.alloc_upload(data)
    # ...
```

**Good:**
```simple
fn process_batches(batches: [[f32]]):
    val ctx = Context.default()  # Create once

    for batch in batches:
        val gpu_data = ctx.alloc_upload(batch)
        # ...
```

---

### 2. Use Async Uploads

**Bad (Sequential):**
```simple
for batch in batches:
    val gpu_batch = ctx.alloc_upload(batch)
    ctx.sync()  # Wait for each upload
    process(gpu_batch)
```

**Good (Async):**
```simple
val stream = ctx.create_stream()

for batch in batches:
    val gpu_batch = ctx.alloc_upload(batch)
    # Don't sync here - let uploads queue up
    process(gpu_batch)

stream.sync()  # Single sync at end
```

---

### 3. Minimize Transfers

**Bad:**
```simple
for i in 0..1000:
    val gpu_x = ctx.alloc_upload([x])  # Upload 1 value 1000 times
    # process...
    val result = gpu_x.download()
```

**Good:**
```simple
val all_x = [...]  # Collect all values
val gpu_x = ctx.alloc_upload(all_x)  # Upload once
# process all...
val results = gpu_x.download()  # Download once
```

---

### 4. Prefer Device-to-Device Copies

**Bad:**
```simple
val cpu_data = gpu_arr1.download()  # GPU → CPU
val gpu_arr2 = ctx.alloc_upload(cpu_data)  # CPU → GPU
```

**Good:**
```simple
gpu_arr1.copy_to(gpu_arr2)  # GPU → GPU (much faster)
```

---

## Complete Example: Training Loop

```simple
use std.gpu.{Context}
use std.src.dl.config.{load_local_config}
use std.gpu.{create_context_from_config}

fn train_model(batches: [[f32]], num_epochs: i64):
    # Load GPU from config
    load_local_config()
    val ctx = create_context_from_config()

    print "Training on {ctx.backend_name()} device {ctx.device_id()}"

    # Create streams for async operations
    val upload_stream = ctx.create_stream()
    val compute_stream = ctx.create_stream()

    for epoch in 0..num_epochs:
        print "Epoch {epoch + 1}/{num_epochs}"

        # Prefetch first batch
        var current_batch = ctx.alloc_upload(batches[0])
        upload_stream.sync()

        var total_loss = 0.0

        for i in 1..batches.len():
            # Upload next batch (async)
            val next_batch = ctx.alloc_upload(batches[i])

            # Train on current batch (parallel with upload)
            val loss = train_step(current_batch)
            total_loss = total_loss + loss

            # Wait for upload
            upload_stream.sync()

            # Move to next
            current_batch = next_batch

        # Train on last batch
        val final_loss = train_step(current_batch)
        total_loss = total_loss + final_loss

        val avg_loss = total_loss / batches.len() as f32
        print "  Average loss: {avg_loss}\n"

    print "Training complete!"

fn main():
    val batches = load_data()
    train_model(batches, num_epochs: 10)
```

---

## Troubleshooting

### "No GPU detected"

**Problem:** Context falls back to CPU

**Solutions:**
1. Check NVIDIA drivers: `nvidia-smi`
2. Check CUDA runtime: `nvcc --version`
3. Check PyTorch CUDA: `python -c "import torch; print(torch.cuda.is_available())"`
4. Verify dl.config.sdn device setting

---

### "Memory allocation failed"

**Problem:** Out of GPU memory

**Solutions:**
1. Reduce batch size
2. Free unused arrays with `.drop()`
3. Use multiple GPUs
4. Check memory usage: `nvidia-smi`

---

### "Stream operations slow"

**Problem:** Not seeing speedup from async operations

**Solutions:**
1. Ensure operations are actually async (don't sync after each op)
2. Use separate streams for independent operations
3. Verify compute/transfer overlap with profiler
4. Check if operations are too small to benefit from async

---

## Next Steps

1. **Run Examples:**
   ```bash
   bin/simple examples/gpu/context_basic.spl
   bin/simple examples/gpu/async_pipeline.spl
   ```

2. **Read Detailed Reports:**
   - `doc/report/context_api_phase2_complete_2026-02-09.md`
   - `doc/report/async_pipeline_phase3_complete_2026-02-09.md`
   - `doc/report/gpu_unified_interface_complete_2026-02-09.md`

3. **Explore Advanced Patterns:**
   - `examples/gpu/training_pipeline.spl`

4. **Integrate with Your Code:**
   - Add `use std.gpu.{Context}` to your project
   - Create dl.config.sdn for device selection
   - Start with Context.default() and expand

---

## API Reference

### Context

| Method | Description |
|--------|-------------|
| `Context.default()` | Auto-detect best GPU |
| `Context.new(backend, device)` | Explicit GPU selection |
| `ctx.alloc[T](count)` | Allocate uninitialized |
| `ctx.alloc_upload(data)` | Allocate and upload |
| `ctx.alloc_zeros[T](count)` | Allocate zero-filled |
| `ctx.sync()` | Wait for all operations |
| `ctx.create_stream()` | Create async stream |
| `ctx.backend_name()` | Get backend name |
| `ctx.device_id()` | Get device ID |

### GpuArray[T]

| Method | Description |
|--------|-------------|
| `arr.upload(data)` | Upload data to GPU |
| `arr.download()` | Download from GPU |
| `arr.copy_to(other)` | Device-to-device copy |
| `arr.size_bytes()` | Get size in bytes |
| `arr.drop()` | Manual cleanup |

### Stream

| Method | Description |
|--------|-------------|
| `stream.sync()` | Wait for stream |
| `stream.query()` | Check if complete |
| `stream.drop()` | Manual cleanup |

---

## Support

**Documentation:**
- Full guide: `doc/report/gpu_unified_interface_complete_2026-02-09.md`
- Implementation plan: `doc/plan/cuda_unified_interface_impl_2026-02-09.md`

**Examples:**
- Basic usage: `examples/gpu/context_basic.spl`
- Async patterns: `examples/gpu/async_pipeline.spl`
- Training loops: `examples/gpu/training_pipeline.spl`
