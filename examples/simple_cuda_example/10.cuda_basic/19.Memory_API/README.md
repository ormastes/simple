# Exercise 19: Memory API

## GPU Memory Management in Simple

Simple provides a safe, typed API for GPU memory management that wraps
CUDA's `cudaMalloc`, `cudaMemcpy`, `cudaFree`, and `cudaMemset`.

### API Overview

| Simple | CUDA | Description |
|--------|------|-------------|
| `gpu_alloc<T>(n)` | `cudaMalloc` | Allocate n elements of type T on device |
| `gpu_upload(buf, data)` | `cudaMemcpy(H2D)` | Copy host data to device buffer |
| `gpu_download<T>(buf, n)` | `cudaMemcpy(D2H)` | Copy device data to host |
| `gpu_free(buf)` | `cudaFree` | Free device buffer |
| `gpu_memset(buf, val, n)` | `cudaMemset` | Set device memory to a byte value |
| `gpu_copy(dst, src, n)` | `cudaMemcpy(D2D)` | Device-to-device copy |

### Memory Lifecycle

```
1. Allocate:  val buf = gpu_alloc<f32>(1024)?
2. Upload:    gpu_upload(buf, host_data)?
3. Compute:   kernel<<<grid, block>>>(buf, ...)
4. Download:  val result = gpu_download<f32>(buf, 1024)?
5. Free:      gpu_free(buf)?
```

### Error Handling

All memory operations return `Result<T, GpuError>`. Use `?` for propagation:

```simple
fn process() -> Result<List<f32>, GpuError>:
    val buf = gpu_alloc<f32>(1024)?    # Propagates allocation failure
    gpu_upload(buf, data)?              # Propagates transfer failure
    val result = gpu_download<f32>(buf, 1024)?
    gpu_free(buf)?
    Ok(result)
```

### Key Differences from CUDA C

1. **Typed buffers:** `GpuBuffer<f32>` carries its element type, preventing
   accidental size mismatches.
2. **No raw pointers:** Cannot accidentally dereference device memory on host.
3. **Result-based errors:** No unchecked error codes; the compiler enforces
   handling via `Result<T, GpuError>`.
4. **Size tracking:** `GpuBuffer` knows its allocated size, enabling bounds
   checking in debug mode.

## Files

- `main.spl` - Full memory lifecycle demonstration
- `spec.spl` - Tests for each memory operation

## Learning Goals

- Allocate and free GPU memory safely
- Transfer data between host and device
- Use `gpu_memset` for initialization
- Handle errors with `Result` and `?`
- Understand the host/device memory separation
