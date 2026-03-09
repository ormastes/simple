# Exercise 22: Streams and Async Operations

## Asynchronous GPU Execution

By default, kernel launches and memory transfers are serialized on a single
stream. CUDA streams allow overlapping computation and data transfer for
better GPU utilization.

### Simple Stream API

| Simple | CUDA | Description |
|--------|------|-------------|
| `gpu_stream_create()` | `cudaStreamCreate` | Create a new stream |
| `gpu_stream_destroy(s)` | `cudaStreamDestroy` | Destroy a stream |
| `gpu_stream_sync(s)` | `cudaStreamSynchronize` | Wait for stream to finish |
| `gpu_device_sync()` | `cudaDeviceSynchronize` | Wait for all streams |
| `gpu_upload_async(buf, data, stream)` | `cudaMemcpyAsync(H2D)` | Async host-to-device |
| `gpu_download_async(buf, n, stream)` | `cudaMemcpyAsync(D2H)` | Async device-to-host |

### Stream Launch Syntax

```simple
val stream = gpu_stream_create()?

# Launch kernel on a specific stream
kernel<<<grid: grid_dim, block: block_dim, stream: stream>>>(args)

# Async memory transfers
gpu_upload_async(buf, data, stream)?
gpu_download_async(buf, n, stream)?

# Wait for completion
gpu_stream_sync(stream)?
gpu_stream_destroy(stream)?
```

### Overlap Patterns

**Pattern 1: Compute + Transfer overlap**
```
Stream 1: [Upload A] [Kernel A] [Download A]
Stream 2:            [Upload B] [Kernel B]  [Download B]
```

**Pattern 2: Pipeline**
```
Stream 1: [Upload 1] [Kernel 1] [Download 1]
Stream 2:           [Upload 2] [Kernel 2]  [Download 2]
Stream 3:                      [Upload 3]  [Kernel 3]  [Download 3]
```

### Key Concepts

- **Default stream (stream 0):** Synchronizes with all other streams.
  Avoid it when using multiple streams.
- **Async transfers require pinned memory:** `gpu_alloc_pinned<T>(n)` for
  host memory that can be used with async transfers.
- **Stream ordering:** Operations within a stream execute in order.
  Operations across streams can overlap.

## Files

- `main.spl` - Multi-stream processing with overlapped transfers and compute
- `spec.spl` - Tests verifying correctness of async operations

## Learning Goals

- Create and manage GPU streams
- Overlap data transfer with computation
- Use async memory transfers
- Synchronize streams correctly
