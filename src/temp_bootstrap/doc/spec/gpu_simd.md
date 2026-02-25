# GPU and SIMD Specification

This document specifies GPU compute and SIMD vector operations for the Simple language.

## Design Philosophy

Simple's GPU/SIMD support follows these principles:

1. **Safety First**: All operations are bounds-checked by default
2. **Explicit Parallelism**: No hidden data races or undefined behavior
3. **Portability**: Abstract over different hardware (CPU SIMD, GPU compute)
4. **Integration**: Works seamlessly with existing type system and memory model

---

## Part 1: SIMD Vector Types

### Vector Type Syntax

SIMD vectors are fixed-size, homogeneous arrays optimized for parallel arithmetic:

```simple
# Vector type syntax: vec[N, T] where N is lane count, T is element type
let v1: vec[4, f32] = vec[1.0, 2.0, 3.0, 4.0]
let v2: vec[8, i32] = vec[1, 2, 3, 4, 5, 6, 7, 8]

# Type aliases for common sizes
type f32x4 = vec[4, f32]
type f32x8 = vec[8, f32]
type i32x4 = vec[4, i32]
type i32x8 = vec[8, i32]
```

### Supported Lane Counts

| Type | 2-lane | 4-lane | 8-lane | 16-lane |
|------|--------|--------|--------|---------|
| f64 | vec[2, f64] | vec[4, f64] | vec[8, f64] | - |
| f32 | vec[2, f32] | vec[4, f32] | vec[8, f32] | vec[16, f32] |
| i64 | vec[2, i64] | vec[4, i64] | vec[8, i64] | - |
| i32 | vec[2, i32] | vec[4, i32] | vec[8, i32] | vec[16, i32] |
| i16 | vec[2, i16] | vec[4, i16] | vec[8, i16] | vec[16, i16] |
| i8 | vec[2, i8] | vec[4, i8] | vec[8, i8] | vec[16, i8] |
| bool | vec[2, bool] | vec[4, bool] | vec[8, bool] | vec[16, bool] |

### Vector Operations

#### Arithmetic (Lane-wise)

```simple
let a: f32x4 = vec[1.0, 2.0, 3.0, 4.0]
let b: f32x4 = vec[5.0, 6.0, 7.0, 8.0]

let sum = a + b       # vec[6.0, 8.0, 10.0, 12.0]
let diff = a - b      # vec[-4.0, -4.0, -4.0, -4.0]
let prod = a * b      # vec[5.0, 12.0, 21.0, 32.0]
let quot = a / b      # vec[0.2, 0.333..., 0.428..., 0.5]
```

#### Comparison (Returns bool vector)

```simple
let mask = a < b      # vec[true, true, true, true]
let eq = a == b       # vec[false, false, false, false]
```

#### Reductions

```simple
let total = a.sum()           # 10.0 (horizontal sum)
let product = a.product()     # 24.0 (horizontal product)
let maximum = a.max()         # 4.0
let minimum = a.min()         # 1.0
let all_positive = (a > 0.0).all()  # true
let any_negative = (a < 0.0).any()  # false
```

#### Shuffles and Swizzles

```simple
# Named swizzle (for vec[2-4])
let v: f32x4 = vec[1.0, 2.0, 3.0, 4.0]
let swapped = v.yxzw          # vec[2.0, 1.0, 3.0, 4.0]
let broadcast = v.xxxx        # vec[1.0, 1.0, 1.0, 1.0]

# Index shuffle (for any size)
let shuffled = v.shuffle([3, 2, 1, 0])  # vec[4.0, 3.0, 2.0, 1.0]

# Cross-vector shuffle
let merged = a.blend(b, [0, 1, 4, 5])   # Takes indices, 0-3 from a, 4-7 from b
```

#### Lane Access

```simple
let v: f32x4 = vec[1.0, 2.0, 3.0, 4.0]
let first = v[0]              # 1.0 (extract)
let modified = v.with(2, 9.0) # vec[1.0, 2.0, 9.0, 4.0] (immutable update)
```

#### Load/Store

```simple
# Load from array (aligned)
let arr: [f32; 8] = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0]
let v1 = f32x4.load(arr, 0)   # Load from index 0
let v2 = f32x4.load(arr, 4)   # Load from index 4

# Store to array
v1.store(arr, 0)

# Gather (indexed load)
let indices: i32x4 = vec[0, 2, 4, 6]
let gathered = f32x4.gather(arr, indices)  # vec[1.0, 3.0, 5.0, 7.0]

# Scatter (indexed store)
v1.scatter(arr, indices)
```

#### Math Functions

```simple
let v: f32x4 = vec[1.0, 4.0, 9.0, 16.0]

let sqrts = v.sqrt()          # vec[1.0, 2.0, 3.0, 4.0]
let recip = v.recip()         # vec[1.0, 0.25, 0.111..., 0.0625]
let abs_v = (-v).abs()        # vec[1.0, 4.0, 9.0, 16.0]
let floor_v = v.floor()
let ceil_v = v.ceil()
let round_v = v.round()

# Fused multiply-add (a * b + c)
let fma = a.fma(b, c)         # More accurate than a * b + c
```

#### Masked Operations

```simple
let mask: vec[4, bool] = vec[true, false, true, false]
let a: f32x4 = vec[1.0, 2.0, 3.0, 4.0]
let b: f32x4 = vec[5.0, 6.0, 7.0, 8.0]

# Select: mask ? a : b
let selected = mask.select(a, b)  # vec[1.0, 6.0, 3.0, 8.0]

# Masked load (load only where mask is true)
let loaded = f32x4.load_masked(arr, 0, mask, 0.0)  # 0.0 for masked lanes

# Masked store (store only where mask is true)
a.store_masked(arr, 0, mask)
```

### SIMD Best Practices

```simple
# Prefer wider vectors when hardware supports it
const SIMD_WIDTH = simd.preferred_width[f32]()  # 4, 8, or 16 depending on CPU

# Process arrays in chunks
fn process_array(data: &mut [f32]):
    let chunks = data.len() / SIMD_WIDTH
    for i in 0..chunks:
        let v = f32x4.load(data, i * SIMD_WIDTH)
        let result = v * 2.0 + 1.0
        result.store(data, i * SIMD_WIDTH)

    # Handle remainder with scalar code
    for i in (chunks * SIMD_WIDTH)..data.len():
        data[i] = data[i] * 2.0 + 1.0
```

---

## Part 2: GPU Compute

### Device and Context

```simple
use gpu

# Query available devices
let devices = gpu.devices()
for d in devices:
    print "Device: {d.name}, Memory: {d.memory_mb}MB"

# Create compute context
let ctx = gpu.Context.new(device: devices[0])

# Or use default device
let ctx = gpu.Context.default()
```

### GPU Buffers

```simple
# Allocate device buffer
let buf: gpu.Buffer[f32] = ctx.alloc(1024)  # 1024 f32 elements

# Upload data to GPU
let host_data: [f32; 1024] = [...]
buf.upload(host_data)

# Download data from GPU
let result = buf.download()  # Returns [f32; 1024]

# Map buffer for direct access (advanced)
with buf.map() as mapped:
    mapped[0] = 42.0
```

### Compute Kernels

Kernels are functions that run on the GPU. They use the `#[gpu]` attribute:

```simple
#[gpu]
fn vector_add(a: &[f32], b: &[f32], out: &mut [f32]):
    let idx = gpu.global_id()
    if idx < out.len():
        out[idx] = a[idx] + b[idx]

#[gpu]
fn matrix_multiply(
    a: &[f32], b: &[f32], out: &mut [f32],
    m: u32, n: u32, k: u32
):
    let row = gpu.global_id(0)
    let col = gpu.global_id(1)

    if row < m and col < n:
        let mut sum = 0.0
        for i in 0..k:
            sum += a[row * k + i] * b[i * n + col]
        out[row * n + col] = sum
```

### Launching Kernels

```simple
# Create buffers
let a_buf = ctx.alloc_upload(host_a)
let b_buf = ctx.alloc_upload(host_b)
let out_buf = ctx.alloc[f32](1024)

# Launch kernel
ctx.launch(
    kernel: vector_add,
    global_size: [1024],       # Total work items
    local_size: [256],         # Work group size (optional)
    args: [a_buf, b_buf, out_buf]
)

# Wait for completion
ctx.sync()

# Get results
let result = out_buf.download()
```

### Work Item Intrinsics

Available inside `#[gpu]` functions:

```simple
gpu.global_id()           # 1D global index
gpu.global_id(dim)        # Multi-dimensional global index
gpu.local_id()            # Local index within work group
gpu.local_id(dim)
gpu.group_id()            # Work group index
gpu.group_id(dim)
gpu.global_size()         # Total number of work items
gpu.local_size()          # Work group size
gpu.num_groups()          # Number of work groups
```

### Shared Memory

Work groups can share fast local memory:

```simple
#[gpu]
fn reduce_sum(input: &[f32], output: &mut [f32], n: u32):
    # Shared memory declaration
    shared let local_data: [f32; 256]

    let gid = gpu.global_id()
    let lid = gpu.local_id()

    # Load to shared memory
    local_data[lid] = if gid < n: input[gid] else: 0.0

    # Synchronize work group
    gpu.barrier()

    # Parallel reduction in shared memory
    let mut stride = gpu.local_size() / 2
    while stride > 0:
        if lid < stride:
            local_data[lid] += local_data[lid + stride]
        gpu.barrier()
        stride /= 2

    # Write result
    if lid == 0:
        output[gpu.group_id()] = local_data[0]
```

### Synchronization

```simple
gpu.barrier()             # Synchronize all threads in work group
gpu.mem_fence()           # Memory fence (ensure writes visible)
gpu.barrier_and_fence()   # Both barrier and fence
```

### Atomic Operations

```simple
#[gpu]
fn histogram(input: &[u32], bins: &mut [u32]):
    let idx = gpu.global_id()
    if idx < input.len():
        let bin = input[idx]
        gpu.atomic_add(&bins[bin], 1)

# Available atomics:
gpu.atomic_add(ptr, val)
gpu.atomic_sub(ptr, val)
gpu.atomic_min(ptr, val)
gpu.atomic_max(ptr, val)
gpu.atomic_and(ptr, val)
gpu.atomic_or(ptr, val)
gpu.atomic_xor(ptr, val)
gpu.atomic_exchange(ptr, val)
gpu.atomic_compare_exchange(ptr, expected, desired)
```

### Async GPU Operations

```simple
async fn compute_async():
    let ctx = gpu.Context.default()

    # Async upload
    let buf = await ctx.upload_async(host_data)

    # Async kernel launch (returns immediately)
    let event = ctx.launch_async(
        kernel: my_kernel,
        global_size: [1024],
        args: [buf]
    )

    # Do other work while GPU computes...

    # Wait for specific operation
    await event

    # Async download
    let result = await buf.download_async()
```

### Multi-GPU

```simple
let devices = gpu.devices()
let contexts: [gpu.Context] = devices.map(\d: gpu.Context.new(device: d))

# Distribute work across GPUs
let chunk_size = data.len() / contexts.len()
let futures = []

for i, ctx in contexts.enumerate():
    let start = i * chunk_size
    let end = if i == contexts.len() - 1: data.len() else: start + chunk_size

    futures.push(async:
        let buf = await ctx.upload_async(data[start:end])
        ctx.launch(kernel: process, args: [buf])
        ctx.sync()
        return buf.download()
    )

# Gather results
let results = await futures.all()
```

---

## Part 3: Data Parallel Operations

Higher-level abstractions built on GPU/SIMD:

### Parallel Iterators

```simple
use parallel

# Parallel map (auto-selects SIMD or GPU)
let result = data.par_map(\x: x * 2.0 + 1.0)

# Parallel reduce
let sum = data.par_reduce(0.0, \a, b: a + b)

# Parallel filter
let positive = data.par_filter(\x: x > 0.0)

# Parallel for_each
data.par_for_each \x:
    print x
```

### Parallel Configuration

```simple
use parallel

# Configure parallelism
parallel.set_config(
    simd_enabled: true,
    gpu_enabled: true,
    gpu_threshold: 10000,    # Min elements before using GPU
    thread_count: 8          # For CPU parallelism
)

# Force specific backend
let result = data.par_map(backend: :gpu, \x: x * 2.0)
let result = data.par_map(backend: :simd, \x: x * 2.0)
let result = data.par_map(backend: :cpu, \x: x * 2.0)
```

### Tensor Operations (Preview)

```simple
use tensor

# Create tensors
let a = Tensor.new[[f32; 3, 3]]([
    [1.0, 2.0, 3.0],
    [4.0, 5.0, 6.0],
    [7.0, 8.0, 9.0]
])

let b = Tensor.zeros[[f32; 3, 3]]()
let c = Tensor.ones[[f32; 3, 3]]()

# Operations (auto-parallelized)
let d = a @ b                 # Matrix multiply
let e = a + b                 # Element-wise add
let f = a.transpose()         # Transpose
let g = a.sum(axis: 0)        # Reduce along axis
```

---

## Part 4: Hardware Detection and Fallbacks

### Feature Detection

```simple
use simd

# Check CPU SIMD support
if simd.has_avx512():
    # Use 512-bit vectors
    let v = vec[16, f32].load(data, 0)
elif simd.has_avx2():
    # Use 256-bit vectors
    let v = vec[8, f32].load(data, 0)
else:
    # Fallback to 128-bit
    let v = vec[4, f32].load(data, 0)

# Query preferred width
let width = simd.preferred_width[f32]()
```

### GPU Feature Detection

```simple
use gpu

let device = gpu.devices()[0]

# Check capabilities
if device.supports_f64():
    # Use double precision
    pass

if device.shared_memory_size() >= 48 * 1024:
    # Use larger shared memory tiles
    pass

if device.supports_atomics():
    # Use atomic operations
    pass
```

### Graceful Fallbacks

```simple
# Automatic fallback: GPU -> SIMD -> Scalar
fn process(data: &mut [f32]):
    if gpu.available() and data.len() > 10000:
        process_gpu(data)
    elif simd.available():
        process_simd(data)
    else:
        process_scalar(data)

# Or use the parallel module which handles this automatically
data.par_map(\x: x * 2.0)
```

---

## Implementation Notes

### SIMD Codegen

SIMD operations compile to:
- SSE/AVX/AVX-512 on x86_64
- NEON on ARM
- Scalar fallback when SIMD unavailable

The compiler uses LLVM's vector intrinsics through Cranelift's SIMD support.

### GPU Backend

The GPU backend supports multiple implementations:
- **WGPU** (default): Cross-platform WebGPU-based compute
- **CUDA** (optional): NVIDIA GPUs
- **Metal** (optional): Apple GPUs
- **Vulkan Compute** (optional): Cross-platform

The `#[gpu]` attribute triggers special compilation:
1. Function is lowered to SPIR-V or target-specific IR
2. Runtime loads and JIT-compiles the kernel
3. Kernel is cached for subsequent calls

### Safety Guarantees

1. **Bounds checking**: All buffer accesses are checked
2. **Race freedom**: No shared mutable state between work items
3. **Memory safety**: GPU buffers are managed, no dangling pointers
4. **Type safety**: All operations are statically typed

### Performance Considerations

1. **Data transfer**: Minimize CPU-GPU transfers
2. **Occupancy**: Choose work group sizes for good GPU utilization
3. **Memory coalescing**: Access patterns affect performance
4. **Vectorization**: Compiler auto-vectorizes where possible

---

## Related Specifications

- [Types](types.md)
- [Memory and Ownership](memory.md)
- [Standard Library](stdlib.md)
- [Concurrency](concurrency.md)
