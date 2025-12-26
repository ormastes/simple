# GPU and SIMD Specification

**Version:** 2025-12-26 Update (Vulkan Backend)
**Scope:** Language + standard runtime contracts (portable semantics; backend-specific lowering is non-normative)

This document specifies GPU compute and SIMD vector operations for the Simple language.

## Recent Updates (2025-12-26)

- **Vulkan/SPIR-V Backend**: Implemented cross-platform GPU compute backend
  - SPIR-V 1.3 bytecode generation for Vulkan 1.1+
  - Full type system support (i32, i64, u32, u64, f32, f64, bool)
  - Control flow (if/else, loops, returns)
  - Multi-type buffer parameters with descriptor sets
  - Array indexing and element access
  - GPU built-ins (thread IDs, barriers, atomics)
- **Enhanced Specification**: Added Vulkan usage examples and backend selection documentation

## Design Philosophy

Simple's GPU/SIMD support follows these principles:

1. **Safety First**: All operations are bounds-checked by default
2. **Explicit Parallelism**: No hidden data races or undefined behavior
3. **Portability**: Abstract over different hardware (CPU SIMD, GPU compute)
4. **Integration**: Works seamlessly with existing type system and memory model
5. **One-pass Parsable**: All constructs recognizable with bounded lookahead
6. **No GPU GC**: Kernels are GC-free; device allocations must be explicit or value-only

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

### Execution Model (SIMT)

A GPU kernel executes across many GPU threads ("work-items"). Threads are grouped into **thread groups** (CUDA blocks / OpenCL work-groups). A kernel sees:

- `this.index()` / `gpu.global_id()` - global linear index (or tuple for multi-d)
- `this.thread_index()` / `gpu.local_id()` - index within the group
- `this.group_index()` / `gpu.group_id()` - group id

Host call semantics: Calling a GPU kernel from host code enqueues a kernel launch (async by default). Synchronization is via runtime APIs (`ctx.sync()`, `Device.wait()`).

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

Kernels are functions that run on the GPU. Two annotation styles are supported:

#### Style 1: `#[gpu]` Attribute

```simple
#[gpu]
fn vector_add(a: &[f32], b: &[f32], out: &mut [f32]):
    let idx = gpu.global_id()
    if idx < out.len():
        out[idx] = a[idx] + b[idx]
```

#### Style 2: `@simd` Annotation (with bounds policy)

```simple
@simd
fn vector_add(a: f32[], b: f32[], out: f32[]):
    let i = this.index()
    out[i] = a[i] + b[i]
```

**Key difference:** `@simd` implies a default bounds policy (`@bounds(default=return, strict=true)`) that automatically handles out-of-bounds accesses by returning from the thread. The `#[gpu]` style requires explicit bounds checks.

#### `@simd` Parameters (optional)

```simple
@simd(grid_size=1024, group_size=256, stream=0, dim=1)
fn my_kernel(...):
    ...
```

- `grid_size` - total threads (scalar or tuple)
- `group_size` - threads per group (scalar or tuple)
- `stream` - queue/stream id
- `dim` - explicit dimensionality (1, 2, or 3)

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

Available inside GPU kernel functions:

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

# Alternative @simd style
this.index()              # global linear index
this.thread_index()       # index within group
this.group_index()        # group id
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

### Thread Groups and Barriers

```simple
# Within kernels, thread_group is an implicit object
thread_group.id           # Group ID
thread_group.size         # Group size
thread_group.barrier()    # Synchronize threads in group

# Or use gpu.* functions
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

---

## Part 3: Kernel Bounds Policy

This section defines the default and programmable behavior when indexing may underflow or overflow in GPU kernels using the `@simd` annotation.

### 3.1 Terms

- **Indexable variable**: any expression used as `base[index...]` (array, buffer, user indexer)
- **Underflow**: `index < lower bound` (typically < 0)
- **Overflow**: `index >= upper bound` (typically >= length)
- **Bounds event**: a dynamic situation where an index operation would underflow/overflow

### 3.2 Default Rule

**`@simd` implies `@bounds(default=return, strict=true)`**

Every `@simd` kernel has an implicit bounds policy unless explicitly overridden:

- `default=return`: any bounds event causes the current GPU thread to return from the kernel
- `strict=true`: the compiler performs static coverage analysis; uncovered possible bounds events must be diagnosed

Override per kernel:

```simple
@simd @bounds(default=trap, strict=true)
fn my_kernel(...):
    ...
```

### 3.3 `@bounds(...)` Attribute

Parameters:

| Parameter | Values | Description |
|-----------|--------|-------------|
| `default` | `return`, `trap`, `panic`, `ignore` | What to do on uncovered bounds events |
| `strict` | `true`, `false` | Whether to require coverage analysis |

- `return`: early-exit the current GPU thread
- `trap`: device trap/abort for the kernel (backend-defined)
- `panic`: host-visible failure (requires runtime support)
- `ignore`: proceed without intervention (unsafe; intended only with explicit `bounds:` cases)

### 3.4 `bounds:` Clause (Pattern-Based Handlers)

A `@simd` kernel may include a trailing `bounds:` block that defines handlers:

```simple
@simd
fn vector_add(a: f32[], b: f32[], out: f32[]):
    let i = this.index()
    out[i] = a[i] + b[i]

bounds:
    _.out.over:
        return
    _.out.under:
        return
```

#### Pattern Keys

A bounds case label is a boolean condition composed of bounds atoms:

- **Bounds atom**: `_.<var>.<kind>` where `<var>` is the base variable and `<kind>` is `over` or `under`
- **Boolean composition**: `&&`, `||`, parentheses `(...)` are permitted

Examples:
- `_.out.over:`
- `(_.a.over || _.b.over) && _.out.over:`
- `_.out.under || _.out.over:`

#### Default Handler

```simple
bounds:
    _.x.over:
        return
    _:                    # Catch-all
        return
```

#### Rules

1. **Fallthrough is an error**: Each case body must end in a terminator (`return`, `trap`, `panic`)
2. **Dead code diagnostics**: Unreachable/shadowed cases are errors under `strict=true`
3. **Uncovered case diagnostics**: Under `strict=true`, all reachable bounds events must be covered

### 3.5 Interaction with `@skip_index_range_check`

`@skip_index_range_check` disables bounds checks at indexing operation sites. It is invalid to combine:
- `@skip_index_range_check` with `@bounds(strict=true)` unless the compiler can prove no out-of-bounds

---

## Part 4: Indexer Trait and Neighbor Accessors

### 4.1 User-Defined Indexers

A class may declare an indexer signature:

```simple
class Matrix indexer(i: i32, j: i32) -> f32:
    data: f32[]
    width: i32

    fn get(self, i: i32, j: i32) -> f32:
        return self.data[i * self.width + j]

    fn set(self, i: i32, j: i32, v: f32):
        self.data[i * self.width + j] = v
```

Compiler desugaring:
- `m[i, j]` in rvalue context -> `m.get(i, j)`
- `m[i, j] = v` -> `m.set(i, j, v)`

### 4.2 Indexer Forwarding (`@indexer` field)

A class may mark exactly one field as the default forwarded indexer:

```simple
class AudioBuffer:
    @indexer samples: f32[]
```

Then `buf[i]` forwards to `buf.samples[i]`.

### 4.3 Neighbor Accessors

For indexables with 1D integer indexing, the following postfix properties are available in `@simd` contexts:

- `.left_neighbor` -> element at `index - 1`
- `.right_neighbor` -> element at `index + 1`

Context rule: the "current index" is the kernel's `this.index()`.

Bounds behavior: Neighbor access triggers bounds events and is governed by `@bounds` / `bounds:`.

```simple
@simd
fn blur_1d(x: f32[], out: f32[]):
    let i = this.index()
    let left  = x.left_neighbor
    let mid   = x[i]
    let right = x.right_neighbor
    out[i] = (left + mid + right) / 3.0

bounds:
    _.x.under || _.x.over:
        return
    _.out.under || _.out.over:
        return
```

---

## Part 5: Data Parallel Operations

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

## Part 6: Hardware Detection and Fallbacks

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

## Part 7: Feature Mapping

| Simple | CUDA | OpenCL |
|--------|------|--------|
| `@simd` / `#[gpu]` kernel | `__global__` | `__kernel` |
| `this.index()` / `gpu.global_id()` | global thread id | `get_global_id(0)` |
| `thread_group.barrier()` / `gpu.barrier()` | `__syncthreads()` | `barrier()` |
| `shared let` | `__shared__` | `__local` |
| `bounds:` + `@bounds(...)` | Manual `if (i < n) return;` | Manual bounds check |

---

## Part 8: Implementation Notes

### SIMD Codegen

SIMD operations compile to:
- SSE/AVX/AVX-512 on x86_64
- NEON on ARM
- Scalar fallback when SIMD unavailable

The compiler uses LLVM's vector intrinsics through Cranelift's SIMD support.

### GPU Backend

The GPU backend supports multiple implementations:
- **Software** (default): CPU-based execution for testing/fallback
- **CUDA/LLVM** (native): NVIDIA GPUs via PTX code generation
- **Vulkan/SPIR-V** (implemented): Cross-platform compute via Vulkan 1.1+
- **WGPU** (planned): Cross-platform WebGPU-based compute
- **Metal** (planned): Apple GPUs

The `#[gpu]` / `@simd` attribute triggers special compilation:
1. Function is lowered to GPU MIR instructions
2. Backend generates target code:
   - CUDA: PTX assembly for NVIDIA GPUs
   - Vulkan: SPIR-V bytecode for Vulkan-compatible GPUs
   - Software: CPU-based fallback
3. Runtime loads and executes the kernel
4. Kernel is cached for subsequent calls

### Current Implementation

**GPU MIR Instructions** (`src/compiler/src/mir/instructions.rs`):
- Thread identification: `GpuGlobalId`, `GpuLocalId`, `GpuGroupId`
- Grid dimensions: `GpuGlobalSize`, `GpuLocalSize`, `GpuNumGroups`
- Synchronization: `GpuBarrier`, `GpuMemFence`
- Atomics: `GpuAtomic` (add, sub, xchg, cmpxchg, min, max, and, or, xor)
- Memory: `GpuSharedAlloc`

**LLVM GPU Backend** (`src/compiler/src/codegen/llvm/gpu.rs`):
- Generates NVPTX target code for NVIDIA GPUs
- Supports compute capabilities SM50-SM90
- PTX assembly emission for kernel compilation

**CUDA Runtime** (`src/runtime/src/cuda_runtime.rs`):
- CUDA Driver API wrapper
- Device enumeration and context management
- Module loading and kernel launching
- Device memory allocation

**Vulkan/SPIR-V Backend** (`src/compiler/src/codegen/vulkan/`):
- SPIR-V 1.3 bytecode generation for Vulkan 1.1+ compatibility
- Cross-platform compute shader compilation (Linux, Windows, macOS)
- rspirv 0.12-based module builder
- Supported capabilities:
  - Type system: i32, i64, u32, u64, f32, f64, bool, void
  - Arithmetic: Add, Sub, Mul, Div, Mod (integer and float)
  - Comparison: Lt, LtEq, Gt, GtEq, Eq, NotEq
  - Bitwise: And, Or, Xor
  - Memory: Load, Store with type-aware operations
  - Control flow: Return, Jump, Branch (conditional), Unreachable
  - Buffer parameters: StorageBuffer with descriptor sets
  - Array indexing: OpAccessChain for element access
  - GPU built-ins: global_id, local_id, group_id
  - Synchronization: Barriers (OpControlBarrier)
  - Atomics: Add, Sub, Min, Max, And, Or, Xor, Exchange
- See `doc/report/VULKAN_BACKEND_IMPLEMENTATION_2025-12-26.md` for details

**Software Backend** (`src/runtime/src/value/gpu.rs`):
- Thread-local work item state simulation
- 1D and 3D kernel execution on CPU
- Useful for testing and systems without GPU

**CPU Parallel Backend** (`src/runtime/src/parallel.rs`):
- Rayon-based work-stealing parallel execution
- High-performance CPU parallel execution
- Same programming model as GPU kernels
- Pure Rust implementation (no C++ FFI required)
- See [cpu_simd_scheduling.md](../research/cpu_simd_scheduling.md) for details

The CPU parallel backend uses Rayon's work-stealing scheduler:

```simple
@simd(backend=:cpu)
fn vector_add(a: f32[], b: f32[], out: f32[]):
    let i = this.index()
    out[i] = a[i] + b[i]
```

Runtime execution:
1. `this.index()` → thread-local `THREAD_INDEX` via `rt_par_global_id()`
2. `thread_group.barrier()` → `std::sync::Barrier::wait()`
3. `shared let` → per-group stack allocation
4. Kernel launch → `(0..n).into_par_iter().for_each(|i| kernel())`

### Vulkan Backend Usage Examples

The Vulkan backend enables cross-platform GPU compute with SPIR-V:

```simple
use gpu

# Vector addition kernel (Vulkan backend)
#[gpu]
fn vector_add_vulkan(a: &[f32], b: &[f32], out: &mut [f32]):
    let idx = gpu.global_id()
    if idx < out.len():
        out[idx] = a[idx] + b[idx]

# Launch on Vulkan device
fn main():
    let ctx = gpu.Context.new(backend: :vulkan)

    # Allocate buffers
    let a = ctx.alloc_upload([1.0, 2.0, 3.0, 4.0])
    let b = ctx.alloc_upload([5.0, 6.0, 7.0, 8.0])
    let out = ctx.alloc[f32](4)

    # Launch kernel
    ctx.launch(
        kernel: vector_add_vulkan,
        global_size: [4],
        args: [a, b, out]
    )

    # Get results
    ctx.sync()
    let result = out.download()  # [6.0, 8.0, 10.0, 12.0]
```

#### Multi-type Buffer Support

The Vulkan backend supports multiple data types in the same kernel:

```simple
#[gpu]
fn mixed_types(
    int_buf: &[i32],
    float_buf: &[f32],
    out_i64: &mut [i64],
    out_f64: &mut [f64]
):
    let idx = gpu.global_id()
    if idx < int_buf.len():
        # Integer operations
        out_i64[idx] = int_buf[idx] as i64 * 2

        # Float operations
        out_f64[idx] = float_buf[idx] as f64 + 1.0
```

#### Control Flow and Array Indexing

```simple
#[gpu]
fn prefix_sum(input: &[f32], output: &mut [f32]):
    let idx = gpu.global_id()

    if idx == 0:
        output[0] = input[0]
    elif idx < input.len():
        # Access previous element
        let prev_sum = output[idx - 1]
        output[idx] = prev_sum + input[idx]
```

### Backend Selection

The compiler automatically selects the appropriate GPU backend based on:

1. **Feature flags**: Build-time configuration enables/disables backends
   - `vulkan` - Vulkan/SPIR-V backend
   - `cuda` - CUDA/PTX backend
   - `wgpu` - WebGPU backend (planned)

2. **Runtime detection**: Hardware capabilities are queried at runtime
   - Vulkan: Checks for compatible Vulkan 1.1+ drivers
   - CUDA: Checks for NVIDIA GPUs with compute capability 5.0+

3. **Explicit selection**: User can force a specific backend
   ```simple
   @simd(backend=:vulkan)
   fn my_kernel(...): ...

   @simd(backend=:cuda)
   fn my_kernel(...): ...
   ```

4. **Fallback chain**: GPU → SIMD → Scalar
   - If GPU unavailable, falls back to CPU SIMD
   - If SIMD unavailable, falls back to scalar execution

### Safety Guarantees

1. **Bounds checking**: All buffer accesses are checked (default with `@simd`)
2. **Race freedom**: No shared mutable state between work items
3. **Memory safety**: GPU buffers are managed, no dangling pointers
4. **Type safety**: All operations are statically typed
5. **Cross-platform**: Same code runs on CUDA, Vulkan, and CPU backends

### Performance Considerations

1. **Data transfer**: Minimize CPU-GPU transfers
2. **Occupancy**: Choose work group sizes for good GPU utilization
3. **Memory coalescing**: Access patterns affect performance
4. **Vectorization**: Compiler auto-vectorizes where possible

---

## Part 9: Diagnostics Summary (Normative)

In `@simd` kernels:

| Condition | Diagnostic |
|-----------|------------|
| Fallthrough in `bounds:` | Error |
| Unreachable/duplicate/shadowed case | Warning (error under `strict=true`) |
| Uncovered reachable bounds event (with `strict=true`) | Error |
| `@skip_index_range_check` + `@bounds(strict=true)` | Error (unless provably safe) |

---

## Related Specifications

- [Types](types.md)
- [Memory and Ownership](memory.md)
- [Standard Library](stdlib.md)
- [Concurrency](concurrency.md)

## Related Implementation Documentation

- [Vulkan Backend Implementation Report](../report/VULKAN_BACKEND_IMPLEMENTATION_2025-12-26.md) - Vulkan/SPIR-V backend details
- [CPU SIMD Scheduling](../research/cpu_simd_scheduling.md) - CPU parallel backend with Rayon
- [CUDA vs TBB Comparison](../research/cuda_tbb_entry_compare.md) - CUDA vs TBB comparison
