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
- **Vulkan/SPIR-V** (implemented): Cross-platform compute and graphics via Vulkan 1.1+
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
- See `doc/gpu/vulkan_implementation.md` for details

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


## Part 10: Diagnostics Summary (Normative)

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
