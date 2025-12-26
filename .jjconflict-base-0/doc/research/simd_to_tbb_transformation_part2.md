# SIMD to TBB Transformation - Part 2: Code Generation

**Part of:** [SIMD to TBB Transformation](./simd_to_tbb_transformation_part1.md)

---

    int32_t j = static_cast<int32_t>(this_index(1));

    // Bounds check via indexer
    if (!out->bounds_check(i, j)) {
        return;
    }

    // %a_val = IndexerGet(a, "get", [i, j])
    float a_val = a->get(i, j);

    // %b_val = IndexerGet(b, "get", [i, j])
    float b_val = b->get(i, j);

    // %sum = FAdd
    float sum = a_val + b_val;

    // IndexerSet(out, "set", [i, j], sum)
    out->set(i, j, sum);
}

} // namespace simple_tbb
```

### 6.4 Generated Kernel with Neighbor Accessors

```cpp
// Generated from: fn blur_1d(x: f32[], out: f32[])

namespace simple_tbb {

void blur_1d_body(float* x, float* out, int64_t len) {
    int64_t i = this_index(0);

    // Bounds check for neighbors
    int64_t left_idx = i - 1;
    int64_t right_idx = i + 1;

    // Check: _.x.under (left_idx < 0)
    if (left_idx < 0) {
        return;
    }

    // Check: _.x.over (right_idx >= len)
    if (right_idx >= len) {
        return;
    }

    // Check: _.out bounds
    if (i >= len) {
        return;
    }

    // Load neighbors
    float left_val = x[left_idx];    // x.left_neighbor
    float mid_val = x[i];            // x[i]
    float right_val = x[right_idx];  // x.right_neighbor

    // Compute average
    float avg = (left_val + mid_val + right_val) / 3.0f;

    // Store result
    out[i] = avg;
}

} // namespace simple_tbb
```

### 6.5 Generated Kernel with Shared Memory

```cpp
// Generated from: fn reduce_sum(input: f32[], output: f32[])

namespace simple_tbb {

void reduce_sum_body(float* input, float* output, int64_t len) {
    // shared let local_data: [f32; 256]
    float* local_data = shared_alloc<float>(256);

    int64_t gid = this_index(0);
    int64_t lid = thread_index(0);
    int64_t group_sz = local_size(0);

    // Load to shared memory
    local_data[lid] = (gid < len) ? input[gid] : 0.0f;

    // Barrier
    barrier();

    // Parallel reduction
    for (int64_t stride = group_sz / 2; stride > 0; stride /= 2) {
        if (lid < stride) {
            local_data[lid] += local_data[lid + stride];
        }
        barrier();
    }

    // Write result (first thread only)
    if (lid == 0) {
        output[group_index(0)] = local_data[0];
    }
}

} // namespace simple_tbb
```

---

## 7. TBB Launcher Generation

### 7.1 1D Launcher

```cpp
namespace simple_tbb {

void vector_add_launch(
    float* a, float* b, float* out, int64_t len,
    int64_t global_size,
    int64_t local_size
) {
    int64_t num_groups = (global_size + local_size - 1) / local_size;

    tbb::parallel_for(
        tbb::blocked_range<int64_t>(0, num_groups),
        [=](const tbb::blocked_range<int64_t>& group_range) {

            for (int64_t group_id = group_range.begin();
                 group_id < group_range.end();
                 ++group_id) {

                // Create per-group barrier
                tbb::spin_barrier barrier(local_size);

                // Execute threads in group
                tbb::parallel_for(
                    tbb::blocked_range<int64_t>(0, local_size),
                    [=, &barrier](const tbb::blocked_range<int64_t>& thread_range) {

                        for (int64_t local_id = thread_range.begin();
                             local_id < thread_range.end();
                             ++local_id) {

                            // Build context
                            KernelContext ctx = {};
                            ctx.global_id[0] = group_id * local_size + local_id;
                            ctx.local_id[0] = local_id;
                            ctx.group_id[0] = group_id;
                            ctx.global_size[0] = global_size;
                            ctx.local_size[0] = local_size;
                            ctx.num_groups[0] = num_groups;
                            ctx.barrier = &barrier;

                            // Set thread-local context
                            g_ctx = &ctx;

                            // Execute kernel
                            vector_add_body(a, b, out, len);

                            g_ctx = nullptr;
                        }
                    }
                );
            }
        }
    );
}

} // namespace simple_tbb
```

### 7.2 2D Launcher (for Matrix operations)

```cpp
namespace simple_tbb {

void matrix_add_launch(
    Matrix* a, Matrix* b, Matrix* out,
    int64_t global_size_x, int64_t global_size_y,
    int64_t local_size_x, int64_t local_size_y
) {
    int64_t num_groups_x = (global_size_x + local_size_x - 1) / local_size_x;
    int64_t num_groups_y = (global_size_y + local_size_y - 1) / local_size_y;
    int64_t total_groups = num_groups_x * num_groups_y;
    int64_t threads_per_group = local_size_x * local_size_y;

    tbb::parallel_for(
        tbb::blocked_range<int64_t>(0, total_groups),
        [=](const tbb::blocked_range<int64_t>& group_range) {

            for (int64_t group_linear = group_range.begin();
                 group_linear < group_range.end();
                 ++group_linear) {

                // Decode 2D group ID
                int64_t group_id_y = group_linear / num_groups_x;
                int64_t group_id_x = group_linear % num_groups_x;

                tbb::spin_barrier barrier(threads_per_group);

                tbb::parallel_for(
                    tbb::blocked_range<int64_t>(0, threads_per_group),
                    [=, &barrier](const tbb::blocked_range<int64_t>& thread_range) {

                        for (int64_t thread_linear = thread_range.begin();
                             thread_linear < thread_range.end();
                             ++thread_linear) {

                            // Decode 2D thread ID
                            int64_t local_id_y = thread_linear / local_size_x;
                            int64_t local_id_x = thread_linear % local_size_x;

                            // Build context
                            KernelContext ctx = {};
                            ctx.global_id[0] = group_id_x * local_size_x + local_id_x;
                            ctx.global_id[1] = group_id_y * local_size_y + local_id_y;
                            ctx.local_id[0] = local_id_x;
                            ctx.local_id[1] = local_id_y;
                            ctx.group_id[0] = group_id_x;
                            ctx.group_id[1] = group_id_y;
                            ctx.global_size[0] = global_size_x;
                            ctx.global_size[1] = global_size_y;
                            ctx.local_size[0] = local_size_x;
                            ctx.local_size[1] = local_size_y;
                            ctx.num_groups[0] = num_groups_x;
                            ctx.num_groups[1] = num_groups_y;
                            ctx.barrier = &barrier;

                            g_ctx = &ctx;
                            matrix_add_body(a, b, out);
                            g_ctx = nullptr;
                        }
                    }
                );
            }
        }
    );
}

} // namespace simple_tbb
```

### 7.3 Launcher with Shared Memory

```cpp
namespace simple_tbb {

void reduce_sum_launch(
    float* input, float* output, int64_t len,
    int64_t global_size, int64_t local_size,
    size_t shared_mem_size  // e.g., 256 * sizeof(float)
) {
    int64_t num_groups = (global_size + local_size - 1) / local_size;

    tbb::parallel_for(
        tbb::blocked_range<int64_t>(0, num_groups),
        [=](const tbb::blocked_range<int64_t>& group_range) {

            for (int64_t group_id = group_range.begin();
                 group_id < group_range.end();
                 ++group_id) {

                // Allocate shared memory PER GROUP
                alignas(64) char shared_mem[shared_mem_size];

                tbb::spin_barrier barrier(local_size);

                tbb::parallel_for(
                    tbb::blocked_range<int64_t>(0, local_size),
                    [=, &barrier, &shared_mem](const tbb::blocked_range<int64_t>& r) {

                        for (int64_t local_id = r.begin(); local_id < r.end(); ++local_id) {

                            KernelContext ctx = {};
                            ctx.global_id[0] = group_id * local_size + local_id;
                            ctx.local_id[0] = local_id;
                            ctx.group_id[0] = group_id;
                            ctx.global_size[0] = global_size;
                            ctx.local_size[0] = local_size;
                            ctx.num_groups[0] = num_groups;
                            ctx.barrier = &barrier;
                            ctx.shared_mem = shared_mem;
                            ctx.shared_mem_size = shared_mem_size;

                            g_ctx = &ctx;
                            reduce_sum_body(input, output, len);
                            g_ctx = nullptr;
                        }
                    }
                );
            }
        }
    );
}

} // namespace simple_tbb
```

---

## 8. Runtime FFI Bridge

### 8.1 Rust FFI Definitions

```rust
// src/runtime/src/tbb_backend.rs

use std::ffi::c_void;

#[repr(C)]
pub struct TbbDim3 {
    pub x: i64,
    pub y: i64,
    pub z: i64,
}

#[repr(C)]
pub struct TbbLaunchParams {
    pub kernel_fn: *const c_void,
    pub grid: TbbDim3,
    pub block: TbbDim3,
    pub args: *const *const c_void,
    pub arg_count: usize,
    pub shared_mem_size: usize,
}

extern "C" {
    /// Launch kernel on TBB backend
    pub fn simple_tbb_launch(params: *const TbbLaunchParams) -> i32;

    /// Get current thread's global ID
    pub fn simple_tbb_global_id(dim: i32) -> i64;

    /// Get current thread's local ID
    pub fn simple_tbb_local_id(dim: i32) -> i64;

    /// Get current thread's group ID
    pub fn simple_tbb_group_id(dim: i32) -> i64;

    /// Synchronize threads in group
    pub fn simple_tbb_barrier();

    /// Allocate shared memory
    pub fn simple_tbb_shared_alloc(size: usize, align: usize) -> *mut c_void;
}

/// High-level launch function
pub fn launch_tbb_kernel<F>(
    kernel: F,
    global_size: (i64, i64, i64),
    local_size: (i64, i64, i64),
    shared_mem_size: usize,
) where F: Fn() + Send + Sync {
    // Implementation calls into C++ TBB runtime
}
```

### 8.2 C++ Runtime Implementation

```cpp
// src/runtime/tbb_runtime.cpp

#include <tbb/tbb.h>
#include "simple_tbb.h"

extern "C" {

int32_t simple_tbb_launch(const TbbLaunchParams* params) {
    // Dispatch to appropriate launcher based on dimensionality
    // ...
    return 0;
}

int64_t simple_tbb_global_id(int32_t dim) {
    return simple_tbb::g_ctx ? simple_tbb::g_ctx->global_id[dim] : 0;
}

int64_t simple_tbb_local_id(int32_t dim) {
    return simple_tbb::g_ctx ? simple_tbb::g_ctx->local_id[dim] : 0;
}

int64_t simple_tbb_group_id(int32_t dim) {
    return simple_tbb::g_ctx ? simple_tbb::g_ctx->group_id[dim] : 0;
}

void simple_tbb_barrier() {
    if (simple_tbb::g_ctx && simple_tbb::g_ctx->barrier) {
        simple_tbb::g_ctx->barrier->wait();
    }
}

void* simple_tbb_shared_alloc(size_t size, size_t align) {
    return simple_tbb::g_ctx ? simple_tbb::g_ctx->shared_mem : nullptr;
}

} // extern "C"
```

---

## 9. Complete Transformation Summary

### 9.1 Construct Mapping Table

| Simple Construct | MIR Instruction | TBB C++ Code |
|------------------|-----------------|--------------|
| `@simd fn` | `FunctionKind::GpuKernel` | `void kernel_body()` + `kernel_launch()` |
| `@simd(backend=:tbb)` | `backend: Tbb` | Force TBB code generation |
| `@simd(dim=2)` | `dim: 2` | 2D grid/block decomposition |
| `this.index()` | `GpuGlobalId(0)` | `g_ctx->global_id[0]` |
| `this.index(1)` | `GpuGlobalId(1)` | `g_ctx->global_id[1]` |
| `this.thread_index()` | `GpuLocalId(0)` | `g_ctx->local_id[0]` |
| `this.group_index()` | `GpuGroupId(0)` | `g_ctx->group_id[0]` |
| `thread_group.barrier()` | `GpuBarrier` | `g_ctx->barrier->wait()` |
| `shared let x: [T; N]` | `GpuSharedAlloc(N*sizeof(T))` | Per-group stack allocation |
| `@bounds(default=return)` | `BoundsCheck + CondBr` | `if (i >= len) return;` |
| `x.left_neighbor` | `Index(x, i-1) + BoundsCheck` | `x[i-1]` with bounds check |
| `x.right_neighbor` | `Index(x, i+1) + BoundsCheck` | `x[i+1]` with bounds check |
| `m[i, j]` (indexer) | `IndexerGet(m, "get", [i,j])` | `m->get(i, j)` |
| `m[i, j] = v` | `IndexerSet(m, "set", [i,j], v)` | `m->set(i, j, v)` |
| `buf[i]` (@indexer field) | `Index(buf.samples, i)` | `buf->samples[i]` |

### 9.2 Launch Mapping

| Simple Launch | TBB Execution |
|---------------|---------------|
| `ctx.launch(kernel, [N], [256], args)` | `tbb::parallel_for` over `N/256` groups |
| `ctx.launch(kernel, [M, N], [16, 16], args)` | 2D `tbb::parallel_for` |
| `kernel(args)` (direct call with @simd) | Auto-launch with default sizes |

### 9.3 Performance Characteristics

| Aspect | GPU (CUDA) | CPU (TBB) |
|--------|------------|-----------|
| Thread count | 1000s-100000s | 10s-100s (core count) |
| Thread overhead | ~0 (hardware) | ~100ns per task |
| Shared memory | Fast SRAM (~100 cycles) | L1/L2 cache |
| Barrier | Hardware (~20 cycles) | `spin_barrier` (~1000 cycles) |
| Memory bandwidth | ~1 TB/s | ~100 GB/s |
| Use case | Production GPU compute | Testing, fallback, CPU-only |

---

## 10. Integration with Parallel Module

```simple
use parallel

# Auto-selects backend
parallel.set_config(
    simd_enabled: true,
    gpu_enabled: false,    # Disable GPU
    tbb_enabled: true,     # Enable TBB
    thread_count: 8
)

# Uses TBB when GPU disabled
@simd
fn my_kernel(data: f32[]):
    let i = this.index()
    data[i] *= 2.0

# Or use parallel iterators (auto-uses TBB)
data.par_map(\x: x * 2.0)
```

---

## Related Documents

- [gpu_simd.md](../spec/gpu_simd.md) - GPU/SIMD specification
- [cuda_tbb_entry_compare.md](cuda_tbb_entry_compare.md) - CUDA vs TBB comparison
- [codegen_status.md](../codegen_status.md) - MIR instruction coverage
