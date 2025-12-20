# Simple @simd to TBB Transformation Pipeline

**Version:** 2025-12
**Purpose:** Detailed specification for transforming Simple `@simd` kernels to TBB-based CPU execution

This document specifies how Simple's `@simd` annotated functions are transformed into TBB (Threading Building Blocks) runnable code for CPU-based parallel execution.

---

## 1. Overview

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    Simple @simd to TBB Pipeline                              │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│  Simple Source          Parser           HIR            MIR                  │
│  ┌──────────────┐      ┌──────┐       ┌──────┐       ┌──────┐               │
│  │ @simd        │─────►│Detect│──────►│Mark  │──────►│ GPU  │               │
│  │ fn kernel()  │      │@simd │       │Kernel│       │Instrs│               │
│  └──────────────┘      └──────┘       └──────┘       └──────┘               │
│                                                           │                  │
│                              ┌────────────────────────────┤                  │
│                              │                            │                  │
│                              ▼                            ▼                  │
│                        ┌──────────┐               ┌──────────┐              │
│                        │   GPU    │               │   TBB    │              │
│                        │ Backend  │               │ Backend  │              │
│                        │(CUDA/PTX)│               │ (C++/TBB)│              │
│                        └──────────┘               └────┬─────┘              │
│                                                        │                     │
│                                                        ▼                     │
│                                              ┌─────────────────┐            │
│                                              │ Generated C++   │            │
│                                              │ + TBB Runtime   │            │
│                                              └─────────────────┘            │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## 2. Source Language Constructs

### 2.1 Basic @simd Kernel

```simple
@simd
fn vector_add(a: f32[], b: f32[], out: f32[]):
    let i = this.index()
    out[i] = a[i] + b[i]
```

### 2.2 With Bounds Policy

```simple
@simd @bounds(default=return, strict=true)
fn safe_add(a: f32[], b: f32[], out: f32[]):
    let i = this.index()
    out[i] = a[i] + b[i]

bounds:
    _.out.over || _.out.under:
        return
```

### 2.3 With Shared Memory

```simple
@simd
fn reduce_sum(input: f32[], output: f32[]):
    shared let local_data: [f32; 256]

    let gid = this.index()
    let lid = this.thread_index()

    local_data[lid] = input[gid]
    thread_group.barrier()

    # Reduction...
```

### 2.4 With User-Defined Indexer

```simple
class Matrix indexer(i: i32, j: i32) -> f32:
    data: f32[]
    width: i32
    height: i32

    fn get(self, i: i32, j: i32) -> f32:
        return self.data[i * self.width + j]

    fn set(self, i: i32, j: i32, v: f32):
        self.data[i * self.width + j] = v

    fn bounds_check(self, i: i32, j: i32) -> bool:
        return i >= 0 and i < self.height and j >= 0 and j < self.width

@simd(dim=2)
fn matrix_add(a: Matrix, b: Matrix, out: Matrix):
    let i = this.index(0)  # row
    let j = this.index(1)  # col
    out[i, j] = a[i, j] + b[i, j]
```

### 2.5 With @indexer Field Forwarding

```simple
class AudioBuffer:
    @indexer samples: f32[]
    sample_rate: i32

@simd
fn amplify(buf: AudioBuffer, gain: f32, out: AudioBuffer):
    let i = this.index()
    out[i] = buf[i] * gain  # Forwards to buf.samples[i]
```

### 2.6 With Neighbor Accessors

```simple
@simd
fn blur_1d(x: f32[], out: f32[]):
    let i = this.index()
    let left  = x.left_neighbor   # x[i - 1]
    let mid   = x[i]              # x[i]
    let right = x.right_neighbor  # x[i + 1]
    out[i] = (left + mid + right) / 3.0

bounds:
    _.x.under || _.x.over:
        return
```

---

## 3. Parser Stage

### 3.1 @simd Annotation Detection

```rust
// src/parser/src/annotations.rs

#[derive(Debug, Clone)]
pub struct SimdAnnotation {
    pub backend: Option<SimdBackend>,
    pub grid_size: Option<Expr>,
    pub group_size: Option<Expr>,
    pub dim: u8,  // 1, 2, or 3
    pub stream: Option<i32>,
}

#[derive(Debug, Clone)]
pub enum SimdBackend {
    Auto,      // Runtime selection
    Gpu,       // Force GPU (CUDA/PTX)
    Tbb,       // Force TBB (CPU)
    Simd,      // Force CPU SIMD (vectorization)
}
```

### 3.2 Intrinsic Recognition

| Source Pattern | Parsed As |
|----------------|-----------|
| `this.index()` | `Intrinsic::ThisIndex { dim: 0 }` |
| `this.index(1)` | `Intrinsic::ThisIndex { dim: 1 }` |
| `this.thread_index()` | `Intrinsic::ThreadIndex { dim: 0 }` |
| `this.group_index()` | `Intrinsic::GroupIndex { dim: 0 }` |
| `thread_group.barrier()` | `Intrinsic::Barrier` |
| `x.left_neighbor` | `Intrinsic::NeighborAccess { base: x, offset: -1 }` |
| `x.right_neighbor` | `Intrinsic::NeighborAccess { base: x, offset: +1 }` |

### 3.3 Indexer Declaration Parsing

```rust
// AST for indexer class
ClassDef {
    name: "Matrix",
    indexer: Some(IndexerSignature {
        params: [(i, i32), (j, i32)],
        return_type: f32,
    }),
    fields: [...],
    methods: [
        MethodDef { name: "get", ... },
        MethodDef { name: "set", ... },
    ]
}

// AST for @indexer field
FieldDef {
    name: "samples",
    ty: "f32[]",
    annotations: [Annotation::Indexer],
}
```

---

## 4. HIR Stage

### 4.1 Kernel Function Representation

```rust
// src/compiler/src/hir/types.rs

pub struct HirFunction {
    pub name: String,
    pub kind: FunctionKind,
    pub params: Vec<HirParam>,
    pub body: Vec<HirStmt>,
    pub bounds_policy: BoundsPolicy,
    pub bounds_handlers: Vec<BoundsHandler>,
}

pub enum FunctionKind {
    Normal,
    GpuKernel {
        backend: SimdBackend,
        dim: u8,
        grid_size: Option<HirExpr>,
        group_size: Option<HirExpr>,
    },
    Async,
    Generator,
}

pub struct BoundsPolicy {
    pub default_action: BoundsAction,
    pub strict: bool,
}

pub enum BoundsAction {
    Return,   // Early exit thread
    Trap,     // Abort kernel
    Panic,    // Host-visible error
    Ignore,   // No check (unsafe)
}
```

### 4.2 Indexer Lowering

**User-Defined Indexer:**
```rust
// m[i, j] in rvalue context
HirExpr::IndexerCall {
    base: HirExpr::Var("m"),
    method: "get",
    args: [HirExpr::Var("i"), HirExpr::Var("j")],
}

// m[i, j] = v
HirStmt::IndexerCall {
    base: HirExpr::Var("m"),
    method: "set",
    args: [HirExpr::Var("i"), HirExpr::Var("j"), HirExpr::Var("v")],
}
```

**@indexer Field Forwarding:**
```rust
// buf[i] where buf has @indexer samples field
HirExpr::Index {
    base: HirExpr::FieldAccess {
        object: HirExpr::Var("buf"),
        field: "samples",
    },
    index: HirExpr::Var("i"),
}
```

### 4.3 Neighbor Accessor Lowering

```rust
// x.left_neighbor
HirExpr::Index {
    base: HirExpr::Var("x"),
    index: HirExpr::BinOp {
        op: Sub,
        lhs: HirExpr::Intrinsic(ThisIndex { dim: 0 }),
        rhs: HirExpr::Const(1),
    },
    bounds_check: true,  // Triggers bounds event
}

// x.right_neighbor
HirExpr::Index {
    base: HirExpr::Var("x"),
    index: HirExpr::BinOp {
        op: Add,
        lhs: HirExpr::Intrinsic(ThisIndex { dim: 0 }),
        rhs: HirExpr::Const(1),
    },
    bounds_check: true,
}
```

---

## 5. MIR Stage

### 5.1 GPU/SIMD Instructions

```rust
// src/compiler/src/mir/instructions.rs

pub enum MirInstr {
    // Thread identification
    GpuGlobalId { dest: VReg, dim: u8 },      // this.index(dim)
    GpuLocalId { dest: VReg, dim: u8 },       // this.thread_index(dim)
    GpuGroupId { dest: VReg, dim: u8 },       // this.group_index(dim)

    // Grid dimensions
    GpuGlobalSize { dest: VReg, dim: u8 },
    GpuLocalSize { dest: VReg, dim: u8 },
    GpuNumGroups { dest: VReg, dim: u8 },

    // Synchronization
    GpuBarrier,
    GpuMemFence { scope: FenceScope },

    // Shared memory
    GpuSharedAlloc { dest: VReg, size: usize, align: usize },

    // Bounds checking
    BoundsCheck { index: VReg, len: VReg, on_fail: BlockId },

    // Indexer calls
    IndexerGet { dest: VReg, base: VReg, method: String, args: Vec<VReg> },
    IndexerSet { base: VReg, method: String, args: Vec<VReg>, value: VReg },

    // ... other instructions
}
```

### 5.2 Example MIR for vector_add

```
fn vector_add(a: *f32, b: *f32, out: *f32, len: i64):
    block0:
        %gid = GpuGlobalId(dim: 0)
        %len_val = Load(len)
        %in_bounds = ICmp(Lt, %gid, %len_val)
        CondBr(%in_bounds, block1, block_exit)

    block1:
        %a_ptr = GepInbounds(a, %gid)
        %a_val = Load(%a_ptr)
        %b_ptr = GepInbounds(b, %gid)
        %b_val = Load(%b_ptr)
        %sum = FAdd(%a_val, %b_val)
        %out_ptr = GepInbounds(out, %gid)
        Store(%out_ptr, %sum)
        Br(block_exit)

    block_exit:
        Return
```

### 5.3 Example MIR for Matrix with Indexer

```
fn matrix_add(a: *Matrix, b: *Matrix, out: *Matrix):
    block0:
        %i = GpuGlobalId(dim: 0)    # row
        %j = GpuGlobalId(dim: 1)    # col

        # a[i, j] -> a.get(i, j)
        %a_val = IndexerGet(base: a, method: "get", args: [%i, %j])

        # b[i, j] -> b.get(i, j)
        %b_val = IndexerGet(base: b, method: "get", args: [%i, %j])

        %sum = FAdd(%a_val, %b_val)

        # out[i, j] = sum -> out.set(i, j, sum)
        IndexerSet(base: out, method: "set", args: [%i, %j], value: %sum)

        Return
```

### 5.4 Example MIR for Neighbor Accessors

```
fn blur_1d(x: *f32, out: *f32, len: i64):
    block0:
        %i = GpuGlobalId(dim: 0)

        # Bounds check for i-1 (left_neighbor)
        %left_idx = ISub(%i, 1)
        %left_valid = ICmp(Gte, %left_idx, 0)
        CondBr(%left_valid, block_check_right, block_exit)

    block_check_right:
        # Bounds check for i+1 (right_neighbor)
        %right_idx = IAdd(%i, 1)
        %right_valid = ICmp(Lt, %right_idx, len)
        CondBr(%right_valid, block_compute, block_exit)

    block_compute:
        %left_ptr = GepInbounds(x, %left_idx)
        %left_val = Load(%left_ptr)

        %mid_ptr = GepInbounds(x, %i)
        %mid_val = Load(%mid_ptr)

        %right_ptr = GepInbounds(x, %right_idx)
        %right_val = Load(%right_ptr)

        %sum = FAdd(%left_val, %mid_val)
        %sum2 = FAdd(%sum, %right_val)
        %avg = FDiv(%sum2, 3.0)

        %out_ptr = GepInbounds(out, %i)
        Store(%out_ptr, %avg)
        Br(block_exit)

    block_exit:
        Return
```

---

## 6. TBB Backend Code Generation

### 6.1 Generated C++ Structure

```cpp
// Generated: kernel_vector_add.cpp

#include <tbb/tbb.h>
#include <tbb/spin_barrier.h>
#include <cstdint>
#include <cstring>

namespace simple_tbb {

//============================================================================
// Kernel Context (injected into each thread)
//============================================================================
struct KernelContext {
    // Thread identification (1D, 2D, 3D)
    int64_t global_id[3];      // this.index(dim)
    int64_t local_id[3];       // this.thread_index(dim)
    int64_t group_id[3];       // this.group_index(dim)

    // Grid dimensions
    int64_t global_size[3];
    int64_t local_size[3];
    int64_t num_groups[3];

    // Synchronization
    tbb::spin_barrier* barrier;

    // Shared memory (per-group)
    void* shared_mem;
    size_t shared_mem_size;
};

// Thread-local context pointer
thread_local KernelContext* g_ctx = nullptr;

//============================================================================
// Intrinsic Implementations
//============================================================================
inline int64_t this_index(int dim = 0) {
    return g_ctx->global_id[dim];
}

inline int64_t thread_index(int dim = 0) {
    return g_ctx->local_id[dim];
}

inline int64_t group_index(int dim = 0) {
    return g_ctx->group_id[dim];
}

inline int64_t global_size(int dim = 0) {
    return g_ctx->global_size[dim];
}

inline int64_t local_size(int dim = 0) {
    return g_ctx->local_size[dim];
}

inline void barrier() {
    if (g_ctx->barrier) {
        g_ctx->barrier->wait();
    }
}

template<typename T>
inline T* shared_alloc(size_t count) {
    // Shared memory is pre-allocated per group
    return static_cast<T*>(g_ctx->shared_mem);
}

//============================================================================
// Neighbor Access Helpers
//============================================================================
template<typename T>
inline T left_neighbor(const T* arr, int64_t current_idx) {
    return arr[current_idx - 1];
}

template<typename T>
inline T right_neighbor(const T* arr, int64_t current_idx) {
    return arr[current_idx + 1];
}

//============================================================================
// Indexer Support
//============================================================================

// User-defined indexer interface
template<typename T, typename... IndexTypes>
struct Indexer {
    virtual T get(IndexTypes... indices) const = 0;
    virtual void set(IndexTypes... indices, T value) = 0;
    virtual bool bounds_check(IndexTypes... indices) const = 0;
};

// Matrix indexer example (generated from Simple class)
struct Matrix {
    float* data;
    int32_t width;
    int32_t height;

    float get(int32_t i, int32_t j) const {
        return data[i * width + j];
    }

    void set(int32_t i, int32_t j, float v) {
        data[i * width + j] = v;
    }

    bool bounds_check(int32_t i, int32_t j) const {
        return i >= 0 && i < height && j >= 0 && j < width;
    }
};

// @indexer field forwarding (generated)
struct AudioBuffer {
    float* samples;  // @indexer
    int32_t sample_rate;

    // Forwarded indexer
    float& operator[](int64_t i) { return samples[i]; }
    const float& operator[](int64_t i) const { return samples[i]; }
};

} // namespace simple_tbb
```

### 6.2 Generated Kernel Body

```cpp
// Generated from: fn vector_add(a: f32[], b: f32[], out: f32[])

namespace simple_tbb {

void vector_add_body(float* a, float* b, float* out, int64_t len) {
    // %gid = GpuGlobalId(dim: 0)
    int64_t i = this_index(0);

    // Bounds check (implicit from @bounds(default=return))
    if (i >= len) {
        return;
    }

    // %a_val = Load(a[i])
    float a_val = a[i];

    // %b_val = Load(b[i])
    float b_val = b[i];

    // %sum = FAdd
    float sum = a_val + b_val;

    // Store(out[i], sum)
    out[i] = sum;
}

} // namespace simple_tbb
```

### 6.3 Generated Kernel with Indexer

```cpp
// Generated from: fn matrix_add(a: Matrix, b: Matrix, out: Matrix)

namespace simple_tbb {

void matrix_add_body(Matrix* a, Matrix* b, Matrix* out) {
    // %i = GpuGlobalId(dim: 0)
    int32_t i = static_cast<int32_t>(this_index(0));

    // %j = GpuGlobalId(dim: 1)
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
