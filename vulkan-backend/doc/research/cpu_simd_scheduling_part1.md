# CPU Scheduling for @simd Kernels (TBB-Style)

**Version:** 2025-12
**Status:** Design Document
**Purpose:** Specify how Simple's `@simd` kernels execute on CPU using TBB-style work-stealing scheduler

---

## 1. Overview

This document describes how Simple's `@simd` annotated functions can execute on CPU with parallel scheduling, providing the same programming model as GPU execution but running on CPU cores.

### Key Insight: No Source Code Generation

**Important:** Simple `@simd` functions are NOT transformed to Rust or C++ source code. They go through the existing compilation pipeline:

```
Simple @simd fn → AST → HIR → MIR → Cranelift → Native Machine Code
```

The only difference is:
- MIR contains GPU-style instructions (`GpuGlobalId`, `GpuBarrier`, etc.)
- These compile to FFI calls into the Rust runtime
- Runtime uses Rayon for parallel execution

### Execution Backends

```
@simd kernel
     │
     ├── GPU Backend (CUDA/PTX) ─── NVIDIA GPU execution
     │
     ├── CPU Parallel Backend ───── TBB-style work-stealing (this document)
     │
     └── Software Backend ───────── Sequential (existing, for testing)
```

### Design Goals

1. **Same API**: `@simd` kernels work unchanged across backends
2. **Work-stealing**: Efficient load balancing like TBB/Rayon
3. **Rust-native**: Use Rayon (Rust's TBB equivalent) - no C++ FFI
4. **Incremental**: Extend existing `gpu.rs` infrastructure

---

## 2. Why Rayon Instead of TBB?

### The Problem with TBB

TBB is a **C++ library**. Using it requires:

```
Simple @simd fn
      │
      ▼
   Cranelift → Native kernel code
      │
      ▼
   Launch needs TBB... but TBB is C++!
      │
      ▼
   ┌─────────────────────────────────────────────┐
   │ REQUIRED: C++ glue layer                    │
   │                                             │
   │ // tbb_runtime.cpp                          │
   │ #include <tbb/tbb.h>                        │
   │                                             │
   │ extern "C" void rt_tbb_launch(              │
   │     void* kernel_ptr, int64_t n, int64_t b  │
   │ ) {                                         │
   │     tbb::parallel_for(                      │
   │         tbb::blocked_range<int64_t>(0, n),  │
   │         [=](auto& r) {                      │
   │             for (auto i = r.begin(); ...)   │
   │                 ((void(*)())kernel_ptr)();  │
   │         }                                   │
   │     );                                      │
   │ }                                           │
   └─────────────────────────────────────────────┘
      │
      ▼
   Build complexity:
   - C++ compiler required
   - Link TBB shared library
   - Rust ↔ C++ FFI
   - Platform-specific .so/.dylib/.dll
```

### The Rayon Solution

Rayon is a **Rust library** with the same work-stealing algorithm:

```
Simple @simd fn
      │
      ▼
   Cranelift → Native kernel code
      │
      ▼
   Launch calls Rayon directly (pure Rust!)
      │
      ▼
   ┌─────────────────────────────────────────────┐
   │ // src/runtime/src/parallel.rs              │
   │                                             │
   │ use rayon::prelude::*;                      │
   │                                             │
   │ #[no_mangle]                                │
   │ pub extern "C" fn rt_par_launch_1d(         │
   │     kernel_ptr: u64, n: i64, block: i64     │
   │ ) {                                         │
   │     let kernel: fn() = unsafe {             │
   │         std::mem::transmute(kernel_ptr)     │
   │     };                                      │
   │     (0..n).into_par_iter().for_each(|i| {   │
   │         THREAD_INDEX.set(i);                │
   │         kernel();                           │
   │     });                                     │
   │ }                                           │
   └─────────────────────────────────────────────┘
      │
      ▼
   Simple:
   - Just add `rayon = "1.10"` to Cargo.toml
   - No C++ compiler needed
   - No external libraries to link
   - Cross-platform automatically
```

### Comparison

| Aspect | TBB | Rayon |
|--------|-----|-------|
| Language | C++ | Rust |
| Integration | FFI + C++ build | Cargo dependency |
| Scheduler | Work-stealing | Work-stealing (same!) |
| Build complexity | High | None |
| Platform support | Manual | Automatic |

---

## 3. Complete Pipeline: Simple @simd to CPU Execution

### 3.1 Pipeline Overview

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    Simple @simd Function Compilation                         │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│  Simple Source                                                               │
│  ┌──────────────────────────────────────┐                                   │
│  │ @simd                                │                                   │
│  │ fn vector_add(a: f32[], b: f32[],    │                                   │
│  │               out: f32[]):           │                                   │
│  │     let i = this.index()             │                                   │
│  │     out[i] = a[i] + b[i]             │                                   │
│  └──────────────────────────────────────┘                                   │
│                       │                                                      │
│                       ▼                                                      │
│  ┌─────────────────────────────────────────────────────────────────────┐    │
│  │                         FRONTEND (shared)                            │    │
│  │  Lexer → Parser → AST → HIR (type-check) → MIR                      │    │
│  └─────────────────────────────────────────────────────────────────────┘    │
│                       │                                                      │
│                       ▼                                                      │
│  MIR with GPU Instructions                                                   │
│  ┌──────────────────────────────────────┐                                   │
│  │ fn vector_add(a: *f32, b: *f32,      │                                   │
│  │               out: *f32, len: i64):  │                                   │
│  │   block0:                            │                                   │
│  │     %i = GpuGlobalId(dim: 0)  ◄───── GPU-style instruction               │
│  │     %cmp = ICmp(Lt, %i, len)         │                                   │
│  │     CondBr(%cmp, block1, exit)       │                                   │
│  │   block1:                            │                                   │
│  │     %a_val = Load(a[%i])             │                                   │
│  │     %b_val = Load(b[%i])             │                                   │
│  │     %sum = FAdd(%a_val, %b_val)      │                                   │
│  │     Store(out[%i], %sum)             │                                   │
│  │   exit:                              │                                   │
│  │     Return                           │                                   │
│  └──────────────────────────────────────┘                                   │
│                       │                                                      │
│           ┌───────────┴───────────┐                                         │
│           │                       │                                         │
│           ▼                       ▼                                         │
│  ┌─────────────────┐    ┌─────────────────┐                                 │
│  │   Cranelift     │    │      LLVM       │                                 │
│  │   Backend       │    │    Backend      │                                 │
│  └────────┬────────┘    └────────┬────────┘                                 │
│           │                       │                                         │
│           ▼                       ▼                                         │
│  ┌─────────────────────────────────────────────────────────────────────┐    │
│  │                    NATIVE MACHINE CODE                               │    │
│  │  (kernel function pointer + launch wrapper)                          │    │
│  └─────────────────────────────────────────────────────────────────────┘    │
│                       │                                                      │
│                       ▼                                                      │
│  ┌─────────────────────────────────────────────────────────────────────┐    │
│  │                    RUNTIME (Rust + Rayon)                            │    │
│  │                                                                       │    │
│  │  rt_par_launch_1d(kernel_ptr, n, block_size)                         │    │
│  │       │                                                               │    │
│  │       ▼                                                               │    │
│  │  Rayon: (0..n).into_par_iter().for_each(|i| kernel())               │    │
│  │       │                                                               │    │
│  │       ▼                                                               │    │
│  │  Work-stealing scheduler distributes to CPU cores                    │    │
│  └─────────────────────────────────────────────────────────────────────┘    │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 3.2 Backend Options

Both Cranelift and LLVM can generate the native kernel code:

| Backend | Use Case | Performance | Compile Speed |
|---------|----------|-------------|---------------|
| **Cranelift** | JIT, fast iteration | Good | Fast |
| **LLVM** | Release, max perf | Best | Slow |

The choice of backend is **orthogonal** to the scheduler. Both backends:
1. Generate native function for kernel body
2. Generate launch code that calls `rt_par_*` FFI functions
3. Runtime (Rayon) handles scheduling

### 3.3 MIR Instruction to FFI Call

During codegen, GPU-style MIR instructions become FFI calls:

```
MIR Instruction          Cranelift/LLVM Output
─────────────────────    ──────────────────────────────────────
GpuGlobalId(dim: 0)  →   call rt_par_global_id(0) → i64
GpuLocalId(dim: 0)   →   call rt_par_local_id(0) → i64
GpuBarrier           →   call rt_par_barrier()
GpuSharedAlloc(256)  →   call rt_par_shared_alloc(256, 8) → *u8
```

### 3.4 Kernel Launch Generation

The compiler generates two pieces:

**1. Kernel Body (native function):**
```
; Generated by Cranelift or LLVM
vector_add_kernel:
    call rt_par_global_id(0)     ; get thread index
    mov %i, %rax
    cmp %i, %len
    jge .exit
    ; ... load, add, store ...
.exit:
    ret
```

**2. Launch Wrapper:**
```
; Calls runtime to schedule kernel
vector_add:
    mov %rdi, vector_add_kernel  ; kernel pointer
    mov %rsi, %len               ; global size
    mov %rdx, 256                ; block size
    call rt_par_launch_1d
    ret
```

### 3.5 Runtime Execution

```rust
// src/runtime/src/parallel.rs

use rayon::prelude::*;

thread_local! {
    static THREAD_INDEX: Cell<i64> = Cell::new(0);
}

#[no_mangle]
pub extern "C" fn rt_par_global_id(dim: u32) -> i64 {
    THREAD_INDEX.with(|t| t.get())
}

#[no_mangle]
pub extern "C" fn rt_par_launch_1d(kernel_ptr: u64, n: i64, _block: i64) {
    let kernel: extern "C" fn() = unsafe { std::mem::transmute(kernel_ptr) };

    (0..n).into_par_iter().for_each(|i| {
        // Set thread-local index before calling kernel
        THREAD_INDEX.with(|t| t.set(i));

        // Execute kernel for this work item
        kernel();
    });
}
```

### 3.6 Summary: What Changes vs Existing GPU Path

| Component | GPU Backend | CPU Parallel Backend |
|-----------|-------------|---------------------|
| Frontend (Parser→MIR) | Same | Same |
| MIR Instructions | Same (`GpuGlobalId`, etc.) | Same |
| Codegen (Cranelift/LLVM) | Same structure | Same structure |
| FFI function prefix | `rt_gpu_*` | `rt_par_*` |
| Runtime implementation | Sequential loops | Rayon `par_iter` |

**The only real difference is the runtime implementation!**

---

## 4. Programming Model Equivalence

### GPU vs CPU Parallel Mapping

| GPU Concept | CPU Parallel Equivalent | Implementation |
|-------------|------------------------|----------------|
| Grid (total threads) | Rayon parallel range | `(0..n).into_par_iter()` |
| Block (thread group) | Chunk of work items | Nested `par_iter` |
| Thread (work item) | Rayon task | Closure execution |
| Shared memory | Per-group stack allocation | Thread-local + barrier |
| `__syncthreads()` | Barrier synchronization | `std::sync::Barrier` |
| Global memory | Shared heap | Normal Rust references |

### Thread Identity Mapping

| Simple Intrinsic | GPU | CPU Parallel |
|-----------------|-----|--------------|
| `this.index()` | `blockIdx * blockDim + threadIdx` | `group_id * group_size + local_id` |
| `this.thread_index()` | `threadIdx` | `local_id` within group |
| `this.group_index()` | `blockIdx` | `group_id` |
| `gpu.global_size()` | `gridDim * blockDim` | Total work items |
| `gpu.local_size()` | `blockDim` | Group size |

---

## 3. Architecture

### 3.1 Runtime Structure

```
src/runtime/src/
├── value/
│   ├── gpu.rs              # Existing software backend (sequential)
│   └── mod.rs              # Re-exports
├── parallel/               # NEW: CPU parallel backend
│   ├── mod.rs              # Module exports
│   ├── context.rs          # KernelContext (thread-local state)
│   ├── executor.rs         # Parallel kernel launcher
│   ├── barrier.rs          # Group barrier synchronization
│   └── shared_mem.rs       # Per-group shared memory
└── lib.rs                  # Add parallel module
```

### 3.2 Kernel Context

```rust
// src/runtime/src/parallel/context.rs

use std::cell::RefCell;

/// Kernel execution context for each work item
#[derive(Debug, Clone, Default)]
pub struct KernelContext {
    /// Global work item ID (x, y, z)
    pub global_id: [i64; 3],
    /// Local work item ID within group
    pub local_id: [i64; 3],
    /// Work group ID
    pub group_id: [i64; 3],
    /// Total global size
    pub global_size: [i64; 3],
    /// Work group size
    pub local_size: [i64; 3],
    /// Number of work groups
    pub num_groups: [i64; 3],
}

// Thread-local context pointer
thread_local! {
    pub static KERNEL_CTX: RefCell<Option<KernelContext>> = RefCell::new(None);
}

/// Get current thread's global index
#[inline]
pub fn this_index(dim: usize) -> i64 {
    KERNEL_CTX.with(|ctx| {
        ctx.borrow()
            .as_ref()
            .map(|c| c.global_id[dim.min(2)])
            .unwrap_or(0)
    })
}

/// Get current thread's local index within group
#[inline]
pub fn thread_index(dim: usize) -> i64 {
    KERNEL_CTX.with(|ctx| {
        ctx.borrow()
            .as_ref()
            .map(|c| c.local_id[dim.min(2)])
            .unwrap_or(0)
    })
}

/// Get current thread's group index
#[inline]
pub fn group_index(dim: usize) -> i64 {
    KERNEL_CTX.with(|ctx| {
        ctx.borrow()
            .as_ref()
            .map(|c| c.group_id[dim.min(2)])
            .unwrap_or(0)
    })
}
```

### 3.3 Parallel Executor

```rust
// src/runtime/src/parallel/executor.rs

use rayon::prelude::*;
use std::sync::{Arc, Barrier};
use super::context::{KernelContext, KERNEL_CTX};

/// Kernel function type
pub type KernelFn = fn();

/// Launch configuration
#[derive(Debug, Clone)]
pub struct LaunchConfig {
    pub global_size: [i64; 3],
    pub local_size: [i64; 3],
    pub shared_mem_size: usize,
}

impl LaunchConfig {
    pub fn new_1d(n: i64, block_size: i64) -> Self {
        Self {
            global_size: [n, 1, 1],
            local_size: [block_size, 1, 1],
            shared_mem_size: 0,
        }
    }

    pub fn new_2d(nx: i64, ny: i64, bx: i64, by: i64) -> Self {
        Self {
            global_size: [nx, ny, 1],
            local_size: [bx, by, 1],
            shared_mem_size: 0,
        }
    }

    fn num_groups(&self) -> [i64; 3] {
        [
            (self.global_size[0] + self.local_size[0] - 1) / self.local_size[0],
            (self.global_size[1] + self.local_size[1] - 1) / self.local_size[1],
            (self.global_size[2] + self.local_size[2] - 1) / self.local_size[2],
        ]
    }

    fn total_groups(&self) -> i64 {
        let ng = self.num_groups();
        ng[0] * ng[1] * ng[2]
    }

    fn threads_per_group(&self) -> i64 {
        self.local_size[0] * self.local_size[1] * self.local_size[2]
    }
}

/// Decode linear index to 3D coordinates
fn decode_3d(linear: i64, dims: [i64; 3]) -> [i64; 3] {
    let z = linear / (dims[0] * dims[1]);
    let rem = linear % (dims[0] * dims[1]);
    let y = rem / dims[0];
    let x = rem % dims[0];
    [x, y, z]
}

/// Launch kernel with TBB-style parallel execution
pub fn launch_parallel(kernel: KernelFn, config: &LaunchConfig) {
    let num_groups = config.num_groups();
    let total_groups = config.total_groups();
    let threads_per_group = config.threads_per_group();
    let global_size = config.global_size;
    let local_size = config.local_size;

    // Parallel over work groups (like TBB parallel_for over blocks)
    (0..total_groups).into_par_iter().for_each(|group_linear| {
        let group_id = decode_3d(group_linear, num_groups);

        // Create barrier for thread synchronization within group
        let barrier = Arc::new(Barrier::new(threads_per_group as usize));

        // Parallel over threads within group
        (0..threads_per_group).into_par_iter().for_each(|local_linear| {
            let local_id = decode_3d(local_linear, local_size);

            // Calculate global ID
            let global_id = [
                group_id[0] * local_size[0] + local_id[0],
                group_id[1] * local_size[1] + local_id[1],
                group_id[2] * local_size[2] + local_id[2],
            ];

            // Skip out-of-bounds threads
            if global_id[0] >= global_size[0]
                || global_id[1] >= global_size[1]
                || global_id[2] >= global_size[2]
            {
                return;
            }

            // Set thread-local context
            KERNEL_CTX.with(|ctx| {
                *ctx.borrow_mut() = Some(KernelContext {
                    global_id,
                    local_id,
                    group_id,
                    global_size,
                    local_size,
                    num_groups,
                });
            });

            // Execute kernel for this work item
            kernel();

            // Clear context
            KERNEL_CTX.with(|ctx| {
                *ctx.borrow_mut() = None;
            });
        });
    });
}

/// Launch 1D kernel (convenience function)
pub fn launch_1d(kernel: KernelFn, n: i64, block_size: i64) {
    launch_parallel(kernel, &LaunchConfig::new_1d(n, block_size));
}

/// Launch 2D kernel (convenience function)
pub fn launch_2d(kernel: KernelFn, nx: i64, ny: i64, bx: i64, by: i64) {
    launch_parallel(kernel, &LaunchConfig::new_2d(nx, ny, bx, by));
}
```

---

**Continued in:** [Part 2](./cpu_simd_scheduling_part2.md)
