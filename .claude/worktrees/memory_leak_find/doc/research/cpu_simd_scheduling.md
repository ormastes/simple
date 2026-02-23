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


---


### 3.4 Barrier Synchronization

```rust
// src/runtime/src/parallel/barrier.rs

use std::sync::{Arc, Barrier};
use std::cell::RefCell;

thread_local! {
    static GROUP_BARRIER: RefCell<Option<Arc<Barrier>>> = RefCell::new(None);
}

/// Set the barrier for the current work group
pub fn set_group_barrier(barrier: Arc<Barrier>) {
    GROUP_BARRIER.with(|b| {
        *b.borrow_mut() = Some(barrier);
    });
}

/// Synchronize all threads in the current work group
/// Equivalent to CUDA's __syncthreads() or OpenCL's barrier()
pub fn thread_group_barrier() {
    GROUP_BARRIER.with(|b| {
        if let Some(barrier) = b.borrow().as_ref() {
            barrier.wait();
        }
    });
}
```

### 3.5 Shared Memory

```rust
// src/runtime/src/parallel/shared_mem.rs

use std::cell::RefCell;
use std::alloc::{alloc_zeroed, dealloc, Layout};

thread_local! {
    static SHARED_MEM: RefCell<SharedMemory> = RefCell::new(SharedMemory::new());
}

struct SharedMemory {
    ptr: *mut u8,
    size: usize,
    offset: usize,
}

impl SharedMemory {
    fn new() -> Self {
        Self {
            ptr: std::ptr::null_mut(),
            size: 0,
            offset: 0,
        }
    }

    fn reset(&mut self, size: usize) {
        if self.size < size {
            if !self.ptr.is_null() {
                unsafe {
                    dealloc(self.ptr, Layout::from_size_align(self.size, 64).unwrap());
                }
            }
            self.ptr = unsafe {
                alloc_zeroed(Layout::from_size_align(size, 64).unwrap())
            };
            self.size = size;
        }
        self.offset = 0;
    }

    fn alloc(&mut self, size: usize, align: usize) -> *mut u8 {
        let aligned_offset = (self.offset + align - 1) & !(align - 1);
        if aligned_offset + size > self.size {
            panic!("Shared memory overflow");
        }
        let ptr = unsafe { self.ptr.add(aligned_offset) };
        self.offset = aligned_offset + size;
        ptr
    }
}

/// Reset shared memory for new work group
pub fn shared_reset(size: usize) {
    SHARED_MEM.with(|m| m.borrow_mut().reset(size));
}

/// Allocate from shared memory
pub fn shared_alloc(size: usize, align: usize) -> *mut u8 {
    SHARED_MEM.with(|m| m.borrow_mut().alloc(size, align))
}
```

---

## 4. FFI Interface

### 4.1 Runtime FFI Functions

```rust
// src/runtime/src/parallel/ffi.rs

use super::{context, executor, barrier, shared_mem};

/// Get global work item ID
#[no_mangle]
pub extern "C" fn rt_par_global_id(dim: u32) -> i64 {
    context::this_index(dim as usize)
}

/// Get local work item ID
#[no_mangle]
pub extern "C" fn rt_par_local_id(dim: u32) -> i64 {
    context::thread_index(dim as usize)
}

/// Get work group ID
#[no_mangle]
pub extern "C" fn rt_par_group_id(dim: u32) -> i64 {
    context::group_index(dim as usize)
}

/// Synchronize threads in work group
#[no_mangle]
pub extern "C" fn rt_par_barrier() {
    barrier::thread_group_barrier();
}

/// Allocate shared memory
#[no_mangle]
pub extern "C" fn rt_par_shared_alloc(size: u64, align: u64) -> *mut u8 {
    shared_mem::shared_alloc(size as usize, align as usize)
}

/// Launch 1D kernel
#[no_mangle]
pub extern "C" fn rt_par_launch_1d(
    kernel_ptr: u64,
    global_size: i64,
    local_size: i64,
) -> i32 {
    let kernel: executor::KernelFn = unsafe { std::mem::transmute(kernel_ptr) };
    executor::launch_1d(kernel, global_size, local_size);
    0
}

/// Launch 3D kernel
#[no_mangle]
pub extern "C" fn rt_par_launch(
    kernel_ptr: u64,
    gx: i64, gy: i64, gz: i64,
    lx: i64, ly: i64, lz: i64,
) -> i32 {
    let kernel: executor::KernelFn = unsafe { std::mem::transmute(kernel_ptr) };
    let config = executor::LaunchConfig {
        global_size: [gx, gy, gz],
        local_size: [lx, ly, lz],
        shared_mem_size: 0,
    };
    executor::launch_parallel(kernel, &config);
    0
}
```

### 4.2 Codegen FFI Mapping

| MIR Instruction | FFI Function | Signature |
|-----------------|--------------|-----------|
| `GpuGlobalId(dim)` | `rt_par_global_id` | `(u32) -> i64` |
| `GpuLocalId(dim)` | `rt_par_local_id` | `(u32) -> i64` |
| `GpuGroupId(dim)` | `rt_par_group_id` | `(u32) -> i64` |
| `GpuBarrier` | `rt_par_barrier` | `() -> ()` |
| `GpuSharedAlloc(size)` | `rt_par_shared_alloc` | `(u64, u64) -> *u8` |
| Kernel launch | `rt_par_launch_1d` | `(u64, i64, i64) -> i32` |

---

## 5. Codegen Integration

### 5.1 Backend Selection

```rust
// src/compiler/src/codegen/mod.rs

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SimdBackend {
    /// GPU execution (CUDA/PTX)
    Gpu,
    /// CPU parallel execution (Rayon/TBB-style)
    CpuParallel,
    /// Sequential software execution (testing)
    Software,
    /// Auto-select based on availability
    Auto,
}

impl SimdBackend {
    pub fn select_runtime_ffi(&self) -> &'static str {
        match self {
            SimdBackend::Gpu => "rt_gpu_",
            SimdBackend::CpuParallel => "rt_par_",
            SimdBackend::Software => "rt_gpu_",  // Reuse sequential
            SimdBackend::Auto => "rt_par_",      // Default to parallel
        }
    }
}
```

### 5.2 MIR to FFI Lowering

```rust
// src/compiler/src/codegen/instr.rs (additions)

fn compile_gpu_intrinsic(&mut self, instr: &MirInstr) -> Result<()> {
    let prefix = self.backend.select_runtime_ffi();

    match instr {
        MirInstr::GpuGlobalId { dest, dim } => {
            // Call rt_par_global_id(dim) or rt_gpu_global_id(dim)
            let func = format!("{}global_id", prefix);
            self.emit_call(dest, &func, &[*dim as i64]);
        }
        MirInstr::GpuLocalId { dest, dim } => {
            let func = format!("{}local_id", prefix);
            self.emit_call(dest, &func, &[*dim as i64]);
        }
        MirInstr::GpuBarrier => {
            let func = format!("{}barrier", prefix);
            self.emit_call_void(&func, &[]);
        }
        // ... other instructions
    }
    Ok(())
}
```

### 5.3 Kernel Launch Generation

For `@simd` functions, the codegen generates:

1. **Kernel body function**: The transformed kernel code
2. **Launch wrapper**: Calls `rt_par_launch_1d` or `rt_par_launch`

```rust
// Generated for: @simd fn vector_add(a: f32[], b: f32[], out: f32[])

// 1. Kernel body (called per work item)
extern "C" fn vector_add_kernel(a: *const f32, b: *const f32, out: *mut f32, len: i64) {
    let i = rt_par_global_id(0);
    if i < len {
        unsafe {
            *out.offset(i as isize) = *a.offset(i as isize) + *b.offset(i as isize);
        }
    }
}

// 2. Launch wrapper (called by user)
pub fn vector_add(a: &[f32], b: &[f32], out: &mut [f32]) {
    let len = out.len() as i64;
    let block_size = 256;
    rt_par_launch_1d(
        vector_add_kernel as u64,
        len,
        block_size,
    );
}
```

---

## 6. Example Transformations

### 6.1 Simple Vector Add

**Simple source:**
```simple
@simd
fn vector_add(a: f32[], b: f32[], out: f32[]):
    let i = this.index()
    out[i] = a[i] + b[i]
```

**Generated execution flow:**
```
User calls vector_add(a, b, out)
    │
    ▼
rt_par_launch_1d(kernel_ptr, len, 256)
    │
    ▼
Rayon: (0..num_groups).into_par_iter()
    │
    ├── Group 0: threads 0-255
    │     ├── Thread 0: KERNEL_CTX.global_id = [0,0,0], execute kernel
    │     ├── Thread 1: KERNEL_CTX.global_id = [1,0,0], execute kernel
    │     └── ...
    │
    ├── Group 1: threads 256-511
    │     └── ...
    │
    └── Group N: remaining threads
```

### 6.2 Reduction with Shared Memory

**Simple source:**
```simple
@simd
fn reduce_sum(input: f32[], output: f32[]):
    shared let local_data: [f32; 256]

    let gid = this.index()
    let lid = this.thread_index()

    local_data[lid] = input[gid]
    thread_group.barrier()

    # Parallel reduction
    let mut stride = 128
    while stride > 0:
        if lid < stride:
            local_data[lid] += local_data[lid + stride]
        thread_group.barrier()
        stride /= 2

    if lid == 0:
        output[this.group_index()] = local_data[0]
```

**Generated with barrier support:**
```rust
fn reduce_sum_kernel(input: *const f32, output: *mut f32, len: i64) {
    // Shared memory allocation
    let local_data: *mut f32 = rt_par_shared_alloc(256 * 4, 4) as *mut f32;

    let gid = rt_par_global_id(0);
    let lid = rt_par_local_id(0);

    // Load to shared
    unsafe {
        *local_data.offset(lid as isize) = if gid < len {
            *input.offset(gid as isize)
        } else {
            0.0
        };
    }

    rt_par_barrier();

    // Reduction
    let mut stride = 128i64;
    while stride > 0 {
        if lid < stride {
            unsafe {
                let val = *local_data.offset(lid as isize)
                        + *local_data.offset((lid + stride) as isize);
                *local_data.offset(lid as isize) = val;
            }
        }
        rt_par_barrier();
        stride /= 2;
    }

    // Write result
    if lid == 0 {
        let group_id = rt_par_group_id(0);
        unsafe {
            *output.offset(group_id as isize) = *local_data;
        }
    }
}
```

### 6.3 2D Matrix Operation

**Simple source:**
```simple
@simd(dim=2)
fn matrix_add(a: Matrix, b: Matrix, out: Matrix):
    let i = this.index(0)  # row
    let j = this.index(1)  # col
    out[i, j] = a[i, j] + b[i, j]
```

**Launch configuration:**
```rust
// 2D launch: global_size = [height, width], local_size = [16, 16]
rt_par_launch(
    matrix_add_kernel as u64,
    height, width, 1,  // global size
    16, 16, 1,         // local size (16x16 tiles)
);
```

---

## 7. Performance Characteristics

### 7.1 Comparison: GPU vs CPU Parallel

| Aspect | GPU (CUDA) | CPU Parallel (Rayon) |
|--------|------------|---------------------|
| Thread count | 10,000 - 1,000,000 | 4 - 128 (core count) |
| Thread overhead | ~0 (hardware) | ~1-10 μs per task |
| Shared memory | Fast SRAM (32KB) | L1/L2 cache |
| Barrier latency | ~20 cycles | ~1000 cycles |
| Memory bandwidth | ~1 TB/s | ~50-100 GB/s |
| Best for | Massive parallelism | Moderate parallelism |

### 7.2 Optimization Guidelines

1. **Block size**: Use 64-256 for CPU (matches cache lines)
2. **Avoid fine-grained barriers**: CPU barriers are expensive
3. **Prefer coarse parallelism**: Larger work items per thread
4. **Memory locality**: Access patterns affect cache performance

---

## 8. Implementation Phases

### Phase 1: Core Infrastructure
- [ ] Add `rayon` dependency to `simple-runtime`
- [ ] Create `src/runtime/src/parallel/` module structure
- [ ] Implement `KernelContext` and thread-local storage
- [ ] Implement `launch_parallel()` with Rayon

### Phase 2: FFI Integration
- [ ] Add FFI functions (`rt_par_*`)
- [ ] Update codegen to use parallel FFI prefix
- [ ] Add backend selection logic

### Phase 3: Synchronization
- [ ] Implement barrier synchronization
- [ ] Implement shared memory allocation
- [ ] Test reduction patterns

### Phase 4: Testing
- [ ] Unit tests for parallel executor
- [ ] Integration tests for @simd kernels
- [ ] Performance benchmarks vs sequential

---

## 9. Dependencies

### Cargo.toml Addition

```toml
[dependencies]
rayon = "1.10"
```

### Why Rayon Instead of TBB?

| Aspect | Rayon | TBB |
|--------|-------|-----|
| Language | Pure Rust | C++ (requires FFI) |
| Integration | Native crate | Build complexity |
| Scheduler | Work-stealing | Work-stealing |
| Performance | Comparable | Comparable |
| Maintenance | Active | Active |

Rayon provides the same work-stealing algorithm as TBB without C++ FFI complexity.

---

## 10. Related Documents

- [gpu_simd/README.md](../spec/gpu_simd/README.md) - GPU/SIMD specification
- [simd_to_tbb_transformation.md](simd_to_tbb_transformation.md) - TBB transformation details
- [cuda_tbb_entry_compare.md](cuda_tbb_entry_compare.md) - CUDA vs TBB comparison
- [codegen_status.md](../codegen_status.md) - MIR instruction coverage
