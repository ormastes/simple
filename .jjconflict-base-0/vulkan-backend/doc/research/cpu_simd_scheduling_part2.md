# CPU SIMD Scheduling - Part 2: Implementation Details

**Part of:** [CPU SIMD Scheduling](./cpu_simd_scheduling_part1.md)

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

- [gpu_simd.md](../spec/gpu_simd.md) - GPU/SIMD specification
- [simd_to_tbb_transformation.md](simd_to_tbb_transformation.md) - TBB transformation details
- [cuda_tbb_entry_compare.md](cuda_tbb_entry_compare.md) - CUDA vs TBB comparison
- [codegen_status.md](../codegen_status.md) - MIR instruction coverage
