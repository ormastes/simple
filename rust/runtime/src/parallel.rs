//! CPU parallel execution backend using Rayon.
//!
//! This module provides FFI functions for `@simd` kernels that execute
//! on CPU using Rayon's work-stealing parallel scheduler. It provides
//! the same programming model as GPU kernels but runs on CPU cores.
//!
//! # Architecture
//!
//! ```text
//! Simple @simd fn → MIR → Cranelift/LLVM → Native Code
//!                                              ↓
//!                                    rt_par_launch_1d(kernel_ptr, n, block)
//!                                              ↓
//!                                    Rayon: (0..n).into_par_iter()
//!                                              ↓
//!                                    Work-stealing across CPU cores
//! ```
//!
//! # FFI Functions
//!
//! | Function | Description |
//! |----------|-------------|
//! | `rt_par_global_id(dim)` | Get global work item index |
//! | `rt_par_local_id(dim)` | Get local index within group |
//! | `rt_par_group_id(dim)` | Get work group index |
//! | `rt_par_global_size(dim)` | Get total work items |
//! | `rt_par_local_size(dim)` | Get work group size |
//! | `rt_par_num_groups(dim)` | Get number of work groups |
//! | `rt_par_barrier()` | Synchronize threads in group |
//! | `rt_par_shared_alloc(size, align)` | Allocate shared memory |
//! | `rt_par_launch_1d(kernel, n, block)` | Launch 1D kernel |
//! | `rt_par_launch(kernel, gx, gy, gz, lx, ly, lz)` | Launch 3D kernel |

#[cfg(feature = "cpu-simd")]
use rayon::prelude::*;

use std::cell::RefCell;
use std::sync::atomic::{AtomicI64, Ordering};
use std::sync::{Arc, Barrier};

// =============================================================================
// Kernel Context (Thread-Local State)
// =============================================================================

/// Kernel execution context for each work item.
/// Stored in thread-local storage during kernel execution.
#[derive(Debug, Clone, Default)]
pub struct KernelContext {
    /// Global work item ID (x, y, z)
    pub global_id: [i64; 3],
    /// Local work item ID within group (x, y, z)
    pub local_id: [i64; 3],
    /// Work group ID (x, y, z)
    pub group_id: [i64; 3],
    /// Total global size (work items per dimension)
    pub global_size: [i64; 3],
    /// Work group size
    pub local_size: [i64; 3],
    /// Number of work groups
    pub num_groups: [i64; 3],
}

// Thread-local kernel context
thread_local! {
    static KERNEL_CTX: RefCell<KernelContext> = RefCell::new(KernelContext::default());
    static GROUP_BARRIER: RefCell<Option<Arc<Barrier>>> = const { RefCell::new(None) };
    static SHARED_MEMORY: RefCell<Vec<u8>> = const { RefCell::new(Vec::new()) };
}

/// Set the kernel context for current thread.
fn set_kernel_context(ctx: KernelContext) {
    KERNEL_CTX.with(|c| *c.borrow_mut() = ctx);
}

/// Set the group barrier for current thread.
fn set_group_barrier(barrier: Option<Arc<Barrier>>) {
    GROUP_BARRIER.with(|b| *b.borrow_mut() = barrier);
}

// =============================================================================
// FFI Functions: Work Item Identification
// =============================================================================

/// Get global work item ID for dimension (0=x, 1=y, 2=z).
/// Equivalent to CUDA's `blockIdx.x * blockDim.x + threadIdx.x`.
#[no_mangle]
pub extern "C" fn rt_par_global_id(dim: u32) -> i64 {
    KERNEL_CTX.with(|ctx| {
        let c = ctx.borrow();
        c.global_id[(dim as usize).min(2)]
    })
}

/// Get local work item ID within work group.
/// Equivalent to CUDA's `threadIdx`.
#[no_mangle]
pub extern "C" fn rt_par_local_id(dim: u32) -> i64 {
    KERNEL_CTX.with(|ctx| {
        let c = ctx.borrow();
        c.local_id[(dim as usize).min(2)]
    })
}

/// Get work group ID.
/// Equivalent to CUDA's `blockIdx`.
#[no_mangle]
pub extern "C" fn rt_par_group_id(dim: u32) -> i64 {
    KERNEL_CTX.with(|ctx| {
        let c = ctx.borrow();
        c.group_id[(dim as usize).min(2)]
    })
}

/// Get global work size (total work items in dimension).
/// Equivalent to CUDA's `gridDim * blockDim`.
#[no_mangle]
pub extern "C" fn rt_par_global_size(dim: u32) -> i64 {
    KERNEL_CTX.with(|ctx| {
        let c = ctx.borrow();
        c.global_size[(dim as usize).min(2)]
    })
}

/// Get work group size.
/// Equivalent to CUDA's `blockDim`.
#[no_mangle]
pub extern "C" fn rt_par_local_size(dim: u32) -> i64 {
    KERNEL_CTX.with(|ctx| {
        let c = ctx.borrow();
        c.local_size[(dim as usize).min(2)]
    })
}

/// Get number of work groups.
/// Equivalent to CUDA's `gridDim`.
#[no_mangle]
pub extern "C" fn rt_par_num_groups(dim: u32) -> i64 {
    KERNEL_CTX.with(|ctx| {
        let c = ctx.borrow();
        c.num_groups[(dim as usize).min(2)]
    })
}

// =============================================================================
// FFI Functions: Synchronization
// =============================================================================

/// Work group barrier - synchronize all work items in the group.
/// Equivalent to CUDA's `__syncthreads()`.
#[no_mangle]
pub extern "C" fn rt_par_barrier() {
    GROUP_BARRIER.with(|b| {
        if let Some(barrier) = b.borrow().as_ref() {
            barrier.wait();
        }
    });
}

/// Memory fence - ensure memory ordering.
#[no_mangle]
pub extern "C" fn rt_par_mem_fence(_scope: u32) {
    std::sync::atomic::fence(Ordering::SeqCst);
}

// =============================================================================
// FFI Functions: Shared Memory
// =============================================================================

/// Allocate shared memory (work group local memory).
/// Returns pointer to the allocated memory.
#[no_mangle]
pub extern "C" fn rt_par_shared_alloc(size: u64, _align: u64) -> *mut u8 {
    SHARED_MEMORY.with(|mem| {
        let mut mem = mem.borrow_mut();
        let offset = mem.len();
        mem.resize(offset + size as usize, 0);
        mem.as_mut_ptr().wrapping_add(offset)
    })
}

/// Reset shared memory (call at start of each work group).
#[no_mangle]
pub extern "C" fn rt_par_shared_reset() {
    SHARED_MEMORY.with(|mem| {
        mem.borrow_mut().clear();
    });
}

// =============================================================================
// Kernel Launch: Sequential Fallback (when cpu-simd feature is disabled)
// =============================================================================

/// Kernel function type.
pub type KernelFn = extern "C" fn();

/// Decode linear index to 3D coordinates.
fn decode_3d(linear: i64, dims: [i64; 3]) -> [i64; 3] {
    let z = linear / (dims[0] * dims[1]);
    let rem = linear % (dims[0] * dims[1]);
    let y = rem / dims[0];
    let x = rem % dims[0];
    [x, y, z]
}

/// Execute kernel sequentially (fallback when Rayon is disabled).
#[cfg(not(feature = "cpu-simd"))]
fn execute_kernel_parallel(kernel: KernelFn, global_size: [i64; 3], local_size: [i64; 3]) {
    let num_groups = [
        (global_size[0] + local_size[0] - 1) / local_size[0],
        (global_size[1] + local_size[1] - 1) / local_size[1],
        (global_size[2] + local_size[2] - 1) / local_size[2],
    ];
    let total_groups = num_groups[0] * num_groups[1] * num_groups[2];
    let threads_per_group = local_size[0] * local_size[1] * local_size[2];

    for group_linear in 0..total_groups {
        let group_id = decode_3d(group_linear, num_groups);

        // Reset shared memory for this group
        rt_par_shared_reset();

        for local_linear in 0..threads_per_group {
            let local_id = decode_3d(local_linear, local_size);
            let global_id = [
                group_id[0] * local_size[0] + local_id[0],
                group_id[1] * local_size[1] + local_id[1],
                group_id[2] * local_size[2] + local_id[2],
            ];

            // Skip out-of-bounds
            if global_id[0] >= global_size[0] || global_id[1] >= global_size[1] || global_id[2] >= global_size[2] {
                continue;
            }

            set_kernel_context(KernelContext {
                global_id,
                local_id,
                group_id,
                global_size,
                local_size,
                num_groups,
            });

            kernel();
        }
    }
}

// =============================================================================
// Kernel Launch: Parallel Execution with Rayon
// =============================================================================

/// Execute kernel in parallel using Rayon's work-stealing scheduler.
#[cfg(feature = "cpu-simd")]
fn execute_kernel_parallel(kernel: KernelFn, global_size: [i64; 3], local_size: [i64; 3]) {
    let num_groups = [
        (global_size[0] + local_size[0] - 1) / local_size[0],
        (global_size[1] + local_size[1] - 1) / local_size[1],
        (global_size[2] + local_size[2] - 1) / local_size[2],
    ];
    let total_groups = num_groups[0] * num_groups[1] * num_groups[2];
    let threads_per_group = (local_size[0] * local_size[1] * local_size[2]) as usize;

    // Parallel over work groups
    (0..total_groups).into_par_iter().for_each(|group_linear| {
        let group_id = decode_3d(group_linear, num_groups);

        // Reset shared memory for this group
        rt_par_shared_reset();

        // Create barrier for this group
        let barrier = if threads_per_group > 1 {
            Some(Arc::new(Barrier::new(threads_per_group)))
        } else {
            None
        };

        // Parallel over threads within group
        (0..threads_per_group as i64).into_par_iter().for_each(|local_linear| {
            let local_id = decode_3d(local_linear, local_size);
            let global_id = [
                group_id[0] * local_size[0] + local_id[0],
                group_id[1] * local_size[1] + local_id[1],
                group_id[2] * local_size[2] + local_id[2],
            ];

            // Skip out-of-bounds
            if global_id[0] >= global_size[0] || global_id[1] >= global_size[1] || global_id[2] >= global_size[2] {
                return;
            }

            // Set thread-local context
            set_kernel_context(KernelContext {
                global_id,
                local_id,
                group_id,
                global_size,
                local_size,
                num_groups,
            });
            set_group_barrier(barrier.clone());

            // Execute kernel
            kernel();

            // Clear barrier
            set_group_barrier(None);
        });
    });
}

// =============================================================================
// FFI Functions: Kernel Launch
// =============================================================================

/// Launch a 1D kernel.
///
/// # Arguments
/// * `kernel_ptr` - Function pointer to the kernel
/// * `global_size` - Total number of work items
/// * `local_size` - Work group size (block size)
///
/// # Returns
/// 0 on success
#[no_mangle]
pub extern "C" fn rt_par_launch_1d(kernel_ptr: u64, global_size: i64, local_size: i64) -> i32 {
    let kernel: KernelFn = unsafe { std::mem::transmute(kernel_ptr) };
    let local = if local_size <= 0 { 256 } else { local_size };
    execute_kernel_parallel(kernel, [global_size, 1, 1], [local, 1, 1]);
    0
}

/// Launch a 3D kernel.
///
/// # Arguments
/// * `kernel_ptr` - Function pointer to the kernel
/// * `gx, gy, gz` - Global work size (total work items per dimension)
/// * `lx, ly, lz` - Local work group size
///
/// # Returns
/// 0 on success
#[no_mangle]
pub extern "C" fn rt_par_launch(kernel_ptr: u64, gx: i64, gy: i64, gz: i64, lx: i64, ly: i64, lz: i64) -> i32 {
    let kernel: KernelFn = unsafe { std::mem::transmute(kernel_ptr) };
    let local_size = [
        if lx <= 0 { 16 } else { lx },
        if ly <= 0 { 16 } else { ly },
        if lz <= 0 { 1 } else { lz },
    ];
    execute_kernel_parallel(kernel, [gx, gy, gz], local_size);
    0
}

// =============================================================================
// Atomic Operations (same interface as GPU backend)
// =============================================================================

/// Atomic add for i64.
#[no_mangle]
pub unsafe extern "C" fn rt_par_atomic_add_i64(ptr: *mut i64, value: i64) -> i64 {
    let atomic = &*(ptr as *const AtomicI64);
    atomic.fetch_add(value, Ordering::SeqCst)
}

/// Atomic subtract for i64.
#[no_mangle]
pub unsafe extern "C" fn rt_par_atomic_sub_i64(ptr: *mut i64, value: i64) -> i64 {
    let atomic = &*(ptr as *const AtomicI64);
    atomic.fetch_sub(value, Ordering::SeqCst)
}

/// Atomic exchange for i64.
#[no_mangle]
pub unsafe extern "C" fn rt_par_atomic_xchg_i64(ptr: *mut i64, value: i64) -> i64 {
    let atomic = &*(ptr as *const AtomicI64);
    atomic.swap(value, Ordering::SeqCst)
}

/// Atomic compare-exchange for i64.
#[no_mangle]
pub unsafe extern "C" fn rt_par_atomic_cmpxchg_i64(ptr: *mut i64, expected: i64, new: i64) -> i64 {
    let atomic = &*(ptr as *const AtomicI64);
    match atomic.compare_exchange(expected, new, Ordering::SeqCst, Ordering::SeqCst) {
        Ok(old) => old,
        Err(old) => old,
    }
}

/// Atomic minimum for i64.
#[no_mangle]
pub unsafe extern "C" fn rt_par_atomic_min_i64(ptr: *mut i64, value: i64) -> i64 {
    let atomic = &*(ptr as *const AtomicI64);
    atomic.fetch_min(value, Ordering::SeqCst)
}

/// Atomic maximum for i64.
#[no_mangle]
pub unsafe extern "C" fn rt_par_atomic_max_i64(ptr: *mut i64, value: i64) -> i64 {
    let atomic = &*(ptr as *const AtomicI64);
    atomic.fetch_max(value, Ordering::SeqCst)
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::AtomicU64;

    #[test]
    fn test_kernel_context() {
        set_kernel_context(KernelContext {
            global_id: [10, 20, 30],
            local_id: [2, 4, 6],
            group_id: [1, 2, 3],
            global_size: [100, 100, 100],
            local_size: [8, 8, 8],
            num_groups: [13, 13, 13],
        });

        assert_eq!(rt_par_global_id(0), 10);
        assert_eq!(rt_par_global_id(1), 20);
        assert_eq!(rt_par_global_id(2), 30);

        assert_eq!(rt_par_local_id(0), 2);
        assert_eq!(rt_par_local_id(1), 4);
        assert_eq!(rt_par_local_id(2), 6);

        assert_eq!(rt_par_group_id(0), 1);
        assert_eq!(rt_par_group_id(1), 2);
        assert_eq!(rt_par_group_id(2), 3);

        assert_eq!(rt_par_global_size(0), 100);
        assert_eq!(rt_par_local_size(0), 8);
        assert_eq!(rt_par_num_groups(0), 13);
    }

    #[test]
    fn test_shared_memory() {
        rt_par_shared_reset();

        let ptr1 = rt_par_shared_alloc(16, 8);
        assert!(!ptr1.is_null());

        let ptr2 = rt_par_shared_alloc(32, 8);
        assert!(!ptr2.is_null());
        assert_ne!(ptr1, ptr2);

        rt_par_shared_reset();
        let ptr3 = rt_par_shared_alloc(16, 8);
        assert!(!ptr3.is_null());
    }

    #[test]
    fn test_kernel_1d_execution() {
        static COUNTER: AtomicU64 = AtomicU64::new(0);
        COUNTER.store(0, Ordering::SeqCst);

        extern "C" fn test_kernel() {
            COUNTER.fetch_add(1, Ordering::SeqCst);
        }

        rt_par_launch_1d(test_kernel as *const () as u64, 100, 32);

        assert_eq!(COUNTER.load(Ordering::SeqCst), 100);
    }

    #[test]
    fn test_decode_3d() {
        assert_eq!(decode_3d(0, [4, 4, 4]), [0, 0, 0]);
        assert_eq!(decode_3d(1, [4, 4, 4]), [1, 0, 0]);
        assert_eq!(decode_3d(4, [4, 4, 4]), [0, 1, 0]);
        assert_eq!(decode_3d(16, [4, 4, 4]), [0, 0, 1]);
        assert_eq!(decode_3d(21, [4, 4, 4]), [1, 1, 1]);
    }

    #[test]
    fn test_atomic_add() {
        let mut value: i64 = 10;
        unsafe {
            let old = rt_par_atomic_add_i64(&mut value, 5);
            assert_eq!(old, 10);
            assert_eq!(value, 15);
        }
    }
}
