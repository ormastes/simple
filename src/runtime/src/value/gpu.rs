//! GPU runtime support for software backend execution.
//!
//! This module provides FFI functions for GPU intrinsics that execute
//! on the CPU using a software emulation approach. Work items are
//! simulated using thread-local state.

use std::cell::RefCell;
use std::sync::atomic::{AtomicI64, AtomicU32, Ordering};

/// GPU work item state for software execution.
/// Each work item in a kernel execution has its own state.
#[derive(Debug, Clone)]
pub struct GpuWorkItemState {
    /// Global work item ID (x, y, z)
    pub global_id: [u32; 3],
    /// Local work item ID within work group (x, y, z)
    pub local_id: [u32; 3],
    /// Work group ID (x, y, z)
    pub group_id: [u32; 3],
    /// Global work size (total work items per dimension)
    pub global_size: [u32; 3],
    /// Local work group size
    pub local_size: [u32; 3],
    /// Number of work groups
    pub num_groups: [u32; 3],
}

impl Default for GpuWorkItemState {
    fn default() -> Self {
        Self {
            global_id: [0, 0, 0],
            local_id: [0, 0, 0],
            group_id: [0, 0, 0],
            global_size: [1, 1, 1],
            local_size: [1, 1, 1],
            num_groups: [1, 1, 1],
        }
    }
}

// Thread-local GPU work item state
thread_local! {
    static WORK_ITEM_STATE: RefCell<GpuWorkItemState> = RefCell::new(GpuWorkItemState::default());
}

/// Set the current work item state for this thread.
pub fn set_work_item_state(state: GpuWorkItemState) {
    WORK_ITEM_STATE.with(|s| {
        *s.borrow_mut() = state;
    });
}

/// Get the current work item state for this thread.
pub fn get_work_item_state() -> GpuWorkItemState {
    WORK_ITEM_STATE.with(|s| s.borrow().clone())
}

// =============================================================================
// GPU Intrinsic FFI Functions (Work Item Identification)
// =============================================================================

/// Get global work item ID for dimension (0=x, 1=y, 2=z)
#[no_mangle]
pub extern "C" fn rt_gpu_global_id(dim: u32) -> u64 {
    WORK_ITEM_STATE.with(|s| {
        let state = s.borrow();
        let idx = (dim as usize).min(2);
        state.global_id[idx] as u64
    })
}

/// Get local work item ID within work group
#[no_mangle]
pub extern "C" fn rt_gpu_local_id(dim: u32) -> u64 {
    WORK_ITEM_STATE.with(|s| {
        let state = s.borrow();
        let idx = (dim as usize).min(2);
        state.local_id[idx] as u64
    })
}

/// Get work group ID
#[no_mangle]
pub extern "C" fn rt_gpu_group_id(dim: u32) -> u64 {
    WORK_ITEM_STATE.with(|s| {
        let state = s.borrow();
        let idx = (dim as usize).min(2);
        state.group_id[idx] as u64
    })
}

/// Get global work size (total work items in dimension)
#[no_mangle]
pub extern "C" fn rt_gpu_global_size(dim: u32) -> u64 {
    WORK_ITEM_STATE.with(|s| {
        let state = s.borrow();
        let idx = (dim as usize).min(2);
        state.global_size[idx] as u64
    })
}

/// Get local work group size
#[no_mangle]
pub extern "C" fn rt_gpu_local_size(dim: u32) -> u64 {
    WORK_ITEM_STATE.with(|s| {
        let state = s.borrow();
        let idx = (dim as usize).min(2);
        state.local_size[idx] as u64
    })
}

/// Get number of work groups
#[no_mangle]
pub extern "C" fn rt_gpu_num_groups(dim: u32) -> u64 {
    WORK_ITEM_STATE.with(|s| {
        let state = s.borrow();
        let idx = (dim as usize).min(2);
        state.num_groups[idx] as u64
    })
}

// =============================================================================
// GPU Synchronization FFI Functions
// =============================================================================

/// Work group barrier - synchronize all work items in the group.
/// In software execution, this is a no-op since we execute sequentially.
/// For parallel execution, this would need proper synchronization.
#[no_mangle]
pub extern "C" fn rt_gpu_barrier() {
    // In single-threaded software execution, barrier is a no-op.
    // In a parallel implementation, this would use a barrier synchronization primitive.
    std::sync::atomic::fence(Ordering::SeqCst);
}

/// Memory fence - ensure memory ordering.
/// scope: 0 = work group, 1 = device, 2+ = all
#[no_mangle]
pub extern "C" fn rt_gpu_mem_fence(scope: u32) {
    match scope {
        0 => std::sync::atomic::fence(Ordering::AcqRel),  // Work group local
        1 => std::sync::atomic::fence(Ordering::SeqCst),  // Device memory
        _ => std::sync::atomic::fence(Ordering::SeqCst),  // All memory
    }
}

// =============================================================================
// GPU Atomic Operations FFI Functions (i64)
// =============================================================================

/// Atomic add for i64
#[no_mangle]
pub unsafe extern "C" fn rt_gpu_atomic_add_i64(ptr: *mut i64, value: i64) -> i64 {
    let atomic = &*(ptr as *const AtomicI64);
    atomic.fetch_add(value, Ordering::SeqCst)
}

/// Atomic subtract for i64
#[no_mangle]
pub unsafe extern "C" fn rt_gpu_atomic_sub_i64(ptr: *mut i64, value: i64) -> i64 {
    let atomic = &*(ptr as *const AtomicI64);
    atomic.fetch_sub(value, Ordering::SeqCst)
}

/// Atomic exchange for i64
#[no_mangle]
pub unsafe extern "C" fn rt_gpu_atomic_xchg_i64(ptr: *mut i64, value: i64) -> i64 {
    let atomic = &*(ptr as *const AtomicI64);
    atomic.swap(value, Ordering::SeqCst)
}

/// Atomic compare-exchange for i64
/// Returns the old value. If old value == expected, the new value is written.
#[no_mangle]
pub unsafe extern "C" fn rt_gpu_atomic_cmpxchg_i64(ptr: *mut i64, expected: i64, new: i64) -> i64 {
    let atomic = &*(ptr as *const AtomicI64);
    match atomic.compare_exchange(expected, new, Ordering::SeqCst, Ordering::SeqCst) {
        Ok(old) => old,
        Err(old) => old,
    }
}

/// Atomic minimum for i64
#[no_mangle]
pub unsafe extern "C" fn rt_gpu_atomic_min_i64(ptr: *mut i64, value: i64) -> i64 {
    let atomic = &*(ptr as *const AtomicI64);
    atomic.fetch_min(value, Ordering::SeqCst)
}

/// Atomic maximum for i64
#[no_mangle]
pub unsafe extern "C" fn rt_gpu_atomic_max_i64(ptr: *mut i64, value: i64) -> i64 {
    let atomic = &*(ptr as *const AtomicI64);
    atomic.fetch_max(value, Ordering::SeqCst)
}

/// Atomic AND for i64
#[no_mangle]
pub unsafe extern "C" fn rt_gpu_atomic_and_i64(ptr: *mut i64, value: i64) -> i64 {
    let atomic = &*(ptr as *const AtomicI64);
    atomic.fetch_and(value, Ordering::SeqCst)
}

/// Atomic OR for i64
#[no_mangle]
pub unsafe extern "C" fn rt_gpu_atomic_or_i64(ptr: *mut i64, value: i64) -> i64 {
    let atomic = &*(ptr as *const AtomicI64);
    atomic.fetch_or(value, Ordering::SeqCst)
}

/// Atomic XOR for i64
#[no_mangle]
pub unsafe extern "C" fn rt_gpu_atomic_xor_i64(ptr: *mut i64, value: i64) -> i64 {
    let atomic = &*(ptr as *const AtomicI64);
    atomic.fetch_xor(value, Ordering::SeqCst)
}

// =============================================================================
// GPU Atomic Operations FFI Functions (u32)
// =============================================================================

/// Atomic add for u32
#[no_mangle]
pub unsafe extern "C" fn rt_gpu_atomic_add_u32(ptr: *mut u32, value: u32) -> u32 {
    let atomic = &*(ptr as *const AtomicU32);
    atomic.fetch_add(value, Ordering::SeqCst)
}

/// Atomic subtract for u32
#[no_mangle]
pub unsafe extern "C" fn rt_gpu_atomic_sub_u32(ptr: *mut u32, value: u32) -> u32 {
    let atomic = &*(ptr as *const AtomicU32);
    atomic.fetch_sub(value, Ordering::SeqCst)
}

/// Atomic exchange for u32
#[no_mangle]
pub unsafe extern "C" fn rt_gpu_atomic_xchg_u32(ptr: *mut u32, value: u32) -> u32 {
    let atomic = &*(ptr as *const AtomicU32);
    atomic.swap(value, Ordering::SeqCst)
}

/// Atomic compare-exchange for u32
#[no_mangle]
pub unsafe extern "C" fn rt_gpu_atomic_cmpxchg_u32(ptr: *mut u32, expected: u32, new: u32) -> u32 {
    let atomic = &*(ptr as *const AtomicU32);
    match atomic.compare_exchange(expected, new, Ordering::SeqCst, Ordering::SeqCst) {
        Ok(old) => old,
        Err(old) => old,
    }
}

/// Atomic minimum for u32
#[no_mangle]
pub unsafe extern "C" fn rt_gpu_atomic_min_u32(ptr: *mut u32, value: u32) -> u32 {
    let atomic = &*(ptr as *const AtomicU32);
    atomic.fetch_min(value, Ordering::SeqCst)
}

/// Atomic maximum for u32
#[no_mangle]
pub unsafe extern "C" fn rt_gpu_atomic_max_u32(ptr: *mut u32, value: u32) -> u32 {
    let atomic = &*(ptr as *const AtomicU32);
    atomic.fetch_max(value, Ordering::SeqCst)
}

/// Atomic AND for u32
#[no_mangle]
pub unsafe extern "C" fn rt_gpu_atomic_and_u32(ptr: *mut u32, value: u32) -> u32 {
    let atomic = &*(ptr as *const AtomicU32);
    atomic.fetch_and(value, Ordering::SeqCst)
}

/// Atomic OR for u32
#[no_mangle]
pub unsafe extern "C" fn rt_gpu_atomic_or_u32(ptr: *mut u32, value: u32) -> u32 {
    let atomic = &*(ptr as *const AtomicU32);
    atomic.fetch_or(value, Ordering::SeqCst)
}

/// Atomic XOR for u32
#[no_mangle]
pub unsafe extern "C" fn rt_gpu_atomic_xor_u32(ptr: *mut u32, value: u32) -> u32 {
    let atomic = &*(ptr as *const AtomicU32);
    atomic.fetch_xor(value, Ordering::SeqCst)
}

// =============================================================================
// GPU Shared Memory FFI Functions
// =============================================================================

// Thread-local shared memory allocation
thread_local! {
    static SHARED_MEMORY: RefCell<Vec<u8>> = RefCell::new(Vec::new());
}

/// Allocate shared memory (work group local memory)
/// Returns pointer to the allocated memory
#[no_mangle]
pub extern "C" fn rt_gpu_shared_alloc(size: u64) -> *mut u8 {
    SHARED_MEMORY.with(|mem| {
        let mut mem = mem.borrow_mut();
        let offset = mem.len();
        mem.resize(offset + size as usize, 0);
        mem.as_mut_ptr().wrapping_add(offset)
    })
}

/// Reset shared memory (call at start of each work group)
#[no_mangle]
pub extern "C" fn rt_gpu_shared_reset() {
    SHARED_MEMORY.with(|mem| {
        mem.borrow_mut().clear();
    });
}

// =============================================================================
// GPU Kernel Execution (Software Backend)
// =============================================================================

/// Type alias for a GPU kernel function pointer
pub type GpuKernelFn = extern "C" fn();

/// Execute a GPU kernel with 1D work configuration
pub fn execute_kernel_1d(kernel: GpuKernelFn, global_size: u32, local_size: u32) {
    let num_groups = (global_size + local_size - 1) / local_size;

    for group_id in 0..num_groups {
        // Reset shared memory at the start of each work group
        rt_gpu_shared_reset();

        for local_id in 0..local_size {
            let global_id = group_id * local_size + local_id;
            if global_id >= global_size {
                break;
            }

            // Set work item state
            set_work_item_state(GpuWorkItemState {
                global_id: [global_id, 0, 0],
                local_id: [local_id, 0, 0],
                group_id: [group_id, 0, 0],
                global_size: [global_size, 1, 1],
                local_size: [local_size, 1, 1],
                num_groups: [num_groups, 1, 1],
            });

            // Execute kernel for this work item
            kernel();
        }
    }
}

/// Execute a GPU kernel with 3D work configuration
pub fn execute_kernel_3d(kernel: GpuKernelFn, global_size: [u32; 3], local_size: [u32; 3]) {
    let num_groups = [
        (global_size[0] + local_size[0] - 1) / local_size[0],
        (global_size[1] + local_size[1] - 1) / local_size[1],
        (global_size[2] + local_size[2] - 1) / local_size[2],
    ];

    for gz in 0..num_groups[2] {
        for gy in 0..num_groups[1] {
            for gx in 0..num_groups[0] {
                // Reset shared memory at the start of each work group
                rt_gpu_shared_reset();

                for lz in 0..local_size[2] {
                    for ly in 0..local_size[1] {
                        for lx in 0..local_size[0] {
                            let global_id = [
                                gx * local_size[0] + lx,
                                gy * local_size[1] + ly,
                                gz * local_size[2] + lz,
                            ];

                            // Skip if outside global size
                            if global_id[0] >= global_size[0]
                                || global_id[1] >= global_size[1]
                                || global_id[2] >= global_size[2]
                            {
                                continue;
                            }

                            // Set work item state
                            set_work_item_state(GpuWorkItemState {
                                global_id,
                                local_id: [lx, ly, lz],
                                group_id: [gx, gy, gz],
                                global_size,
                                local_size,
                                num_groups,
                            });

                            // Execute kernel for this work item
                            kernel();
                        }
                    }
                }
            }
        }
    }
}

/// Launch a GPU kernel (FFI entry point)
/// kernel_ptr: Function pointer to the kernel
/// gx, gy, gz: Global work size
/// lx, ly, lz: Local work group size
#[no_mangle]
pub extern "C" fn rt_gpu_launch(
    kernel_ptr: u64,
    gx: u32, gy: u32, gz: u32,
    lx: u32, ly: u32, lz: u32,
) -> i32 {
    let kernel: GpuKernelFn = unsafe { std::mem::transmute(kernel_ptr) };
    execute_kernel_3d(kernel, [gx, gy, gz], [lx, ly, lz]);
    0 // Success
}

/// Launch a 1D GPU kernel (convenience FFI entry point)
#[no_mangle]
pub extern "C" fn rt_gpu_launch_1d(kernel_ptr: u64, global_size: u32, local_size: u32) -> i32 {
    let kernel: GpuKernelFn = unsafe { std::mem::transmute(kernel_ptr) };
    execute_kernel_1d(kernel, global_size, local_size);
    0 // Success
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_work_item_state() {
        set_work_item_state(GpuWorkItemState {
            global_id: [10, 20, 30],
            local_id: [2, 4, 6],
            group_id: [1, 2, 3],
            global_size: [100, 100, 100],
            local_size: [8, 8, 8],
            num_groups: [13, 13, 13],
        });

        assert_eq!(rt_gpu_global_id(0), 10);
        assert_eq!(rt_gpu_global_id(1), 20);
        assert_eq!(rt_gpu_global_id(2), 30);

        assert_eq!(rt_gpu_local_id(0), 2);
        assert_eq!(rt_gpu_local_id(1), 4);
        assert_eq!(rt_gpu_local_id(2), 6);

        assert_eq!(rt_gpu_group_id(0), 1);
        assert_eq!(rt_gpu_group_id(1), 2);
        assert_eq!(rt_gpu_group_id(2), 3);

        assert_eq!(rt_gpu_global_size(0), 100);
        assert_eq!(rt_gpu_local_size(0), 8);
        assert_eq!(rt_gpu_num_groups(0), 13);
    }

    #[test]
    fn test_atomic_add_i64() {
        let mut value: i64 = 10;
        unsafe {
            let old = rt_gpu_atomic_add_i64(&mut value, 5);
            assert_eq!(old, 10);
            assert_eq!(value, 15);
        }
    }

    #[test]
    fn test_atomic_cmpxchg_i64() {
        let mut value: i64 = 10;
        unsafe {
            // Successful exchange
            let old = rt_gpu_atomic_cmpxchg_i64(&mut value, 10, 20);
            assert_eq!(old, 10);
            assert_eq!(value, 20);

            // Failed exchange (expected doesn't match)
            let old = rt_gpu_atomic_cmpxchg_i64(&mut value, 10, 30);
            assert_eq!(old, 20);
            assert_eq!(value, 20);
        }
    }

    #[test]
    fn test_shared_memory() {
        rt_gpu_shared_reset();

        let ptr1 = rt_gpu_shared_alloc(16);
        assert!(!ptr1.is_null());

        let ptr2 = rt_gpu_shared_alloc(32);
        assert!(!ptr2.is_null());
        assert_ne!(ptr1, ptr2);

        // Reset and verify we can allocate again from the start
        rt_gpu_shared_reset();
        let ptr3 = rt_gpu_shared_alloc(16);
        assert!(!ptr3.is_null());
    }

    #[test]
    fn test_kernel_1d_execution() {
        use std::sync::atomic::AtomicU64;

        static COUNTER: AtomicU64 = AtomicU64::new(0);
        COUNTER.store(0, Ordering::SeqCst);

        extern "C" fn test_kernel() {
            COUNTER.fetch_add(1, Ordering::SeqCst);
        }

        execute_kernel_1d(test_kernel, 100, 32);

        assert_eq!(COUNTER.load(Ordering::SeqCst), 100);
    }
}
