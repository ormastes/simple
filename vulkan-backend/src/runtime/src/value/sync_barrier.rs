// Barrier implementation for sync module
// (imports are inherited from parent sync.rs)

// ============================================================================
// Barrier Implementation
// ============================================================================

/// Runtime barrier for synchronizing multiple threads.
#[repr(C)]
pub struct RuntimeBarrier {
    pub header: HeapHeader,
    /// The barrier
    pub inner: *mut Arc<Barrier>,
    /// Barrier ID
    pub barrier_id: u64,
    /// Number of threads to synchronize
    pub thread_count: u64,
}

static NEXT_BARRIER_ID: AtomicU64 = AtomicU64::new(1);

/// Create a new barrier for the given number of threads.
#[no_mangle]
pub extern "C" fn rt_barrier_new(thread_count: i64) -> RuntimeValue {
    if thread_count <= 0 {
        return RuntimeValue::NIL;
    }

    let barrier_id = NEXT_BARRIER_ID.fetch_add(1, Ordering::SeqCst);
    let inner = Box::into_raw(Box::new(Arc::new(Barrier::new(thread_count as usize))));

    let size = std::mem::size_of::<RuntimeBarrier>();
    let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();

    unsafe {
        let ptr = std::alloc::alloc_zeroed(layout) as *mut RuntimeBarrier;
        if ptr.is_null() {
            drop(Box::from_raw(inner));
            return RuntimeValue::NIL;
        }

        (*ptr).header = HeapHeader::new(HeapObjectType::Barrier, size as u32);
        (*ptr).inner = inner;
        (*ptr).barrier_id = barrier_id;
        (*ptr).thread_count = thread_count as u64;

        RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader)
    }
}

fn as_barrier_ptr(value: RuntimeValue) -> Option<*mut RuntimeBarrier> {
    if !value.is_heap() {
        return None;
    }
    let ptr = value.as_heap_ptr() as *mut RuntimeBarrier;
    unsafe {
        if (*ptr).inner.is_null() {
            return None;
        }
        Some(ptr)
    }
}

/// Wait at the barrier. Blocks until all threads arrive.
/// Returns 1 if this is the leader (last to arrive), 0 otherwise.
#[no_mangle]
pub extern "C" fn rt_barrier_wait(barrier: RuntimeValue) -> i64 {
    let Some(bar_ptr) = as_barrier_ptr(barrier) else {
        return 0;
    };

    unsafe {
        let arc = &*(*bar_ptr).inner;
        let result = arc.wait();
        if result.is_leader() { 1 } else { 0 }
    }
}

/// Get the thread count for this barrier.
#[no_mangle]
pub extern "C" fn rt_barrier_thread_count(barrier: RuntimeValue) -> i64 {
    let Some(bar_ptr) = as_barrier_ptr(barrier) else {
        return 0;
    };

    unsafe { (*bar_ptr).thread_count as i64 }
}

/// Free a barrier.
#[no_mangle]
pub extern "C" fn rt_barrier_free(barrier: RuntimeValue) {
    let Some(bar_ptr) = as_barrier_ptr(barrier) else {
        return;
    };

    unsafe {
        if !(*bar_ptr).inner.is_null() {
            drop(Box::from_raw((*bar_ptr).inner));
        }
        let size = std::mem::size_of::<RuntimeBarrier>();
        let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();
        std::alloc::dealloc(bar_ptr as *mut u8, layout);
    }
}
