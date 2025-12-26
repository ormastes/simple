// Semaphore implementation for sync module
// (imports are inherited from parent sync.rs)

// ============================================================================
// Semaphore Implementation
// ============================================================================

/// Runtime semaphore (counting semaphore).
#[repr(C)]
pub struct RuntimeSemaphore {
    pub header: HeapHeader,
    /// The semaphore state (count, mutex, condvar)
    pub inner: *mut SemaphoreInner,
    /// Semaphore ID
    pub sem_id: u64,
}

struct SemaphoreInner {
    count: Mutex<i64>,
    condvar: Condvar,
}

static NEXT_SEM_ID: AtomicU64 = AtomicU64::new(1);

/// Create a new semaphore with initial count.
#[no_mangle]
pub extern "C" fn rt_semaphore_new(initial_count: i64) -> RuntimeValue {
    let sem_id = NEXT_SEM_ID.fetch_add(1, Ordering::SeqCst);
    let inner = Box::into_raw(Box::new(SemaphoreInner {
        count: Mutex::new(initial_count.max(0)),
        condvar: Condvar::new(),
    }));

    let size = std::mem::size_of::<RuntimeSemaphore>();
    let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();

    unsafe {
        let ptr = std::alloc::alloc_zeroed(layout) as *mut RuntimeSemaphore;
        if ptr.is_null() {
            drop(Box::from_raw(inner));
            return RuntimeValue::NIL;
        }

        (*ptr).header = HeapHeader::new(HeapObjectType::Semaphore, size as u32);
        (*ptr).inner = inner;
        (*ptr).sem_id = sem_id;

        RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader)
    }
}

fn as_semaphore_ptr(value: RuntimeValue) -> Option<*mut RuntimeSemaphore> {
    if !value.is_heap() {
        return None;
    }
    let ptr = value.as_heap_ptr() as *mut RuntimeSemaphore;
    unsafe {
        if (*ptr).inner.is_null() {
            return None;
        }
        Some(ptr)
    }
}

/// Acquire the semaphore (decrement count). Blocks if count is 0.
#[no_mangle]
pub extern "C" fn rt_semaphore_acquire(sem: RuntimeValue) -> i64 {
    let Some(sem_ptr) = as_semaphore_ptr(sem) else {
        return 0;
    };

    unsafe {
        let inner = &*(*sem_ptr).inner;
        let mut count = inner.count.lock().unwrap();
        while *count <= 0 {
            count = inner.condvar.wait(count).unwrap();
        }
        *count -= 1;
        1
    }
}

/// Try to acquire the semaphore without blocking.
/// Returns 1 if acquired, 0 if would block.
#[no_mangle]
pub extern "C" fn rt_semaphore_try_acquire(sem: RuntimeValue) -> i64 {
    let Some(sem_ptr) = as_semaphore_ptr(sem) else {
        return 0;
    };

    unsafe {
        let inner = &*(*sem_ptr).inner;
        let mut count = match inner.count.try_lock() {
            Ok(g) => g,
            Err(_) => return 0,
        };
        if *count > 0 {
            *count -= 1;
            1
        } else {
            0
        }
    }
}

/// Acquire with timeout (milliseconds).
/// Returns 1 if acquired, 0 if timeout.
#[no_mangle]
pub extern "C" fn rt_semaphore_acquire_timeout(sem: RuntimeValue, timeout_ms: i64) -> i64 {
    let Some(sem_ptr) = as_semaphore_ptr(sem) else {
        return 0;
    };

    let timeout = Duration::from_millis(timeout_ms.max(0) as u64);

    unsafe {
        let inner = &*(*sem_ptr).inner;
        let mut count = inner.count.lock().unwrap();
        let deadline = std::time::Instant::now() + timeout;

        while *count <= 0 {
            let remaining = deadline.saturating_duration_since(std::time::Instant::now());
            if remaining.is_zero() {
                return 0;
            }
            let (new_count, result) = inner.condvar.wait_timeout(count, remaining).unwrap();
            count = new_count;
            if result.timed_out() && *count <= 0 {
                return 0;
            }
        }
        *count -= 1;
        1
    }
}

/// Release the semaphore (increment count).
#[no_mangle]
pub extern "C" fn rt_semaphore_release(sem: RuntimeValue) -> i64 {
    let Some(sem_ptr) = as_semaphore_ptr(sem) else {
        return 0;
    };

    unsafe {
        let inner = &*(*sem_ptr).inner;
        let mut count = inner.count.lock().unwrap();
        *count += 1;
        inner.condvar.notify_one();
        1
    }
}

/// Get current semaphore count.
#[no_mangle]
pub extern "C" fn rt_semaphore_count(sem: RuntimeValue) -> i64 {
    let Some(sem_ptr) = as_semaphore_ptr(sem) else {
        return 0;
    };

    unsafe {
        let inner = &*(*sem_ptr).inner;
        *inner.count.lock().unwrap()
    }
}

/// Free a semaphore.
#[no_mangle]
pub extern "C" fn rt_semaphore_free(sem: RuntimeValue) {
    let Some(sem_ptr) = as_semaphore_ptr(sem) else {
        return;
    };

    unsafe {
        if !(*sem_ptr).inner.is_null() {
            drop(Box::from_raw((*sem_ptr).inner));
        }
        let size = std::mem::size_of::<RuntimeSemaphore>();
        let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();
        std::alloc::dealloc(sem_ptr as *mut u8, layout);
    }
}
