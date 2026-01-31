// RwLock implementation for sync module
// (imports are inherited from parent sync.rs)

// ============================================================================
// RwLock Implementation
// ============================================================================

/// Runtime read-write lock.
#[repr(C)]
pub struct RuntimeRwLock {
    pub header: HeapHeader,
    /// The RwLock holding the protected value
    pub inner: *mut Arc<RwLock<RuntimeValue>>,
    /// Lock ID for debugging
    pub lock_id: u64,
}

static NEXT_RWLOCK_ID: AtomicU64 = AtomicU64::new(1);

/// Create a new RwLock protecting the given value.
#[no_mangle]
pub extern "C" fn rt_rwlock_new(value: RuntimeValue) -> RuntimeValue {
    let lock_id = NEXT_RWLOCK_ID.fetch_add(1, Ordering::SeqCst);
    let inner = Box::into_raw(Box::new(Arc::new(RwLock::new(value))));

    let size = std::mem::size_of::<RuntimeRwLock>();
    let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();

    unsafe {
        let ptr = std::alloc::alloc_zeroed(layout) as *mut RuntimeRwLock;
        if ptr.is_null() {
            drop(Box::from_raw(inner));
            return RuntimeValue::NIL;
        }

        (*ptr).header = HeapHeader::new(HeapObjectType::RwLock, size as u32);
        (*ptr).inner = inner;
        (*ptr).lock_id = lock_id;

        RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader)
    }
}

fn as_rwlock_ptr(value: RuntimeValue) -> Option<*mut RuntimeRwLock> {
    if !value.is_heap() {
        return None;
    }
    let ptr = value.as_heap_ptr() as *mut RuntimeRwLock;
    unsafe {
        if (*ptr).inner.is_null() {
            return None;
        }
        Some(ptr)
    }
}

/// Acquire a read lock (shared). Blocks until acquired.
#[no_mangle]
pub extern "C" fn rt_rwlock_read(lock: RuntimeValue) -> RuntimeValue {
    let Some(rw_ptr) = as_rwlock_ptr(lock) else {
        return RuntimeValue::NIL;
    };

    unsafe {
        let arc = &*(*rw_ptr).inner;
        match arc.read() {
            Ok(guard) => *guard,
            Err(_) => RuntimeValue::NIL,
        }
    }
}

/// Try to acquire a read lock without blocking.
#[no_mangle]
pub extern "C" fn rt_rwlock_try_read(lock: RuntimeValue) -> RuntimeValue {
    let Some(rw_ptr) = as_rwlock_ptr(lock) else {
        return RuntimeValue::NIL;
    };

    unsafe {
        let arc = &*(*rw_ptr).inner;
        match arc.try_read() {
            Ok(guard) => *guard,
            Err(_) => RuntimeValue::NIL,
        }
    }
}

/// Acquire a write lock (exclusive). Blocks until acquired.
#[no_mangle]
pub extern "C" fn rt_rwlock_write(lock: RuntimeValue) -> RuntimeValue {
    let Some(rw_ptr) = as_rwlock_ptr(lock) else {
        return RuntimeValue::NIL;
    };

    unsafe {
        let arc = &*(*rw_ptr).inner;
        match arc.write() {
            Ok(guard) => *guard,
            Err(_) => RuntimeValue::NIL,
        }
    }
}

/// Try to acquire a write lock without blocking.
#[no_mangle]
pub extern "C" fn rt_rwlock_try_write(lock: RuntimeValue) -> RuntimeValue {
    let Some(rw_ptr) = as_rwlock_ptr(lock) else {
        return RuntimeValue::NIL;
    };

    unsafe {
        let arc = &*(*rw_ptr).inner;
        match arc.try_write() {
            Ok(guard) => *guard,
            Err(_) => RuntimeValue::NIL,
        }
    }
}

/// Update the protected value (must hold write lock).
#[no_mangle]
pub extern "C" fn rt_rwlock_set(lock: RuntimeValue, new_value: RuntimeValue) -> i64 {
    let Some(rw_ptr) = as_rwlock_ptr(lock) else {
        return 0;
    };

    unsafe {
        let arc = &*(*rw_ptr).inner;
        match arc.write() {
            Ok(mut guard) => {
                *guard = new_value;
                1
            }
            Err(_) => 0,
        }
    }
}

/// Free a RwLock.
#[no_mangle]
pub extern "C" fn rt_rwlock_free(lock: RuntimeValue) {
    let Some(rw_ptr) = as_rwlock_ptr(lock) else {
        return;
    };

    unsafe {
        if !(*rw_ptr).inner.is_null() {
            drop(Box::from_raw((*rw_ptr).inner));
        }
        let size = std::mem::size_of::<RuntimeRwLock>();
        let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();
        std::alloc::dealloc(rw_ptr as *mut u8, layout);
    }
}
