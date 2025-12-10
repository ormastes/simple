//! Future and Generator types and their FFI functions.

use super::core::RuntimeValue;
use super::heap::{HeapHeader, HeapObjectType};

// ============================================================================
// Future type and operations
// ============================================================================

/// RuntimeFuture represents a suspended computation
#[repr(C)]
pub struct RuntimeFuture {
    pub header: HeapHeader,
    /// Current state (0 = pending, 1 = ready)
    pub state: u64,
    /// Result value when ready
    pub result: RuntimeValue,
    /// Function pointer to the body (for resuming)
    pub body_func: u64,
}

/// Create a new future. Eagerly executes the body and stores result.
#[no_mangle]
pub extern "C" fn rt_future_new(body_func: u64, ctx: RuntimeValue) -> RuntimeValue {
    let size = std::mem::size_of::<RuntimeFuture>();
    let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();

    unsafe {
        let ptr = std::alloc::alloc_zeroed(layout) as *mut RuntimeFuture;
        if ptr.is_null() {
            return RuntimeValue::NIL;
        }

        (*ptr).header = HeapHeader::new(HeapObjectType::Future, size as u32);
        (*ptr).state = 0; // pending
        (*ptr).result = RuntimeValue::NIL;
        (*ptr).body_func = body_func;

        // Eagerly execute body if provided and capture return value
        if body_func != 0 {
            // Body function signature: fn(ctx: RuntimeValue) -> RuntimeValue
            let func: extern "C" fn(RuntimeValue) -> RuntimeValue =
                std::mem::transmute(body_func as usize);
            let result = func(ctx);
            (*ptr).state = 1; // ready
            (*ptr).result = result;
        }

        RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader)
    }
}

/// Await a future. For now, immediately returns NIL (stub).
/// Full implementation needs async runtime integration.
#[no_mangle]
pub extern "C" fn rt_future_await(future: RuntimeValue) -> RuntimeValue {
    if !future.is_heap() {
        return RuntimeValue::NIL;
    }

    let ptr = future.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::Future {
            return RuntimeValue::NIL;
        }
        let f = ptr as *const RuntimeFuture;
        if (*f).state == 1 {
            // Already ready
            return (*f).result;
        }
        // Stub: return NIL for pending futures
        RuntimeValue::NIL
    }
}

// ============================================================================
// Generator type and operations
// ============================================================================

/// RuntimeGenerator represents a stackless generator with explicit frame slots.
#[repr(C)]
pub struct RuntimeGenerator {
    pub header: HeapHeader,
    /// Next state to execute (0 = entry, n = resume after nth yield).
    pub state: u64,
    /// Heap-allocated frame slots for live locals.
    pub slots: *mut Vec<RuntimeValue>,
    /// Captured context (array) passed at creation time.
    pub ctx: RuntimeValue,
    /// Compiled dispatcher function pointer.
    pub body_func: u64,
    /// Completion flag (1 = done).
    pub done: u8,
}

fn alloc_generator_slots(size: usize) -> *mut Vec<RuntimeValue> {
    let mut v = Vec::with_capacity(size);
    v.resize(size, RuntimeValue::NIL);
    Box::into_raw(Box::new(v))
}

/// Create a new generator with an empty frame initialized to NIL.
#[no_mangle]
pub extern "C" fn rt_generator_new(body_func: u64, slots: i64, ctx: RuntimeValue) -> RuntimeValue {
    let slots = if slots < 0 { 0 } else { slots as usize };
    let slots_ptr = alloc_generator_slots(slots);

    let size = std::mem::size_of::<RuntimeGenerator>();
    let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();

    unsafe {
        let ptr = std::alloc::alloc_zeroed(layout) as *mut RuntimeGenerator;
        if ptr.is_null() {
            drop(Box::from_raw(slots_ptr));
            return RuntimeValue::NIL;
        }

        (*ptr).header = HeapHeader::new(HeapObjectType::Generator, size as u32);
        (*ptr).state = 0;
        (*ptr).slots = slots_ptr;
        (*ptr).ctx = ctx;
        (*ptr).body_func = body_func;
        (*ptr).done = 0;

        RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader)
    }
}

#[no_mangle]
pub extern "C" fn rt_generator_get_state(generator: RuntimeValue) -> i64 {
    if !generator.is_heap() {
        return 0;
    }
    let ptr = generator.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::Generator {
            return 0;
        }
        let gen = ptr as *mut RuntimeGenerator;
        (*gen).state as i64
    }
}

#[no_mangle]
pub extern "C" fn rt_generator_set_state(generator: RuntimeValue, state: i64) {
    if !generator.is_heap() {
        return;
    }
    let ptr = generator.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::Generator {
            return;
        }
        let gen = ptr as *mut RuntimeGenerator;
        (*gen).state = if state < 0 { 0 } else { state as u64 };
    }
}

#[no_mangle]
pub extern "C" fn rt_generator_store_slot(generator: RuntimeValue, idx: i64, value: RuntimeValue) {
    if idx < 0 || !generator.is_heap() {
        return;
    }
    let ptr = generator.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::Generator {
            return;
        }
        let gen = ptr as *mut RuntimeGenerator;
        if (*gen).slots.is_null() {
            return;
        }
        let slots = &mut *(*gen).slots;
        let idx = idx as usize;
        if idx >= slots.len() {
            slots.resize(idx + 1, RuntimeValue::NIL);
        }
        slots[idx] = value;
    }
}

#[no_mangle]
pub extern "C" fn rt_generator_load_slot(generator: RuntimeValue, idx: i64) -> RuntimeValue {
    if idx < 0 || !generator.is_heap() {
        return RuntimeValue::NIL;
    }
    let ptr = generator.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::Generator {
            return RuntimeValue::NIL;
        }
        let gen = ptr as *mut RuntimeGenerator;
        if (*gen).slots.is_null() {
            return RuntimeValue::NIL;
        }
        let slots = &*(*gen).slots;
        let idx = idx as usize;
        slots.get(idx).copied().unwrap_or(RuntimeValue::NIL)
    }
}

#[no_mangle]
pub extern "C" fn rt_generator_get_ctx(generator: RuntimeValue) -> RuntimeValue {
    if !generator.is_heap() {
        return RuntimeValue::NIL;
    }
    let ptr = generator.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::Generator {
            return RuntimeValue::NIL;
        }
        let gen = ptr as *mut RuntimeGenerator;
        (*gen).ctx
    }
}

#[no_mangle]
pub extern "C" fn rt_generator_mark_done(generator: RuntimeValue) {
    if !generator.is_heap() {
        return;
    }
    let ptr = generator.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::Generator {
            return;
        }
        let gen = ptr as *mut RuntimeGenerator;
        (*gen).done = 1;
    }
}

/// Resume a generator by calling its compiled dispatcher. Returns NIL when exhausted.
#[no_mangle]
pub extern "C" fn rt_generator_next(generator: RuntimeValue) -> RuntimeValue {
    if !generator.is_heap() {
        return RuntimeValue::NIL;
    }

    let ptr = generator.as_heap_ptr();
    unsafe {
        if (*ptr).object_type != HeapObjectType::Generator {
            return RuntimeValue::NIL;
        }
        let gen = ptr as *mut RuntimeGenerator;
        if (*gen).done != 0 || (*gen).body_func == 0 {
            return RuntimeValue::NIL;
        }
        let func: extern "C" fn(RuntimeValue) -> RuntimeValue =
            std::mem::transmute((*gen).body_func as usize);
        let gen_val = RuntimeValue::from_heap_ptr(ptr);
        func(gen_val)
    }
}

