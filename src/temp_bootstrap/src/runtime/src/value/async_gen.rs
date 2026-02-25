//! Future and Generator types and their FFI functions.

use super::core::RuntimeValue;
use super::heap::{HeapHeader, HeapObjectType};

/// Helper macro to validate a heap object type and get a typed pointer.
/// Returns the specified default if validation fails.
macro_rules! validate_heap_type {
    ($val:expr, $expected:expr, $ty:ty, $default:expr) => {{
        if !$val.is_heap() {
            return $default;
        }
        let ptr = $val.as_heap_ptr();
        unsafe {
            if (*ptr).object_type != $expected {
                return $default;
            }
            ptr as *mut $ty
        }
    }};
}

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
    let gen = validate_heap_type!(generator, HeapObjectType::Generator, RuntimeGenerator, 0);
    unsafe { (*gen).state as i64 }
}

#[no_mangle]
pub extern "C" fn rt_generator_set_state(generator: RuntimeValue, state: i64) {
    let gen = validate_heap_type!(generator, HeapObjectType::Generator, RuntimeGenerator, ());
    unsafe {
        (*gen).state = if state < 0 { 0 } else { state as u64 };
    }
}

#[no_mangle]
pub extern "C" fn rt_generator_store_slot(generator: RuntimeValue, idx: i64, value: RuntimeValue) {
    if idx < 0 {
        return;
    }
    let gen = validate_heap_type!(generator, HeapObjectType::Generator, RuntimeGenerator, ());
    unsafe {
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
    if idx < 0 {
        return RuntimeValue::NIL;
    }
    let gen = validate_heap_type!(
        generator,
        HeapObjectType::Generator,
        RuntimeGenerator,
        RuntimeValue::NIL
    );
    unsafe {
        if (*gen).slots.is_null() {
            return RuntimeValue::NIL;
        }
        let slots = &*(*gen).slots;
        slots
            .get(idx as usize)
            .copied()
            .unwrap_or(RuntimeValue::NIL)
    }
}

#[no_mangle]
pub extern "C" fn rt_generator_get_ctx(generator: RuntimeValue) -> RuntimeValue {
    let gen = validate_heap_type!(
        generator,
        HeapObjectType::Generator,
        RuntimeGenerator,
        RuntimeValue::NIL
    );
    unsafe { (*gen).ctx }
}

#[no_mangle]
pub extern "C" fn rt_generator_mark_done(generator: RuntimeValue) {
    let gen = validate_heap_type!(generator, HeapObjectType::Generator, RuntimeGenerator, ());
    unsafe {
        (*gen).done = 1;
    }
}

/// Resume a generator by calling its compiled dispatcher. Returns NIL when exhausted.
#[no_mangle]
pub extern "C" fn rt_generator_next(generator: RuntimeValue) -> RuntimeValue {
    let gen = validate_heap_type!(
        generator,
        HeapObjectType::Generator,
        RuntimeGenerator,
        RuntimeValue::NIL
    );
    unsafe {
        if (*gen).done != 0 || (*gen).body_func == 0 {
            return RuntimeValue::NIL;
        }
        let func: extern "C" fn(RuntimeValue) -> RuntimeValue =
            std::mem::transmute((*gen).body_func as usize);
        let gen_val = RuntimeValue::from_heap_ptr(gen as *mut HeapHeader);
        func(gen_val)
    }
}

// ============================================================================
// Future Combinators
// ============================================================================

use super::collections::rt_array_new;

/// Check if a future is ready.
/// Returns 1 if ready, 0 if still pending.
#[no_mangle]
pub extern "C" fn rt_future_is_ready(future: RuntimeValue) -> i64 {
    let fut = validate_heap_type!(future, HeapObjectType::Future, RuntimeFuture, 0);
    unsafe {
        if (*fut).state == 1 { 1 } else { 0 }
    }
}

/// Get the result of a ready future without blocking.
/// Returns NIL if the future is not ready.
#[no_mangle]
pub extern "C" fn rt_future_get_result(future: RuntimeValue) -> RuntimeValue {
    let fut = validate_heap_type!(future, HeapObjectType::Future, RuntimeFuture, RuntimeValue::NIL);
    unsafe {
        if (*fut).state == 1 {
            (*fut).result
        } else {
            RuntimeValue::NIL
        }
    }
}

/// Wait for all futures in an array to complete.
/// Returns an array of results in the same order.
/// Note: In eager execution mode, all futures complete immediately.
#[no_mangle]
pub extern "C" fn rt_future_all(futures_array: RuntimeValue) -> RuntimeValue {
    use super::collections::{rt_array_get, rt_array_len, rt_array_push};

    let len = rt_array_len(futures_array);
    if len == 0 {
        return rt_array_new(0);
    }

    // Create result array
    let results = rt_array_new(len as u64);

    // Collect results from each future
    for i in 0..len {
        let future = rt_array_get(futures_array, i);
        let result = rt_future_await(future);
        rt_array_push(results, result);
    }

    results
}

/// Wait for the first future in an array to complete.
/// Returns the result of the first completed future.
/// Note: In eager execution mode, returns the first future's result.
#[no_mangle]
pub extern "C" fn rt_future_race(futures_array: RuntimeValue) -> RuntimeValue {
    use super::collections::{rt_array_get, rt_array_len};

    let len = rt_array_len(futures_array);
    if len == 0 {
        return RuntimeValue::NIL;
    }

    // In eager mode, all futures are already complete
    // Return the first one that's ready
    for i in 0..len {
        let future = rt_array_get(futures_array, i);
        if rt_future_is_ready(future) == 1 {
            return rt_future_get_result(future);
        }
    }

    // Fall back to awaiting the first future
    let first_future = rt_array_get(futures_array, 0);
    rt_future_await(first_future)
}

/// Create a resolved future with an immediate value.
#[no_mangle]
pub extern "C" fn rt_future_resolve(value: RuntimeValue) -> RuntimeValue {
    let size = std::mem::size_of::<RuntimeFuture>();
    let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();

    unsafe {
        let ptr = std::alloc::alloc_zeroed(layout) as *mut RuntimeFuture;
        if ptr.is_null() {
            return RuntimeValue::NIL;
        }

        (*ptr).header = HeapHeader::new(HeapObjectType::Future, size as u32);
        (*ptr).state = 1; // already ready
        (*ptr).result = value;
        (*ptr).body_func = 0;

        RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader)
    }
}

/// Create a rejected future (for error handling).
/// The error value is stored as the result.
#[no_mangle]
pub extern "C" fn rt_future_reject(error: RuntimeValue) -> RuntimeValue {
    // For now, rejection is modeled as a ready future with an error value
    // A proper implementation would track rejection state separately
    rt_future_resolve(error)
}
