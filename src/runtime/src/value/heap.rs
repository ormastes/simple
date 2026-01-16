//! Heap object types and header structure.

/// Heap object type tags
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HeapObjectType {
    String = 0x01,
    Array = 0x02,
    Dict = 0x03,
    Tuple = 0x04,
    Object = 0x05,
    Closure = 0x06,
    Enum = 0x07,
    Future = 0x08,
    Generator = 0x09,
    Actor = 0x0A,
    Unique = 0x0B,
    Shared = 0x0C,
    Borrow = 0x0D,
    Channel = 0x0E,
    Weak = 0x0F,
    ContractViolation = 0x10,
    // Synchronization primitives
    Mutex = 0x11,
    RwLock = 0x12,
    Semaphore = 0x13,
    Barrier = 0x14,
    Atomic = 0x15,
    // Monoio direct async I/O (feature: monoio-direct)
    MonoioFuture = 0x16,
}

/// Header for all heap-allocated objects
#[repr(C)]
#[derive(Debug)]
pub struct HeapHeader {
    /// Type of the heap object
    pub object_type: HeapObjectType,
    /// GC flags (mark bit, etc.)
    pub gc_flags: u8,
    /// Reserved for alignment
    pub reserved: u16,
    /// Size of the object in bytes (including header)
    pub size: u32,
}

impl HeapHeader {
    pub fn new(object_type: HeapObjectType, size: u32) -> Self {
        Self {
            object_type,
            gc_flags: 0,
            reserved: 0,
            size,
        }
    }
}

// ============================================================================
// Shared heap validation utilities
// ============================================================================

use super::core::RuntimeValue;

/// Validate heap object type, returns None if invalid
///
/// This is a shared helper to reduce boilerplate in FFI functions.
#[inline]
pub fn validate_heap_obj(val: RuntimeValue, expected: HeapObjectType) -> Option<*mut HeapHeader> {
    if !val.is_heap() {
        return None;
    }
    let ptr = val.as_heap_ptr();
    if unsafe { (*ptr).object_type != expected } {
        return None;
    }
    Some(ptr)
}

/// Get typed pointer from heap object with validation.
/// Returns None if the value is not a valid heap object of the expected type.
#[inline]
pub fn get_typed_ptr<T>(val: RuntimeValue, expected: HeapObjectType) -> Option<*const T> {
    validate_heap_obj(val, expected).map(|ptr| ptr as *const T)
}

/// Get mutable typed pointer from heap object with validation.
/// Returns None if the value is not a valid heap object of the expected type.
#[inline]
pub fn get_typed_ptr_mut<T>(val: RuntimeValue, expected: HeapObjectType) -> Option<*mut T> {
    validate_heap_obj(val, expected).map(|ptr| ptr as *mut T)
}

/// Macro to get typed pointer with early return on invalid type.
/// Usage: `let ptr = as_typed_ptr!(val, HeapObjectType::Array, RuntimeArray, RuntimeValue::NIL);`
#[macro_export]
macro_rules! as_typed_ptr {
    ($val:expr, $expected:expr, $ty:ty, $ret:expr) => {{
        match $crate::value::heap::get_typed_ptr::<$ty>($val, $expected) {
            Some(ptr) => ptr,
            None => return $ret,
        }
    }};
    (mut $val:expr, $expected:expr, $ty:ty, $ret:expr) => {{
        match $crate::value::heap::get_typed_ptr_mut::<$ty>($val, $expected) {
            Some(ptr) => ptr,
            None => return $ret,
        }
    }};
}
