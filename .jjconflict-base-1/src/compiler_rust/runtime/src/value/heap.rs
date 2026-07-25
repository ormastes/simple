//! Heap object types and header structure.

use crate::hir_core::ValueKind;

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
    // High-performance collections (Rust std::collections)
    HashMap = 0x17,
    BTreeMap = 0x18,
    HashSet = 0x19,
    BTreeSet = 0x1A,
    // SFFI-wrapped Rust objects (object-based SFFI system)
    FfiObject = 0x1B,
    // Heap-boxed f64. The inline TAG_FLOAT representation stores only the upper
    // 61 bits of the mantissa (`bits >> 3`), silently zeroing the low 3 bits, so
    // a container/Any float loses precision ([0.1][0] != 0.1). Container floats
    // are boxed here instead, preserving the full double losslessly.
    Float = 0x1C,
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

/// Heap-boxed f64 (see `HeapObjectType::Float`). A leaf object: the full
/// double is stored verbatim so container/Any floats round-trip exactly.
/// Discrimination is O(1): the pointer is validated against the shared
/// `HEAP_ALLOCATION_REGISTRY` HashSet (a pure membership test, performed
/// before any `->value`/`->header` dereference), so a stray i64 that merely
/// aliases TAG_HEAP is never dereferenced.
#[repr(C)]
pub struct HeapFloat {
    pub header: HeapHeader,
    pub value: f64,
}

/// GC flag bits stored in HeapHeader::gc_flags
pub mod gc_flags {
    /// Object has not been visited by GC (white in tri-color marking)
    pub const WHITE: u8 = 0b00;
    /// Object is reachable but not yet scanned (gray in tri-color marking)
    pub const GRAY: u8 = 0b01;
    /// Object has been scanned and is definitely reachable (black in tri-color marking)
    pub const BLACK: u8 = 0b10;
    /// Mask for the color bits
    pub const COLOR_MASK: u8 = 0b11;
    /// Object is pinned and should not be moved
    pub const PINNED: u8 = 0b100;
    /// RuntimeArray stores raw u8 bytes in data instead of RuntimeValue slots.
    pub const BYTE_PACKED: u8 = 0b1000;
    /// RuntimeArray stores raw u64 words in data instead of tagged RuntimeValue slots.
    pub const U64_PACKED: u8 = 0b1_0000;
}

impl HeapHeader {
    pub fn new(object_type: HeapObjectType, size: u32) -> Self {
        Self {
            object_type,
            gc_flags: gc_flags::WHITE,
            reserved: 0,
            size,
        }
    }

    /// Get the GC color of this object
    #[inline]
    pub fn gc_color(&self) -> u8 {
        self.gc_flags & gc_flags::COLOR_MASK
    }

    /// Check if this object is white (not yet visited)
    #[inline]
    pub fn is_white(&self) -> bool {
        self.gc_color() == gc_flags::WHITE
    }

    /// Check if this object is gray (reachable, needs scanning)
    #[inline]
    pub fn is_gray(&self) -> bool {
        self.gc_color() == gc_flags::GRAY
    }

    /// Check if this object is black (fully scanned)
    #[inline]
    pub fn is_black(&self) -> bool {
        self.gc_color() == gc_flags::BLACK
    }

    /// Mark this object as gray (reachable, needs scanning)
    #[inline]
    pub fn mark_gray(&mut self) {
        self.gc_flags = (self.gc_flags & !gc_flags::COLOR_MASK) | gc_flags::GRAY;
    }

    /// Mark this object as black (fully scanned)
    #[inline]
    pub fn mark_black(&mut self) {
        self.gc_flags = (self.gc_flags & !gc_flags::COLOR_MASK) | gc_flags::BLACK;
    }

    /// Reset this object to white (for new GC cycle)
    #[inline]
    pub fn reset_color(&mut self) {
        self.gc_flags = (self.gc_flags & !gc_flags::COLOR_MASK) | gc_flags::WHITE;
    }

    /// Check if this object is pinned
    #[inline]
    pub fn is_pinned(&self) -> bool {
        (self.gc_flags & gc_flags::PINNED) != 0
    }

    /// Pin this object (prevent moving)
    #[inline]
    pub fn pin(&mut self) {
        self.gc_flags |= gc_flags::PINNED;
    }

    /// Unpin this object
    #[inline]
    pub fn unpin(&mut self) {
        self.gc_flags &= !gc_flags::PINNED;
    }
}

// ============================================================================
// Shared heap validation utilities
// ============================================================================

use super::core::RuntimeValue;
use std::collections::HashSet;
use std::sync::{Mutex, OnceLock};

const MIN_VALID_HEAP_ADDR: usize = 4096;

static HEAP_ALLOCATION_REGISTRY: OnceLock<Mutex<HashSet<usize>>> = OnceLock::new();

fn heap_allocation_registry() -> &'static Mutex<HashSet<usize>> {
    HEAP_ALLOCATION_REGISTRY.get_or_init(|| Mutex::new(HashSet::new()))
}

#[inline]
pub fn register_heap_ptr(ptr: *mut HeapHeader) {
    if !ptr.is_null() {
        let _ = heap_allocation_registry()
            .lock()
            .map(|mut registry| registry.insert(ptr as usize));
    }
}

#[inline]
pub fn unregister_heap_ptr(ptr: *mut HeapHeader) {
    if !ptr.is_null() {
        let _ = heap_allocation_registry()
            .lock()
            .map(|mut registry| registry.remove(&(ptr as usize)));
    }
}

#[inline]
pub fn is_registered_heap_ptr(ptr: *mut HeapHeader) -> bool {
    heap_allocation_registry()
        .lock()
        .map(|registry| registry.contains(&(ptr as usize)))
        .unwrap_or(false)
}

/// Number of RuntimeValue heap objects known to the hosted runtime.
///
/// This is a diagnostic registry count, not a live-byte measurement: most
/// no-GC compiler temporaries stay registered for the process lifetime.
#[no_mangle]
pub extern "C" fn rt_heap_registry_count() -> i64 {
    heap_allocation_registry()
        .lock()
        .map(|registry| registry.len() as i64)
        .unwrap_or(0)
}

pub fn clear_heap_allocation_registry() {
    if let Some(registry) = HEAP_ALLOCATION_REGISTRY.get() {
        let _ = registry.lock().map(|mut registry| registry.clear());
    }
}

/// Validate heap object type, returns None if invalid
///
/// This is a shared helper to reduce boilerplate in SFFI functions.
#[inline]
pub fn validate_heap_obj(val: RuntimeValue, expected: HeapObjectType) -> Option<*mut HeapHeader> {
    if !val.is_heap() {
        return None;
    }
    let ptr = val.as_heap_ptr();
    let addr = ptr as usize;
    if ptr.is_null() || addr < MIN_VALID_HEAP_ADDR || addr & 0x7 != 0 {
        return None;
    }
    if !is_registered_heap_ptr(ptr) {
        return None;
    }
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

// ============================================================================
// ValueKind conversion
// ============================================================================

impl From<HeapObjectType> for ValueKind {
    fn from(heap_type: HeapObjectType) -> Self {
        match heap_type {
            HeapObjectType::String => ValueKind::String,
            HeapObjectType::Array => ValueKind::Array,
            HeapObjectType::Dict => ValueKind::Dict,
            HeapObjectType::Tuple => ValueKind::Tuple,
            HeapObjectType::Object => ValueKind::Object,
            HeapObjectType::Closure => ValueKind::Closure,
            HeapObjectType::Enum => ValueKind::Enum,
            HeapObjectType::Future => ValueKind::Future,
            HeapObjectType::Generator => ValueKind::Generator,
            HeapObjectType::Actor => ValueKind::Actor,
            HeapObjectType::Unique => ValueKind::Unique,
            HeapObjectType::Shared => ValueKind::Shared,
            HeapObjectType::Borrow => ValueKind::Borrow,
            HeapObjectType::Channel => ValueKind::Channel,
            HeapObjectType::Weak => ValueKind::Weak,
            HeapObjectType::ContractViolation => ValueKind::ContractViolation,
            HeapObjectType::Mutex => ValueKind::Mutex,
            HeapObjectType::RwLock => ValueKind::RwLock,
            HeapObjectType::Semaphore => ValueKind::Semaphore,
            HeapObjectType::Barrier => ValueKind::Barrier,
            HeapObjectType::Atomic => ValueKind::Atomic,
            HeapObjectType::MonoioFuture => ValueKind::MonoioFuture,
            HeapObjectType::HashMap => ValueKind::HashMap,
            HeapObjectType::BTreeMap => ValueKind::BTreeMap,
            HeapObjectType::HashSet => ValueKind::HashSet,
            HeapObjectType::BTreeSet => ValueKind::BTreeSet,
            HeapObjectType::FfiObject => ValueKind::FfiObject,
            // Heap-boxed float presents as a plain float to the value system.
            HeapObjectType::Float => ValueKind::Float,
        }
    }
}
