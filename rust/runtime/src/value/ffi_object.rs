//! FFI object support for object-based FFI system.
//!
//! This module provides the infrastructure for wrapping Rust objects and exposing
//! them to Simple language code through a clean object-oriented interface.
//!
//! # Architecture
//!
//! ```text
//! RuntimeValue (tagged pointer)
//!       │
//!       ▼
//! RuntimeFfiObject (heap-allocated)
//! ┌─────────────────────────────────┐
//! │ HeapHeader                      │  8 bytes
//! │ type_id: u32                    │  4 bytes (registered type ID)
//! │ handle: u32                     │  4 bytes (handle into storage)
//! │ vtable: *const FfiVtable        │  8 bytes (method dispatch table)
//! └─────────────────────────────────┘
//!       │
//!       ▼ (via vtable)
//! FfiVtable
//! ┌─────────────────────────────────┐
//! │ type_name: *const u8            │  Type name for debugging
//! │ type_name_len: u32              │
//! │ method_count: u32               │
//! │ methods: *const FfiMethodEntry  │  Sorted by name_hash
//! │ drop_fn                         │  Destructor
//! │ clone_fn                        │  Clone (optional)
//! └─────────────────────────────────┘
//! ```
//!
//! # Method Dispatch
//!
//! Methods are looked up using FNV-1a hash of the method name, followed by
//! binary search in the sorted method table. This provides O(log n) lookup
//! with excellent cache performance.

use super::core::RuntimeValue;
use super::heap::{HeapHeader, HeapObjectType};

/// FNV-1a hash function for method name lookup.
///
/// This is the 64-bit FNV-1a variant, chosen for:
/// - Excellent distribution for short strings (method names)
/// - Fast computation
/// - Minimal collision rate for typical method name lengths
#[inline]
pub fn fnv1a_hash(s: &[u8]) -> u64 {
    const FNV_OFFSET_BASIS: u64 = 0xcbf29ce484222325;
    const FNV_PRIME: u64 = 0x100000001b3;

    let mut hash = FNV_OFFSET_BASIS;
    for &byte in s {
        hash ^= byte as u64;
        hash = hash.wrapping_mul(FNV_PRIME);
    }
    hash
}

/// FNV-1a hash for string slices.
#[inline]
pub fn fnv1a_hash_str(s: &str) -> u64 {
    fnv1a_hash(s.as_bytes())
}

/// Method entry flags.
pub mod method_flags {
    /// Method takes &self (immutable borrow)
    pub const IMMUTABLE: u32 = 0;
    /// Method takes &mut self (mutable borrow)
    pub const MUTABLE: u32 = 1 << 0;
    /// Method is static (no self parameter)
    pub const STATIC: u32 = 1 << 1;
    /// Method returns a RuntimeValue
    pub const RETURNS_VALUE: u32 = 1 << 2;
    /// Method may fail (returns Result-like)
    pub const MAY_FAIL: u32 = 1 << 3;
}

/// Entry in the FFI method vtable.
///
/// Methods are stored sorted by `name_hash` to enable binary search.
#[repr(C)]
pub struct FfiMethodEntry {
    /// FNV-1a hash of the method name (for fast lookup)
    pub name_hash: u64,
    /// Pointer to the method name string (for debugging/reflection)
    pub name_ptr: *const u8,
    /// Length of the method name
    pub name_len: u32,
    /// Method flags (mutability, return type hints)
    pub flags: u32,
    /// Function pointer (actual signature depends on the method)
    ///
    /// For instance methods: `fn(handle: u32, argc: u32, argv: *const RuntimeValue) -> RuntimeValue`
    /// For static methods: `fn(argc: u32, argv: *const RuntimeValue) -> RuntimeValue`
    pub func_ptr: *const (),
}

impl FfiMethodEntry {
    /// Create a new method entry.
    ///
    /// # Safety
    /// The `name_ptr` must point to valid UTF-8 data that lives at least as long as this entry.
    /// The `func_ptr` must point to a valid function with the appropriate signature.
    pub const fn new(name_hash: u64, name_ptr: *const u8, name_len: u32, flags: u32, func_ptr: *const ()) -> Self {
        Self {
            name_hash,
            name_ptr,
            name_len,
            flags,
            func_ptr,
        }
    }

    /// Get the method name as a string slice.
    ///
    /// # Safety
    /// The name_ptr must point to valid UTF-8 data.
    pub unsafe fn name(&self) -> &str {
        let bytes = std::slice::from_raw_parts(self.name_ptr, self.name_len as usize);
        std::str::from_utf8_unchecked(bytes)
    }

    /// Check if this method is mutable (takes &mut self).
    #[inline]
    pub const fn is_mutable(&self) -> bool {
        self.flags & method_flags::MUTABLE != 0
    }

    /// Check if this method is static (no self parameter).
    #[inline]
    pub const fn is_static(&self) -> bool {
        self.flags & method_flags::STATIC != 0
    }
}

// Safety: FfiMethodEntry is safe to send between threads because it only contains
// raw pointers that point to static data (method names, function pointers).
unsafe impl Send for FfiMethodEntry {}
unsafe impl Sync for FfiMethodEntry {}

/// Virtual table for FFI objects.
///
/// Contains type metadata and method dispatch table.
#[repr(C)]
pub struct FfiVtable {
    /// Type name (for debugging and reflection)
    pub type_name: *const u8,
    /// Length of type name
    pub type_name_len: u32,
    /// Number of methods in the method table
    pub method_count: u32,
    /// Pointer to sorted array of method entries
    pub methods: *const FfiMethodEntry,
    /// Destructor function (called when the FFI object is dropped)
    /// Signature: `fn(handle: u32)`
    pub drop_fn: Option<unsafe extern "C" fn(handle: u32)>,
    /// Clone function (optional, for cloneable types)
    /// Signature: `fn(handle: u32) -> u32` (returns new handle)
    pub clone_fn: Option<unsafe extern "C" fn(handle: u32) -> u32>,
}

impl FfiVtable {
    /// Create a new vtable.
    ///
    /// # Safety
    /// - `type_name` must point to valid UTF-8 data
    /// - `methods` must point to a valid array of `method_count` entries
    /// - `methods` must be sorted by `name_hash`
    pub const fn new(
        type_name: *const u8,
        type_name_len: u32,
        method_count: u32,
        methods: *const FfiMethodEntry,
        drop_fn: Option<unsafe extern "C" fn(handle: u32)>,
        clone_fn: Option<unsafe extern "C" fn(handle: u32) -> u32>,
    ) -> Self {
        Self {
            type_name,
            type_name_len,
            method_count,
            methods,
            drop_fn,
            clone_fn,
        }
    }

    /// Get the type name as a string slice.
    ///
    /// # Safety
    /// The type_name must point to valid UTF-8 data.
    pub unsafe fn name(&self) -> &str {
        let bytes = std::slice::from_raw_parts(self.type_name, self.type_name_len as usize);
        std::str::from_utf8_unchecked(bytes)
    }

    /// Get the method table as a slice.
    pub fn methods(&self) -> &[FfiMethodEntry] {
        if self.methods.is_null() || self.method_count == 0 {
            &[]
        } else {
            unsafe { std::slice::from_raw_parts(self.methods, self.method_count as usize) }
        }
    }

    /// Look up a method by name using binary search on name_hash.
    ///
    /// Returns the method entry and its index if found.
    pub fn lookup_method(&self, method_name: &str) -> Option<&FfiMethodEntry> {
        let hash = fnv1a_hash_str(method_name);
        let methods = self.methods();

        // Binary search on sorted method table
        methods
            .binary_search_by_key(&hash, |m| m.name_hash)
            .ok()
            .map(|idx| &methods[idx])
    }

    /// Check if this type has a specific method.
    #[inline]
    pub fn has_method(&self, method_name: &str) -> bool {
        self.lookup_method(method_name).is_some()
    }
}

// Safety: FfiVtable is safe to send between threads because it only contains
// raw pointers that point to static data.
unsafe impl Send for FfiVtable {}
unsafe impl Sync for FfiVtable {}

/// FFI object representation on the heap.
///
/// This structure wraps a Rust object that has been registered with the FFI system.
/// The actual object is stored in the `FfiTypeRegistry` and referenced via `handle`.
#[repr(C)]
pub struct RuntimeFfiObject {
    /// Heap header (required for all heap objects)
    pub header: HeapHeader,
    /// Registered type ID (from FfiTypeRegistry)
    pub type_id: u32,
    /// Handle into the type's storage (from FfiTypeRegistry)
    pub handle: u32,
    /// Pointer to the vtable for method dispatch
    pub vtable: *const FfiVtable,
}

impl RuntimeFfiObject {
    /// Size of RuntimeFfiObject in bytes (for allocation)
    pub const SIZE: usize = std::mem::size_of::<Self>();

    /// Create a new FFI object.
    ///
    /// # Safety
    /// The vtable pointer must be valid for the lifetime of this object.
    pub fn new(type_id: u32, handle: u32, vtable: *const FfiVtable) -> Self {
        Self {
            header: HeapHeader::new(HeapObjectType::FfiObject, Self::SIZE as u32),
            type_id,
            handle,
            vtable,
        }
    }

    /// Get the vtable for this object.
    ///
    /// # Safety
    /// The vtable pointer must be valid.
    pub unsafe fn vtable(&self) -> &FfiVtable {
        &*self.vtable
    }

    /// Get the type name of this object.
    ///
    /// # Safety
    /// The vtable and type name pointer must be valid.
    pub unsafe fn type_name(&self) -> &str {
        self.vtable().name()
    }

    /// Look up a method by name.
    ///
    /// # Safety
    /// The vtable must be valid.
    pub unsafe fn lookup_method(&self, method_name: &str) -> Option<&FfiMethodEntry> {
        self.vtable().lookup_method(method_name)
    }
}

// ============================================================================
// FFI Functions for RuntimeFfiObject
// ============================================================================

use std::alloc::{Layout, alloc_zeroed, dealloc};

/// Allocate a new FFI object on the heap.
///
/// # Safety
/// The vtable pointer must be valid and live for the lifetime of the object.
///
/// # Returns
/// A RuntimeValue containing the FFI object, or NIL on allocation failure.
#[no_mangle]
pub unsafe extern "C" fn rt_ffi_object_new(type_id: u32, handle: u32, vtable: *const FfiVtable) -> RuntimeValue {
    if vtable.is_null() {
        return RuntimeValue::NIL;
    }

    let layout = Layout::from_size_align(RuntimeFfiObject::SIZE, 8).unwrap();
    let ptr = alloc_zeroed(layout) as *mut RuntimeFfiObject;

    if ptr.is_null() {
        return RuntimeValue::NIL;
    }

    // Initialize the object
    std::ptr::write(ptr, RuntimeFfiObject::new(type_id, handle, vtable));

    RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader)
}

/// Free an FFI object.
///
/// This deallocates the heap memory but does NOT call the drop_fn.
/// The drop_fn should be called separately to clean up the underlying Rust object.
///
/// # Safety
/// The value must be a valid FFI object.
#[no_mangle]
pub unsafe extern "C" fn rt_ffi_object_free(value: RuntimeValue) {
    if !value.is_heap() {
        return;
    }

    let ptr = value.as_heap_ptr();
    if ptr.is_null() {
        return;
    }

    if (*ptr).object_type != HeapObjectType::FfiObject {
        return;
    }

    let layout = Layout::from_size_align(RuntimeFfiObject::SIZE, 8).unwrap();
    dealloc(ptr as *mut u8, layout);
}

/// Get the type ID of an FFI object.
///
/// # Returns
/// The type ID, or 0 if the value is not an FFI object.
#[no_mangle]
pub extern "C" fn rt_ffi_object_type_id(value: RuntimeValue) -> u32 {
    get_ffi_object(value).map(|obj| obj.type_id).unwrap_or(0)
}

/// Get the handle of an FFI object.
///
/// # Returns
/// The handle, or 0 if the value is not an FFI object.
#[no_mangle]
pub extern "C" fn rt_ffi_object_handle(value: RuntimeValue) -> u32 {
    get_ffi_object(value).map(|obj| obj.handle).unwrap_or(0)
}

/// Get the vtable pointer of an FFI object.
///
/// # Returns
/// The vtable pointer, or null if the value is not an FFI object.
#[no_mangle]
pub extern "C" fn rt_ffi_object_vtable(value: RuntimeValue) -> *const FfiVtable {
    get_ffi_object(value).map(|obj| obj.vtable).unwrap_or(std::ptr::null())
}

/// Check if a value is an FFI object.
#[no_mangle]
pub extern "C" fn rt_ffi_object_is_ffi(value: RuntimeValue) -> bool {
    get_ffi_object(value).is_some()
}

/// Get the type name of an FFI object as a RuntimeValue string.
///
/// # Returns
/// A RuntimeValue containing the type name string, or NIL if not an FFI object.
#[no_mangle]
pub extern "C" fn rt_ffi_object_type_name(value: RuntimeValue) -> RuntimeValue {
    let Some(obj) = get_ffi_object(value) else {
        return RuntimeValue::NIL;
    };

    unsafe {
        let vtable = &*obj.vtable;
        let name = vtable.name();
        super::collections::rt_string_new(name.as_ptr(), name.len() as u64)
    }
}

/// Check if an FFI object has a specific method.
///
/// # Parameters
/// - `value`: The FFI object
/// - `name_ptr`: Pointer to the method name (UTF-8)
/// - `name_len`: Length of the method name
///
/// # Returns
/// `true` if the method exists, `false` otherwise.
#[no_mangle]
pub extern "C" fn rt_ffi_object_has_method(value: RuntimeValue, name_ptr: *const u8, name_len: u32) -> bool {
    let Some(obj) = get_ffi_object(value) else {
        return false;
    };

    if name_ptr.is_null() {
        return false;
    }

    unsafe {
        let name = std::slice::from_raw_parts(name_ptr, name_len as usize);
        let name_str = std::str::from_utf8_unchecked(name);
        (*obj.vtable).has_method(name_str)
    }
}

/// Call a method on an FFI object.
///
/// # Parameters
/// - `value`: The FFI object
/// - `name_ptr`: Pointer to the method name (UTF-8)
/// - `name_len`: Length of the method name
/// - `argc`: Number of arguments
/// - `argv`: Pointer to the argument array
///
/// # Returns
/// The result of the method call, or NIL if the method doesn't exist.
///
/// # Safety
/// - `name_ptr` must point to valid UTF-8 data
/// - `argv` must point to a valid array of `argc` RuntimeValues (if argc > 0)
#[no_mangle]
pub unsafe extern "C" fn rt_ffi_object_call_method(
    value: RuntimeValue,
    name_ptr: *const u8,
    name_len: u32,
    argc: u32,
    argv: *const RuntimeValue,
) -> RuntimeValue {
    let Some(obj) = get_ffi_object(value) else {
        return RuntimeValue::NIL;
    };

    if name_ptr.is_null() {
        return RuntimeValue::NIL;
    }

    let name = std::slice::from_raw_parts(name_ptr, name_len as usize);
    let name_str = std::str::from_utf8_unchecked(name);

    let vtable = &*obj.vtable;
    let Some(method) = vtable.lookup_method(name_str) else {
        return RuntimeValue::NIL;
    };

    // Get the function pointer and call it
    // For instance methods: fn(handle: u32, argc: u32, argv: *const RuntimeValue) -> RuntimeValue
    type InstanceMethodFn = unsafe extern "C" fn(u32, u32, *const RuntimeValue) -> RuntimeValue;

    let func = std::mem::transmute::<*const (), InstanceMethodFn>(method.func_ptr);
    func(obj.handle, argc, argv)
}

// ============================================================================
// Helper Functions
// ============================================================================

/// Get a reference to the RuntimeFfiObject from a RuntimeValue.
fn get_ffi_object(value: RuntimeValue) -> Option<&'static RuntimeFfiObject> {
    if !value.is_heap() {
        return None;
    }

    let ptr = value.as_heap_ptr();
    if ptr.is_null() {
        return None;
    }

    unsafe {
        if (*ptr).object_type != HeapObjectType::FfiObject {
            return None;
        }
        Some(&*(ptr as *const RuntimeFfiObject))
    }
}

/// Get a mutable reference to the RuntimeFfiObject from a RuntimeValue.
#[allow(dead_code)]
fn get_ffi_object_mut(value: RuntimeValue) -> Option<&'static mut RuntimeFfiObject> {
    if !value.is_heap() {
        return None;
    }

    let ptr = value.as_heap_ptr();
    if ptr.is_null() {
        return None;
    }

    unsafe {
        if (*ptr).object_type != HeapObjectType::FfiObject {
            return None;
        }
        Some(&mut *(ptr as *mut RuntimeFfiObject))
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fnv1a_hash() {
        // Known FNV-1a 64-bit test vectors
        assert_eq!(fnv1a_hash(b""), 0xcbf29ce484222325);
        assert_eq!(fnv1a_hash(b"a"), 0xaf63dc4c8601ec8c);
        assert_eq!(fnv1a_hash(b"foo"), 0xdcb27518fed9d577);

        // Method names should have different hashes
        let hash1 = fnv1a_hash_str("open");
        let hash2 = fnv1a_hash_str("close");
        let hash3 = fnv1a_hash_str("query");
        assert_ne!(hash1, hash2);
        assert_ne!(hash2, hash3);
        assert_ne!(hash1, hash3);
    }

    #[test]
    #[allow(clippy::manual_c_str_literals)]
    fn test_method_entry_flags() {
        let entry = FfiMethodEntry::new(
            fnv1a_hash_str("test"),
            b"test\0".as_ptr(),
            4,
            method_flags::MUTABLE | method_flags::RETURNS_VALUE,
            std::ptr::null(),
        );

        assert!(entry.is_mutable());
        assert!(!entry.is_static());
    }

    #[test]
    #[allow(clippy::manual_c_str_literals)]
    fn test_vtable_lookup() {
        // Create a sorted method table
        static METHODS: [FfiMethodEntry; 3] = [
            // Sorted by name_hash
            FfiMethodEntry {
                name_hash: 0x1000, // Fake hash for testing
                name_ptr: b"a\0".as_ptr(),
                name_len: 1,
                flags: 0,
                func_ptr: std::ptr::null(),
            },
            FfiMethodEntry {
                name_hash: 0x2000,
                name_ptr: b"b\0".as_ptr(),
                name_len: 1,
                flags: 0,
                func_ptr: std::ptr::null(),
            },
            FfiMethodEntry {
                name_hash: 0x3000,
                name_ptr: b"c\0".as_ptr(),
                name_len: 1,
                flags: 0,
                func_ptr: std::ptr::null(),
            },
        ];

        let vtable = FfiVtable::new(b"Test\0".as_ptr(), 4, 3, METHODS.as_ptr(), None, None);

        assert_eq!(vtable.methods().len(), 3);
        assert!(unsafe { vtable.name() } == "Test");
    }

    #[test]
    fn test_runtime_ffi_object_size() {
        // Verify size is as expected (8 + 4 + 4 + 8 = 24 bytes)
        assert_eq!(RuntimeFfiObject::SIZE, 24);
    }
}
