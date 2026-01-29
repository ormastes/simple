//! Object types: Object, Closure, Enum and their FFI functions.

use super::core::RuntimeValue;
use super::heap::{get_typed_ptr, get_typed_ptr_mut, HeapHeader, HeapObjectType};

// ============================================================================
// Heap-allocated object structures
// ============================================================================

/// A heap-allocated closure
#[repr(C)]
pub struct RuntimeClosure {
    pub header: HeapHeader,
    /// Pointer to the compiled function
    pub func_ptr: *const u8,
    /// Number of captured variables
    pub capture_count: u32,
    /// Reserved for alignment
    pub reserved: u32,
    // Followed by captured RuntimeValue elements
}

impl RuntimeClosure {
    /// Get the captured values as a slice
    ///
    /// # Safety
    /// The caller must ensure the RuntimeClosure was properly allocated.
    pub unsafe fn captures(&self) -> &[RuntimeValue] {
        let data_ptr = (self as *const Self).add(1) as *const RuntimeValue;
        std::slice::from_raw_parts(data_ptr, self.capture_count as usize)
    }

    /// Get the captured values as a mutable slice
    ///
    /// # Safety
    /// The caller must ensure the RuntimeClosure was properly allocated.
    pub unsafe fn captures_mut(&mut self) -> &mut [RuntimeValue] {
        let data_ptr = (self as *mut Self).add(1) as *mut RuntimeValue;
        std::slice::from_raw_parts_mut(data_ptr, self.capture_count as usize)
    }
}

/// A heap-allocated object (class/struct instance)
#[repr(C)]
pub struct RuntimeObject {
    pub header: HeapHeader,
    /// Class ID (index into class metadata table)
    pub class_id: u32,
    /// Number of fields
    pub field_count: u32,
    // Followed by field RuntimeValue elements (indexed by field order)
}

impl RuntimeObject {
    /// Get the fields as a slice
    ///
    /// # Safety
    /// The caller must ensure the RuntimeObject was properly allocated.
    pub unsafe fn fields(&self) -> &[RuntimeValue] {
        let data_ptr = (self as *const Self).add(1) as *const RuntimeValue;
        std::slice::from_raw_parts(data_ptr, self.field_count as usize)
    }

    /// Get the fields as a mutable slice
    ///
    /// # Safety
    /// The caller must ensure the RuntimeObject was properly allocated.
    pub unsafe fn fields_mut(&mut self) -> &mut [RuntimeValue] {
        let data_ptr = (self as *mut Self).add(1) as *mut RuntimeValue;
        std::slice::from_raw_parts_mut(data_ptr, self.field_count as usize)
    }
}

/// A heap-allocated enum variant
#[repr(C)]
pub struct RuntimeEnum {
    pub header: HeapHeader,
    /// Enum type ID
    pub enum_id: u32,
    /// Variant discriminant
    pub discriminant: u32,
    /// Payload (NIL if no payload)
    pub payload: RuntimeValue,
}

// ============================================================================
// Object FFI functions
// ============================================================================

/// Allocate a new object with the given number of fields
#[no_mangle]
pub extern "C" fn rt_object_new(class_id: u32, field_count: u32) -> RuntimeValue {
    let size = std::mem::size_of::<RuntimeObject>() + field_count as usize * std::mem::size_of::<RuntimeValue>();
    let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();

    unsafe {
        let ptr = std::alloc::alloc_zeroed(layout) as *mut RuntimeObject;
        if ptr.is_null() {
            return RuntimeValue::NIL;
        }

        (*ptr).header = HeapHeader::new(HeapObjectType::Object, size as u32);
        (*ptr).class_id = class_id;
        (*ptr).field_count = field_count;

        // Initialize all fields to NIL
        let fields = (*ptr).fields_mut();
        for field in fields {
            *field = RuntimeValue::NIL;
        }

        RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader)
    }
}

/// Get a field from an object by index
#[no_mangle]
pub extern "C" fn rt_object_field_get(object: RuntimeValue, field_index: u32) -> RuntimeValue {
    let Some(obj) = get_typed_ptr::<RuntimeObject>(object, HeapObjectType::Object) else {
        return RuntimeValue::NIL;
    };
    unsafe {
        if field_index >= (*obj).field_count {
            return RuntimeValue::NIL;
        }
        (*obj).fields()[field_index as usize]
    }
}

/// Set a field on an object by index
#[no_mangle]
pub extern "C" fn rt_object_field_set(object: RuntimeValue, field_index: u32, value: RuntimeValue) -> bool {
    let Some(obj) = get_typed_ptr_mut::<RuntimeObject>(object, HeapObjectType::Object) else {
        return false;
    };
    unsafe {
        if field_index >= (*obj).field_count {
            return false;
        }
        (*obj).fields_mut()[field_index as usize] = value;
        true
    }
}

/// Get the class ID of an object
#[no_mangle]
pub extern "C" fn rt_object_class_id(object: RuntimeValue) -> i64 {
    get_typed_ptr::<RuntimeObject>(object, HeapObjectType::Object).map_or(-1, |p| unsafe { (*p).class_id as i64 })
}

/// Get the field count of an object
#[no_mangle]
pub extern "C" fn rt_object_field_count(object: RuntimeValue) -> i64 {
    get_typed_ptr::<RuntimeObject>(object, HeapObjectType::Object).map_or(-1, |p| unsafe { (*p).field_count as i64 })
}

// ============================================================================
// Closure FFI functions
// ============================================================================

/// Allocate a new closure with the given function pointer and captures
#[no_mangle]
pub extern "C" fn rt_closure_new(func_ptr: *const u8, capture_count: u32) -> RuntimeValue {
    let size = std::mem::size_of::<RuntimeClosure>() + capture_count as usize * std::mem::size_of::<RuntimeValue>();
    let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();

    unsafe {
        let ptr = std::alloc::alloc_zeroed(layout) as *mut RuntimeClosure;
        if ptr.is_null() {
            return RuntimeValue::NIL;
        }

        (*ptr).header = HeapHeader::new(HeapObjectType::Closure, size as u32);
        (*ptr).func_ptr = func_ptr;
        (*ptr).capture_count = capture_count;
        (*ptr).reserved = 0;

        RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader)
    }
}

/// Set a captured variable in a closure
#[no_mangle]
pub extern "C" fn rt_closure_set_capture(closure: RuntimeValue, index: u32, value: RuntimeValue) -> bool {
    let Some(clos) = get_typed_ptr_mut::<RuntimeClosure>(closure, HeapObjectType::Closure) else {
        return false;
    };
    unsafe {
        if index >= (*clos).capture_count {
            return false;
        }
        (*clos).captures_mut()[index as usize] = value;
        true
    }
}

/// Get a captured variable from a closure
#[no_mangle]
pub extern "C" fn rt_closure_get_capture(closure: RuntimeValue, index: u32) -> RuntimeValue {
    let Some(clos) = get_typed_ptr::<RuntimeClosure>(closure, HeapObjectType::Closure) else {
        return RuntimeValue::NIL;
    };
    unsafe {
        if index >= (*clos).capture_count {
            return RuntimeValue::NIL;
        }
        (*clos).captures()[index as usize]
    }
}

/// Get the function pointer from a closure
#[no_mangle]
pub extern "C" fn rt_closure_func_ptr(closure: RuntimeValue) -> *const u8 {
    get_typed_ptr::<RuntimeClosure>(closure, HeapObjectType::Closure)
        .map_or(std::ptr::null(), |p| unsafe { (*p).func_ptr })
}

// ============================================================================
// Enum FFI functions
// ============================================================================

/// Hash a variant name to get its discriminant, matching the compiler's hashing scheme.
pub fn hash_variant_discriminant(variant_name: &str) -> u32 {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    let mut hasher = DefaultHasher::new();
    variant_name.hash(&mut hasher);
    (hasher.finish() & 0xFFFFFFFF) as u32
}

/// Allocate a new enum value
#[no_mangle]
pub extern "C" fn rt_enum_new(enum_id: u32, discriminant: u32, payload: RuntimeValue) -> RuntimeValue {
    let size = std::mem::size_of::<RuntimeEnum>();
    let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();

    unsafe {
        let ptr = std::alloc::alloc(layout) as *mut RuntimeEnum;
        if ptr.is_null() {
            return RuntimeValue::NIL;
        }

        (*ptr).header = HeapHeader::new(HeapObjectType::Enum, size as u32);
        (*ptr).enum_id = enum_id;
        (*ptr).discriminant = discriminant;
        (*ptr).payload = payload;

        RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader)
    }
}

/// Get the discriminant of an enum value
#[no_mangle]
pub extern "C" fn rt_enum_discriminant(value: RuntimeValue) -> i64 {
    get_typed_ptr::<RuntimeEnum>(value, HeapObjectType::Enum).map_or(-1, |p| unsafe { (*p).discriminant as i64 })
}

/// Check if an enum value has the expected discriminant
#[no_mangle]
pub extern "C" fn rt_enum_check_discriminant(value: RuntimeValue, expected: i64) -> bool {
    get_typed_ptr::<RuntimeEnum>(value, HeapObjectType::Enum)
        .map_or(false, |p| unsafe {
            (*p).discriminant as i64 == expected
        })
}

/// Unwrap an optional value: if it's a Some enum, return its payload; otherwise return as-is.
/// Used by the `??` operator's then-branch to unwrap Option values.
#[no_mangle]
pub extern "C" fn rt_unwrap_or_self(value: RuntimeValue) -> RuntimeValue {
    if let Some(p) = get_typed_ptr::<RuntimeEnum>(value, HeapObjectType::Enum) {
        unsafe { (*p).payload }
    } else {
        // Not an enum — return the value itself (could be a raw string, int, etc.)
        value
    }
}

/// Get the payload of an enum value
#[no_mangle]
pub extern "C" fn rt_enum_payload(value: RuntimeValue) -> RuntimeValue {
    let result = get_typed_ptr::<RuntimeEnum>(value, HeapObjectType::Enum)
        .map_or(RuntimeValue::NIL, |p| unsafe { (*p).payload });
    result
}

/// Check if a value is None/nil.
/// Returns true if:
/// - value is nil (raw 0 / TAG_SPECIAL with SPECIAL_NIL)
/// - value is an enum with discriminant hash("None")
#[no_mangle]
pub extern "C" fn rt_is_none(value: RuntimeValue) -> bool {
    // Check for raw nil (value == 0 or TAG_SPECIAL with NIL)
    if value.0 == 0 || value.0 == super::tags::TAG_SPECIAL as u64 {
        return true;
    }
    if value.is_nil() {
        return true;
    }
    // Check for enum None variant
    rt_enum_check_discriminant(value, {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        let mut hasher = DefaultHasher::new();
        "None".hash(&mut hasher);
        (hasher.finish() & 0xFFFFFFFF) as i64
    })
}

/// Check if a value is Some (not None/nil).
#[no_mangle]
pub extern "C" fn rt_is_some(value: RuntimeValue) -> bool {
    !rt_is_none(value)
}

/// Map over an Option value: if Some(x), apply closure to x and return Some(result).
/// If None/nil, return None.
/// The closure is a RuntimeValue containing a function pointer (RuntimeClosure).
#[no_mangle]
pub extern "C" fn rt_option_map(value: RuntimeValue, closure: RuntimeValue) -> RuntimeValue {
    eprintln!("[rt_option_map] value={:#x} closure={:#x} is_none={} is_nil={} is_heap={}",
        value.to_raw(), closure.to_raw(), rt_is_none(value), value.is_nil(), value.is_heap());

    // If None/nil, return as-is
    if rt_is_none(value) {
        eprintln!("[rt_option_map] value is None, returning as-is");
        return value;
    }

    // Extract the payload from Some(x)
    let payload = rt_enum_payload(value);
    eprintln!("[rt_option_map] payload={:#x}", payload.to_raw());

    // Get function pointer from closure
    let func_ptr = rt_closure_func_ptr(closure);
    eprintln!("[rt_option_map] func_ptr={:?} closure_is_heap={}", func_ptr, closure.is_heap());
    if func_ptr.is_null() {
        eprintln!("[rt_option_map] func_ptr is null, returning NIL");
        return RuntimeValue::NIL;
    }

    // Call the closure: fn(closure, payload) -> RuntimeValue
    // Closures are called with the closure itself as first arg (for captures) and the value as second
    eprintln!("[rt_option_map] calling closure...");
    let func: extern "C" fn(RuntimeValue, RuntimeValue) -> RuntimeValue =
        unsafe { std::mem::transmute(func_ptr) };
    let result = func(closure, payload);
    eprintln!("[rt_option_map] closure returned {:#x}", result.to_raw());

    // Wrap result in Some
    let some_disc = hash_variant_discriminant("Some");
    rt_enum_new(0, some_disc, result)
}

// ============================================================================
// Unique Pointer - Heap structure and FFI functions
// ============================================================================
//
// Unique pointers provide single-owner semantics with RAII cleanup.
// They collaborate with GC by registering as roots when containing GC-managed values.

use crate::memory::gc::{register_unique_root, unregister_unique_root};

/// A heap-allocated unique pointer with GC root registration capability.
///
/// When the contained value references GC-managed objects, this unique pointer
/// registers as a GC root to prevent those objects from being collected.
#[repr(C)]
pub struct RuntimeUnique {
    pub header: HeapHeader,
    /// The wrapped RuntimeValue
    pub value: RuntimeValue,
    /// Flag indicating if GC tracing is needed (1 = yes, 0 = no)
    pub needs_trace: u8,
    /// Reserved for alignment
    pub reserved: [u8; 7],
}

/// Allocate a new unique pointer wrapping the given value.
/// If the value contains heap references, the unique pointer is registered as a GC root.
#[no_mangle]
pub extern "C" fn rt_unique_new(value: RuntimeValue) -> RuntimeValue {
    let size = std::mem::size_of::<RuntimeUnique>();
    let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();

    unsafe {
        let ptr = std::alloc::alloc_zeroed(layout) as *mut RuntimeUnique;
        if ptr.is_null() {
            return RuntimeValue::NIL;
        }

        (*ptr).header = HeapHeader::new(HeapObjectType::Unique, size as u32);
        (*ptr).value = value;
        (*ptr).needs_trace = if value.is_heap() { 1 } else { 0 };
        (*ptr).reserved = [0; 7];

        // Register as GC root if value contains heap references
        if (*ptr).needs_trace != 0 {
            register_unique_root(ptr as *mut u8);
        }

        RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader)
    }
}

/// Get the value inside a unique pointer (read-only).
#[no_mangle]
pub extern "C" fn rt_unique_get(unique: RuntimeValue) -> RuntimeValue {
    let Some(ptr) = get_typed_ptr::<RuntimeUnique>(unique, HeapObjectType::Unique) else {
        return RuntimeValue::NIL;
    };
    unsafe { (*ptr).value }
}

/// Set the value inside a unique pointer (mutable access / update).
/// Updates GC root registration if the new value's heap status differs.
#[no_mangle]
pub extern "C" fn rt_unique_set(unique: RuntimeValue, new_value: RuntimeValue) -> RuntimeValue {
    let Some(ptr) = get_typed_ptr_mut::<RuntimeUnique>(unique, HeapObjectType::Unique) else {
        return RuntimeValue::from_bool(false);
    };
    unsafe {
        let old_needs_trace = (*ptr).needs_trace;
        let new_needs_trace = if new_value.is_heap() { 1 } else { 0 };

        (*ptr).value = new_value;
        (*ptr).needs_trace = new_needs_trace;

        // Update GC root registration if needed
        if old_needs_trace == 0 && new_needs_trace != 0 {
            // Newly needs tracing, register as root
            register_unique_root(ptr as *mut u8);
        } else if old_needs_trace != 0 && new_needs_trace == 0 {
            // No longer needs tracing, unregister from roots
            unregister_unique_root(ptr as *mut u8);
        }

        RuntimeValue::from_bool(true)
    }
}

/// Free a unique pointer and unregister from GC roots.
#[no_mangle]
pub extern "C" fn rt_unique_free(unique: RuntimeValue) {
    let Some(ptr) = get_typed_ptr_mut::<RuntimeUnique>(unique, HeapObjectType::Unique) else {
        return;
    };
    unsafe {
        // Unregister from GC roots if it was registered
        if (*ptr).needs_trace != 0 {
            unregister_unique_root(ptr as *mut u8);
        }

        let size = std::mem::size_of::<RuntimeUnique>();
        let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();
        std::alloc::dealloc(ptr as *mut u8, layout);
    }
}

/// Check if unique pointer needs GC tracing.
#[no_mangle]
pub extern "C" fn rt_unique_needs_trace(unique: RuntimeValue) -> RuntimeValue {
    let Some(ptr) = get_typed_ptr::<RuntimeUnique>(unique, HeapObjectType::Unique) else {
        return RuntimeValue::from_bool(false);
    };
    unsafe { RuntimeValue::from_bool((*ptr).needs_trace != 0) }
}

// ============================================================================
// Shared Pointer - Heap structure and FFI functions
// ============================================================================
//
// Shared pointers (*T) provide reference-counted ownership semantics.
// Multiple owners can share the same value. The value is freed when
// the last owner releases it (ref count drops to 0).

use crate::memory::gc::{register_shared_root, unregister_shared_root};
use std::sync::atomic::{AtomicU64, Ordering};

/// A heap-allocated shared (reference-counted) pointer with GC root registration.
///
/// When the contained value references GC-managed objects, this shared pointer
/// registers as a GC root to prevent those objects from being collected.
#[repr(C)]
pub struct RuntimeShared {
    pub header: HeapHeader,
    /// The wrapped RuntimeValue
    pub value: RuntimeValue,
    /// Reference count (atomic for thread safety)
    pub ref_count: AtomicU64,
    /// Flag indicating if GC tracing is needed (1 = yes, 0 = no)
    pub needs_trace: u8,
    /// Reserved for alignment
    pub reserved: [u8; 7],
}

/// Allocate a new shared pointer wrapping the given value.
/// Initial reference count is 1.
#[no_mangle]
pub extern "C" fn rt_shared_new(value: RuntimeValue) -> RuntimeValue {
    let size = std::mem::size_of::<RuntimeShared>();
    let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();

    unsafe {
        let ptr = std::alloc::alloc_zeroed(layout) as *mut RuntimeShared;
        if ptr.is_null() {
            return RuntimeValue::NIL;
        }

        (*ptr).header = HeapHeader::new(HeapObjectType::Shared, size as u32);
        (*ptr).value = value;
        (*ptr).ref_count = AtomicU64::new(1);
        (*ptr).needs_trace = if value.is_heap() { 1 } else { 0 };
        (*ptr).reserved = [0; 7];

        // Register as GC root if value contains heap references
        if (*ptr).needs_trace != 0 {
            register_shared_root(ptr as *mut u8);
        }

        RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader)
    }
}

/// Get the value inside a shared pointer (read-only).
#[no_mangle]
pub extern "C" fn rt_shared_get(shared: RuntimeValue) -> RuntimeValue {
    let Some(ptr) = get_typed_ptr::<RuntimeShared>(shared, HeapObjectType::Shared) else {
        return RuntimeValue::NIL;
    };
    unsafe { (*ptr).value }
}

/// Increment the reference count (clone the shared pointer).
/// Returns the same shared pointer value.
#[no_mangle]
pub extern "C" fn rt_shared_clone(shared: RuntimeValue) -> RuntimeValue {
    let Some(ptr) = get_typed_ptr::<RuntimeShared>(shared, HeapObjectType::Shared) else {
        return RuntimeValue::NIL;
    };
    unsafe {
        (*ptr).ref_count.fetch_add(1, Ordering::SeqCst);
    }
    shared
}

/// Get the current reference count.
#[no_mangle]
pub extern "C" fn rt_shared_ref_count(shared: RuntimeValue) -> RuntimeValue {
    let Some(ptr) = get_typed_ptr::<RuntimeShared>(shared, HeapObjectType::Shared) else {
        return RuntimeValue::from_int(-1);
    };
    unsafe { RuntimeValue::from_int((*ptr).ref_count.load(Ordering::SeqCst) as i64) }
}

/// Decrement the reference count and free if it reaches zero.
/// Returns true if the shared pointer was freed, false otherwise.
#[no_mangle]
pub extern "C" fn rt_shared_release(shared: RuntimeValue) -> RuntimeValue {
    let Some(ptr) = get_typed_ptr_mut::<RuntimeShared>(shared, HeapObjectType::Shared) else {
        return RuntimeValue::from_bool(false);
    };
    unsafe {
        let old_count = (*ptr).ref_count.fetch_sub(1, Ordering::SeqCst);
        if old_count == 1 {
            // Last reference, free the memory
            if (*ptr).needs_trace != 0 {
                unregister_shared_root(ptr as *mut u8);
            }
            let size = std::mem::size_of::<RuntimeShared>();
            let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();
            std::alloc::dealloc(ptr as *mut u8, layout);
            RuntimeValue::from_bool(true)
        } else {
            RuntimeValue::from_bool(false)
        }
    }
}

/// Check if shared pointer needs GC tracing.
#[no_mangle]
pub extern "C" fn rt_shared_needs_trace(shared: RuntimeValue) -> RuntimeValue {
    let Some(ptr) = get_typed_ptr::<RuntimeShared>(shared, HeapObjectType::Shared) else {
        return RuntimeValue::from_bool(false);
    };
    unsafe { RuntimeValue::from_bool((*ptr).needs_trace != 0) }
}

/// Create a weak pointer from a shared pointer.
/// The weak pointer does not increment the reference count.
#[no_mangle]
pub extern "C" fn rt_shared_downgrade(shared: RuntimeValue) -> RuntimeValue {
    let Some(ptr) = get_typed_ptr::<RuntimeShared>(shared, HeapObjectType::Shared) else {
        return RuntimeValue::NIL;
    };
    // Create a weak pointer that references this shared pointer
    rt_weak_new(shared, ptr as *const u8 as u64)
}

// ============================================================================
// Weak Pointer - Heap structure and FFI functions
// ============================================================================
//
// Weak pointers (-T) are non-owning references to shared pointers.
// They do not affect the reference count and can become dangling
// if all strong (shared) references are released.

/// A heap-allocated weak pointer referencing a shared pointer.
///
/// Weak pointers store the address of a RuntimeShared and check validity
/// before dereferencing.
#[repr(C)]
pub struct RuntimeWeak {
    pub header: HeapHeader,
    /// Address of the RuntimeShared this weak pointer references
    pub shared_addr: u64,
    /// The original shared RuntimeValue (for type checking)
    pub shared_value: RuntimeValue,
}

/// Allocate a new weak pointer referencing a shared pointer.
/// Internal function - use rt_shared_downgrade instead.
#[no_mangle]
pub extern "C" fn rt_weak_new(shared_value: RuntimeValue, shared_addr: u64) -> RuntimeValue {
    let size = std::mem::size_of::<RuntimeWeak>();
    let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();

    unsafe {
        let ptr = std::alloc::alloc_zeroed(layout) as *mut RuntimeWeak;
        if ptr.is_null() {
            return RuntimeValue::NIL;
        }

        (*ptr).header = HeapHeader::new(HeapObjectType::Borrow, size as u32);
        (*ptr).shared_addr = shared_addr;
        (*ptr).shared_value = shared_value;

        RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader)
    }
}

/// Attempt to upgrade a weak pointer to a shared pointer.
/// Returns NIL if the shared pointer has been freed.
/// If successful, increments the reference count and returns the shared pointer.
#[no_mangle]
pub extern "C" fn rt_weak_upgrade(weak: RuntimeValue) -> RuntimeValue {
    let Some(weak_ptr) = get_typed_ptr::<RuntimeWeak>(weak, HeapObjectType::Borrow) else {
        return RuntimeValue::NIL;
    };
    unsafe {
        let shared_addr = (*weak_ptr).shared_addr;
        if shared_addr == 0 {
            return RuntimeValue::NIL;
        }

        // Validate the shared pointer is still valid
        let shared_ptr = shared_addr as *const RuntimeShared;

        // Check if the header still indicates a shared pointer
        if (*shared_ptr).header.object_type != HeapObjectType::Shared {
            return RuntimeValue::NIL;
        }

        // Check if reference count is > 0 (not freed)
        let ref_count = (*shared_ptr).ref_count.load(Ordering::SeqCst);
        if ref_count == 0 {
            return RuntimeValue::NIL;
        }

        // Increment reference count and return the shared pointer
        (*shared_ptr).ref_count.fetch_add(1, Ordering::SeqCst);
        (*weak_ptr).shared_value
    }
}

/// Check if the weak pointer is still valid (shared pointer exists).
#[no_mangle]
pub extern "C" fn rt_weak_is_valid(weak: RuntimeValue) -> RuntimeValue {
    let Some(weak_ptr) = get_typed_ptr::<RuntimeWeak>(weak, HeapObjectType::Borrow) else {
        return RuntimeValue::from_bool(false);
    };
    unsafe {
        let shared_addr = (*weak_ptr).shared_addr;
        if shared_addr == 0 {
            return RuntimeValue::from_bool(false);
        }

        let shared_ptr = shared_addr as *const RuntimeShared;

        // Check header type and reference count
        if (*shared_ptr).header.object_type != HeapObjectType::Shared {
            return RuntimeValue::from_bool(false);
        }

        let ref_count = (*shared_ptr).ref_count.load(Ordering::SeqCst);
        RuntimeValue::from_bool(ref_count > 0)
    }
}

/// Free a weak pointer.
/// This does not affect the shared pointer's reference count.
#[no_mangle]
pub extern "C" fn rt_weak_free(weak: RuntimeValue) {
    let Some(ptr) = get_typed_ptr_mut::<RuntimeWeak>(weak, HeapObjectType::Borrow) else {
        return;
    };
    unsafe {
        let size = std::mem::size_of::<RuntimeWeak>();
        let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();
        std::alloc::dealloc(ptr as *mut u8, layout);
    }
}

// ============================================================================
// Handle Pointer - Heap structure and FFI functions
// ============================================================================
//
// Handle pointers are pool-allocated index-based references. They provide
// fast allocation from a pre-allocated pool and enable efficient memory
// management patterns. Unlike unique/shared pointers, handles don't use
// reference counting but rely on explicit pool management.
//
// A Handle contains:
// - header: Standard heap header
// - pool_index: Index into the pool
// - value: The stored RuntimeValue
// - valid: Whether the handle is still valid (not freed)

/// Runtime representation of a handle pointer.
#[repr(C)]
pub struct RuntimeHandle {
    pub header: HeapHeader,
    pub pool_index: u32,
    pub valid: u32, // 1 = valid, 0 = freed
    pub value: RuntimeValue,
}

/// Create a new handle pointer wrapping a value.
/// Allocates from the heap (a real pool implementation would use a pool allocator).
#[no_mangle]
pub extern "C" fn rt_handle_new(value: RuntimeValue) -> RuntimeValue {
    let size = std::mem::size_of::<RuntimeHandle>();
    let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();

    unsafe {
        let ptr = std::alloc::alloc_zeroed(layout) as *mut RuntimeHandle;
        if ptr.is_null() {
            return RuntimeValue::NIL;
        }

        // Use a simple counter for pool index (in a real impl, this would be from a pool)
        static NEXT_POOL_INDEX: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(1);
        let pool_index = NEXT_POOL_INDEX.fetch_add(1, Ordering::SeqCst);

        (*ptr).header = HeapHeader::new(HeapObjectType::Unique, size as u32); // Using Unique type for handles
        (*ptr).pool_index = pool_index;
        (*ptr).valid = 1;
        (*ptr).value = value;

        RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader)
    }
}

/// Get the value inside a handle pointer.
/// Returns NIL if the handle is invalid or freed.
#[no_mangle]
pub extern "C" fn rt_handle_get(handle: RuntimeValue) -> RuntimeValue {
    let ptr = handle.as_heap_ptr();
    if ptr.is_null() {
        return RuntimeValue::NIL;
    }

    unsafe {
        let handle_ptr = ptr as *const RuntimeHandle;
        if (*handle_ptr).valid == 0 {
            return RuntimeValue::NIL;
        }
        (*handle_ptr).value
    }
}

/// Set the value inside a handle pointer.
/// Returns success as a boolean RuntimeValue.
#[no_mangle]
pub extern "C" fn rt_handle_set(handle: RuntimeValue, new_value: RuntimeValue) -> RuntimeValue {
    let ptr = handle.as_heap_ptr();
    if ptr.is_null() {
        return RuntimeValue::from_bool(false);
    }

    unsafe {
        let handle_ptr = ptr as *mut RuntimeHandle;
        if (*handle_ptr).valid == 0 {
            return RuntimeValue::from_bool(false);
        }
        (*handle_ptr).value = new_value;
        RuntimeValue::from_bool(true)
    }
}

/// Free a handle pointer.
/// Marks the handle as invalid and deallocates the memory.
#[no_mangle]
pub extern "C" fn rt_handle_free(handle: RuntimeValue) {
    let ptr = handle.as_heap_ptr();
    if ptr.is_null() {
        return;
    }

    unsafe {
        let handle_ptr = ptr as *mut RuntimeHandle;
        // Mark as invalid first
        (*handle_ptr).valid = 0;

        // Deallocate
        let size = std::mem::size_of::<RuntimeHandle>();
        let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();
        std::alloc::dealloc(ptr as *mut u8, layout);
    }
}

/// Check if a handle pointer is still valid.
#[no_mangle]
pub extern "C" fn rt_handle_is_valid(handle: RuntimeValue) -> RuntimeValue {
    let ptr = handle.as_heap_ptr();
    if ptr.is_null() {
        return RuntimeValue::from_bool(false);
    }

    unsafe {
        let handle_ptr = ptr as *const RuntimeHandle;
        RuntimeValue::from_bool((*handle_ptr).valid != 0)
    }
}

#[cfg(test)]
#[path = "object_tests.rs"]
mod tests;
