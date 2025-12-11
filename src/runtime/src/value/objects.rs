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
    let size = std::mem::size_of::<RuntimeObject>()
        + field_count as usize * std::mem::size_of::<RuntimeValue>();
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
pub extern "C" fn rt_object_field_set(
    object: RuntimeValue,
    field_index: u32,
    value: RuntimeValue,
) -> bool {
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
    get_typed_ptr::<RuntimeObject>(object, HeapObjectType::Object)
        .map_or(-1, |p| unsafe { (*p).class_id as i64 })
}

/// Get the field count of an object
#[no_mangle]
pub extern "C" fn rt_object_field_count(object: RuntimeValue) -> i64 {
    get_typed_ptr::<RuntimeObject>(object, HeapObjectType::Object)
        .map_or(-1, |p| unsafe { (*p).field_count as i64 })
}

// ============================================================================
// Closure FFI functions
// ============================================================================

/// Allocate a new closure with the given function pointer and captures
#[no_mangle]
pub extern "C" fn rt_closure_new(func_ptr: *const u8, capture_count: u32) -> RuntimeValue {
    let size = std::mem::size_of::<RuntimeClosure>()
        + capture_count as usize * std::mem::size_of::<RuntimeValue>();
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
pub extern "C" fn rt_closure_set_capture(
    closure: RuntimeValue,
    index: u32,
    value: RuntimeValue,
) -> bool {
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

/// Allocate a new enum value
#[no_mangle]
pub extern "C" fn rt_enum_new(
    enum_id: u32,
    discriminant: u32,
    payload: RuntimeValue,
) -> RuntimeValue {
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
    get_typed_ptr::<RuntimeEnum>(value, HeapObjectType::Enum)
        .map_or(-1, |p| unsafe { (*p).discriminant as i64 })
}

/// Get the payload of an enum value
#[no_mangle]
pub extern "C" fn rt_enum_payload(value: RuntimeValue) -> RuntimeValue {
    get_typed_ptr::<RuntimeEnum>(value, HeapObjectType::Enum)
        .map_or(RuntimeValue::NIL, |p| unsafe { (*p).payload })
}
