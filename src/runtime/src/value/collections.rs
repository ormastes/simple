//! Collection types: Array, Tuple, String and their FFI functions.
//! Dict FFI functions are in the dict module.

use super::core::RuntimeValue;
use super::dict::RuntimeDict;
use super::heap::{get_typed_ptr, get_typed_ptr_mut, HeapHeader, HeapObjectType};

// ============================================================================
// Helper macros to reduce FFI boilerplate
// ============================================================================

/// Get typed pointer from heap object with validation, returning early if invalid
macro_rules! as_typed_ptr {
    ($val:expr, $expected:expr, $ty:ty, $ret:expr) => {{
        match get_typed_ptr::<$ty>($val, $expected) {
            Some(ptr) => ptr,
            None => return $ret,
        }
    }};
    (mut $val:expr, $expected:expr, $ty:ty, $ret:expr) => {{
        match get_typed_ptr_mut::<$ty>($val, $expected) {
            Some(ptr) => ptr,
            None => return $ret,
        }
    }};
}

/// Normalize a Python-style index (handles negative indices)
#[inline]
fn normalize_index(index: i64, len: i64) -> i64 {
    if index < 0 {
        len + index
    } else {
        index
    }
}

/// FNV-1a hash for strings (64-bit)
/// This is a simple, fast hash suitable for hash tables.
#[inline]
fn fnv1a_hash(bytes: &[u8]) -> u64 {
    const FNV_OFFSET: u64 = 0xcbf29ce484222325;
    const FNV_PRIME: u64 = 0x100000001b3;

    let mut hash = FNV_OFFSET;
    for &byte in bytes {
        hash ^= byte as u64;
        hash = hash.wrapping_mul(FNV_PRIME);
    }
    hash
}

// ============================================================================
// Heap-allocated collection structures
// ============================================================================

/// A heap-allocated string
#[repr(C)]
pub struct RuntimeString {
    pub header: HeapHeader,
    /// Length in bytes
    pub len: u64,
    /// Cached hash value
    pub hash: u64,
    // Followed by UTF-8 bytes (flexible array member)
}

impl RuntimeString {
    /// Get the string data as a byte slice
    ///
    /// # Safety
    /// The caller must ensure the RuntimeString was properly allocated
    /// with the correct length.
    pub unsafe fn as_bytes(&self) -> &[u8] {
        let data_ptr = (self as *const Self).add(1) as *const u8;
        std::slice::from_raw_parts(data_ptr, self.len as usize)
    }

    /// Get the string data as a str
    ///
    /// # Safety
    /// The caller must ensure the RuntimeString contains valid UTF-8.
    pub unsafe fn as_str(&self) -> &str {
        std::str::from_utf8_unchecked(self.as_bytes())
    }
}

/// Allocate a RuntimeString with given length (no data copied).
/// Returns None if allocation fails.
/// # Safety
/// The caller must initialize the string data and hash.
unsafe fn alloc_runtime_string(len: u64) -> Option<*mut RuntimeString> {
    let size = std::mem::size_of::<RuntimeString>() + len as usize;
    let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();
    let ptr = std::alloc::alloc(layout) as *mut RuntimeString;
    if ptr.is_null() {
        return None;
    }
    (*ptr).header = HeapHeader::new(HeapObjectType::String, size as u32);
    (*ptr).len = len;
    Some(ptr)
}

/// A heap-allocated array
#[repr(C)]
pub struct RuntimeArray {
    pub header: HeapHeader,
    /// Number of elements
    pub len: u64,
    /// Capacity (allocated slots)
    pub capacity: u64,
    // Followed by RuntimeValue elements
}

impl RuntimeArray {
    /// Get the elements as a slice
    ///
    /// # Safety
    /// The caller must ensure the RuntimeArray was properly allocated.
    pub unsafe fn as_slice(&self) -> &[RuntimeValue] {
        let data_ptr = (self as *const Self).add(1) as *const RuntimeValue;
        std::slice::from_raw_parts(data_ptr, self.len as usize)
    }

    /// Get the elements as a mutable slice
    ///
    /// # Safety
    /// The caller must ensure the RuntimeArray was properly allocated.
    pub unsafe fn as_mut_slice(&mut self) -> &mut [RuntimeValue] {
        let data_ptr = (self as *mut Self).add(1) as *mut RuntimeValue;
        std::slice::from_raw_parts_mut(data_ptr, self.len as usize)
    }
}

/// A heap-allocated tuple (fixed-size array)
#[repr(C)]
pub struct RuntimeTuple {
    pub header: HeapHeader,
    /// Number of elements
    pub len: u64,
    // Followed by RuntimeValue elements
}

impl RuntimeTuple {
    /// Get the elements as a slice
    ///
    /// # Safety
    /// The caller must ensure the RuntimeTuple was properly allocated.
    pub unsafe fn as_slice(&self) -> &[RuntimeValue] {
        let data_ptr = (self as *const Self).add(1) as *const RuntimeValue;
        std::slice::from_raw_parts(data_ptr, self.len as usize)
    }
}

// RuntimeDict is in dict.rs module

// ============================================================================
// Array FFI functions
// ============================================================================

/// Allocate a new array with the given capacity
#[no_mangle]
pub extern "C" fn rt_array_new(capacity: u64) -> RuntimeValue {
    let size = std::mem::size_of::<RuntimeArray>() + capacity as usize * std::mem::size_of::<RuntimeValue>();
    let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();

    unsafe {
        let ptr = std::alloc::alloc_zeroed(layout) as *mut RuntimeArray;
        if ptr.is_null() {
            return RuntimeValue::NIL;
        }

        (*ptr).header = HeapHeader::new(HeapObjectType::Array, size as u32);
        (*ptr).len = 0;
        (*ptr).capacity = capacity;

        RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader)
    }
}

/// Get the length of an array
#[no_mangle]
pub extern "C" fn rt_array_len(array: RuntimeValue) -> i64 {
    let arr = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, -1);
    unsafe { (*arr).len as i64 }
}

/// Get an element from an array
#[no_mangle]
pub extern "C" fn rt_array_get(array: RuntimeValue, index: i64) -> RuntimeValue {
    let arr = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, RuntimeValue::NIL);
    unsafe {
        let len = (*arr).len as i64;
        let idx = normalize_index(index, len);
        if idx < 0 || idx >= len {
            return RuntimeValue::NIL;
        }
        (*arr).as_slice()[idx as usize]
    }
}

/// Set an element in an array
#[no_mangle]
pub extern "C" fn rt_array_set(array: RuntimeValue, index: i64, value: RuntimeValue) -> bool {
    let arr = as_typed_ptr!(mut array, HeapObjectType::Array, RuntimeArray, false);
    unsafe {
        let len = (*arr).len as i64;
        let idx = normalize_index(index, len);
        if idx < 0 || idx >= len {
            return false;
        }
        (*arr).as_mut_slice()[idx as usize] = value;
        true
    }
}

/// Push an element to an array
#[no_mangle]
pub extern "C" fn rt_array_push(array: RuntimeValue, value: RuntimeValue) -> bool {
    let arr = as_typed_ptr!(mut array, HeapObjectType::Array, RuntimeArray, false);
    unsafe {
        if (*arr).len >= (*arr).capacity {
            return false;
        }
        let data_ptr = (arr.add(1)) as *mut RuntimeValue;
        *data_ptr.add((*arr).len as usize) = value;
        (*arr).len += 1;
        true
    }
}

/// Pop an element from an array
#[no_mangle]
pub extern "C" fn rt_array_pop(array: RuntimeValue) -> RuntimeValue {
    let arr = as_typed_ptr!(mut array, HeapObjectType::Array, RuntimeArray, RuntimeValue::NIL);
    unsafe {
        if (*arr).len == 0 {
            return RuntimeValue::NIL;
        }
        (*arr).len -= 1;
        let data_ptr = (arr.add(1)) as *const RuntimeValue;
        *data_ptr.add((*arr).len as usize)
    }
}

/// Clear all elements from an array
#[no_mangle]
pub extern "C" fn rt_array_clear(array: RuntimeValue) -> bool {
    let arr = as_typed_ptr!(mut array, HeapObjectType::Array, RuntimeArray, false);
    unsafe {
        (*arr).len = 0;
        true
    }
}

/// Create an array from a slice of RuntimeValues
///
/// This is a convenience function for creating arrays with initial values.
/// The array will have capacity equal to the slice length.
pub fn rt_array_create_from_slice(values: &[RuntimeValue]) -> RuntimeValue {
    let capacity = values.len() as u64;
    let array = rt_array_new(capacity);

    if array.is_nil() {
        return RuntimeValue::NIL;
    }

    // Push all values into the array
    for value in values {
        if !rt_array_push(array, *value) {
            return RuntimeValue::NIL;
        }
    }

    array
}

// ============================================================================
// Tuple FFI functions
// ============================================================================

/// Allocate a new tuple with the given length
#[no_mangle]
pub extern "C" fn rt_tuple_new(len: u64) -> RuntimeValue {
    let size = std::mem::size_of::<RuntimeTuple>() + len as usize * std::mem::size_of::<RuntimeValue>();
    let layout = std::alloc::Layout::from_size_align(size, 8).unwrap();

    unsafe {
        let ptr = std::alloc::alloc_zeroed(layout) as *mut RuntimeTuple;
        if ptr.is_null() {
            return RuntimeValue::NIL;
        }

        (*ptr).header = HeapHeader::new(HeapObjectType::Tuple, size as u32);
        (*ptr).len = len;

        RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader)
    }
}

/// Get an element from a tuple
#[no_mangle]
pub extern "C" fn rt_tuple_get(tuple: RuntimeValue, index: u64) -> RuntimeValue {
    let tup = as_typed_ptr!(tuple, HeapObjectType::Tuple, RuntimeTuple, RuntimeValue::NIL);
    unsafe {
        if index >= (*tup).len {
            return RuntimeValue::NIL;
        }
        (*tup).as_slice()[index as usize]
    }
}

/// Set an element in a tuple (used during construction)
#[no_mangle]
pub extern "C" fn rt_tuple_set(tuple: RuntimeValue, index: u64, value: RuntimeValue) -> bool {
    let tup = as_typed_ptr!(mut tuple, HeapObjectType::Tuple, RuntimeTuple, false);
    unsafe {
        if index >= (*tup).len {
            return false;
        }
        let data_ptr = (tup.add(1)) as *mut RuntimeValue;
        *data_ptr.add(index as usize) = value;
        true
    }
}

/// Get the length of a tuple
#[no_mangle]
pub extern "C" fn rt_tuple_len(tuple: RuntimeValue) -> i64 {
    let tup = as_typed_ptr!(tuple, HeapObjectType::Tuple, RuntimeTuple, -1);
    unsafe { (*tup).len as i64 }
}

// ============================================================================
// String FFI functions
// ============================================================================

/// Create a string from UTF-8 bytes
///
/// # Safety
/// The bytes must be valid UTF-8.
#[no_mangle]
pub extern "C" fn rt_string_new(bytes: *const u8, len: u64) -> RuntimeValue {
    if bytes.is_null() && len > 0 {
        return RuntimeValue::NIL;
    }

    unsafe {
        let Some(ptr) = alloc_runtime_string(len) else {
            return RuntimeValue::NIL;
        };

        // Copy string data and compute hash
        if len > 0 {
            let data_ptr = ptr.add(1) as *mut u8;
            std::ptr::copy_nonoverlapping(bytes, data_ptr, len as usize);
            (*ptr).hash = fnv1a_hash(std::slice::from_raw_parts(bytes, len as usize));
        } else {
            (*ptr).hash = 0;
        }

        RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader)
    }
}

/// Get the length of a string in bytes
#[no_mangle]
pub extern "C" fn rt_string_len(string: RuntimeValue) -> i64 {
    let str_ptr = as_typed_ptr!(string, HeapObjectType::String, RuntimeString, -1);
    unsafe { (*str_ptr).len as i64 }
}

/// Get a pointer to the string data
#[no_mangle]
pub extern "C" fn rt_string_data(string: RuntimeValue) -> *const u8 {
    let str_ptr = as_typed_ptr!(string, HeapObjectType::String, RuntimeString, std::ptr::null());
    unsafe { str_ptr.add(1) as *const u8 }
}

/// Concatenate two strings
#[no_mangle]
pub extern "C" fn rt_string_concat(a: RuntimeValue, b: RuntimeValue) -> RuntimeValue {
    let len_a = rt_string_len(a);
    let len_b = rt_string_len(b);

    if len_a < 0 || len_b < 0 {
        return RuntimeValue::NIL;
    }

    let total_len = len_a as u64 + len_b as u64;

    unsafe {
        let Some(ptr) = alloc_runtime_string(total_len) else {
            return RuntimeValue::NIL;
        };

        // Copy first string
        let data_ptr = ptr.add(1) as *mut u8;
        let data_a = rt_string_data(a);
        if !data_a.is_null() && len_a > 0 {
            std::ptr::copy_nonoverlapping(data_a, data_ptr, len_a as usize);
        }

        // Copy second string
        let data_b = rt_string_data(b);
        if !data_b.is_null() && len_b > 0 {
            std::ptr::copy_nonoverlapping(data_b, data_ptr.add(len_a as usize), len_b as usize);
        }

        // Compute hash for concatenated string
        (*ptr).hash = if total_len > 0 {
            fnv1a_hash(std::slice::from_raw_parts(data_ptr, total_len as usize))
        } else {
            0
        };

        RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader)
    }
}

// Dict FFI functions are in dict.rs module

// ============================================================================
// Generic collection operations
// ============================================================================

/// Index into a collection (array, tuple, string, dict)
/// Returns NIL if out of bounds or wrong type
#[no_mangle]
pub extern "C" fn rt_index_get(collection: RuntimeValue, index: RuntimeValue) -> RuntimeValue {
    if !collection.is_heap() {
        return RuntimeValue::NIL;
    }

    let ptr = collection.as_heap_ptr();
    unsafe {
        match (*ptr).object_type {
            HeapObjectType::Array => {
                if index.is_int() {
                    rt_array_get(collection, index.as_int())
                } else {
                    RuntimeValue::NIL
                }
            }
            HeapObjectType::Tuple => {
                if index.is_int() {
                    let idx = index.as_int();
                    if idx < 0 {
                        RuntimeValue::NIL
                    } else {
                        rt_tuple_get(collection, idx as u64)
                    }
                } else {
                    RuntimeValue::NIL
                }
            }
            HeapObjectType::String => {
                // String indexing returns character code
                if index.is_int() {
                    let str_ptr = ptr as *const RuntimeString;
                    let len = (*str_ptr).len as i64;
                    let idx = index.as_int();
                    let idx = if idx < 0 { len + idx } else { idx };
                    if idx < 0 || idx >= len {
                        RuntimeValue::NIL
                    } else {
                        let data = str_ptr.add(1) as *const u8;
                        RuntimeValue::from_int(*data.add(idx as usize) as i64)
                    }
                } else {
                    RuntimeValue::NIL
                }
            }
            // Dict indexing would go here
            _ => RuntimeValue::NIL,
        }
    }
}

/// Set a value in a collection (array, dict)
/// Returns true on success, false on error
#[no_mangle]
pub extern "C" fn rt_index_set(collection: RuntimeValue, index: RuntimeValue, value: RuntimeValue) -> bool {
    if !collection.is_heap() {
        return false;
    }

    let ptr = collection.as_heap_ptr();
    unsafe {
        match (*ptr).object_type {
            HeapObjectType::Array => {
                if index.is_int() {
                    rt_array_set(collection, index.as_int(), value)
                } else {
                    false
                }
            }
            // Dict indexing would go here
            _ => false,
        }
    }
}

/// Slice a collection (array, tuple, string)
/// Returns a new collection with elements from start to end (exclusive)
#[no_mangle]
pub extern "C" fn rt_slice(collection: RuntimeValue, start: i64, end: i64, step: i64) -> RuntimeValue {
    if !collection.is_heap() || step == 0 {
        return RuntimeValue::NIL;
    }

    let ptr = collection.as_heap_ptr();
    unsafe {
        match (*ptr).object_type {
            HeapObjectType::Array => {
                let arr = ptr as *const RuntimeArray;
                let len = (*arr).len as i64;

                // Normalize start and end
                let start = if start < 0 {
                    (len + start).max(0)
                } else {
                    start.min(len)
                };
                let end = if end < 0 { (len + end).max(0) } else { end.min(len) };

                if step > 0 && start >= end {
                    return rt_array_new(0);
                }
                if step < 0 && start <= end {
                    return rt_array_new(0);
                }

                // Calculate result length
                let result_len = if step > 0 {
                    ((end - start + step - 1) / step) as u64
                } else {
                    ((start - end - step - 1) / (-step)) as u64
                };

                let result = rt_array_new(result_len);
                if result.is_nil() {
                    return result;
                }

                let src_slice = (*arr).as_slice();
                let mut idx = start;
                while (step > 0 && idx < end) || (step < 0 && idx > end) {
                    rt_array_push(result, src_slice[idx as usize]);
                    idx += step;
                }

                result
            }
            HeapObjectType::String => {
                let str_ptr = ptr as *const RuntimeString;
                let len = (*str_ptr).len as i64;
                let start = normalize_index(start, len).max(0).min(len);
                let end = normalize_index(end, len).max(0).min(len);

                if step != 1 || start >= end {
                    return rt_string_new(std::ptr::null(), 0);
                }

                let data = str_ptr.add(1) as *const u8;
                rt_string_new(data.add(start as usize), (end - start) as u64)
            }
            _ => RuntimeValue::NIL,
        }
    }
}

/// Check if a value is contained in a collection (array, dict, string)
/// Returns true (1) if found, false (0) if not
#[no_mangle]
pub extern "C" fn rt_contains(collection: RuntimeValue, value: RuntimeValue) -> u8 {
    use super::ffi::rt_value_eq;

    if !collection.is_heap() {
        return 0;
    }

    let ptr = collection.as_heap_ptr();
    unsafe {
        match (*ptr).object_type {
            HeapObjectType::Array => {
                let arr = ptr as *const RuntimeArray;
                let slice = (*arr).as_slice();
                for item in slice {
                    if rt_value_eq(*item, value) != 0 {
                        return 1;
                    }
                }
                0
            }
            HeapObjectType::Dict => {
                // For dicts, 'in' checks if the key exists
                let dict = ptr as *const RuntimeDict;
                // Entries are stored after the RuntimeDict header as pairs of RuntimeValue
                let entries_ptr = (dict as *const u8).add(std::mem::size_of::<RuntimeDict>()) as *const RuntimeValue;
                for i in 0..(*dict).len as usize {
                    let key = *entries_ptr.add(i * 2);
                    if rt_value_eq(key, value) != 0 {
                        return 1;
                    }
                }
                0
            }
            HeapObjectType::String => {
                // For strings, check if value (as string) is a substring
                // Simplified: only check if value is a single character in the string
                if value.is_int() {
                    let char_code = value.as_int();
                    let str_ptr = ptr as *const RuntimeString;
                    let data = (str_ptr.add(1)) as *const u8;
                    for i in 0..(*str_ptr).len {
                        if *data.add(i as usize) as i64 == char_code {
                            return 1;
                        }
                    }
                }
                0
            }
            _ => 0,
        }
    }
}

#[cfg(test)]
#[path = "collection_tests.rs"]
mod tests;
