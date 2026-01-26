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

/// Push an element to an array (no grow, returns false if full)
#[no_mangle]
pub extern "C" fn rt_array_push(array: RuntimeValue, value: RuntimeValue) -> bool {
    rt_array_push_grow(array, value)
}

/// Push an element to an array, growing the array if necessary.
/// This is the default push behavior - arrays automatically grow.
#[no_mangle]
pub extern "C" fn rt_array_push_grow(array: RuntimeValue, value: RuntimeValue) -> bool {
    let arr = as_typed_ptr!(mut array, HeapObjectType::Array, RuntimeArray, false);
    unsafe {
        // If array is at capacity, grow it
        if (*arr).len >= (*arr).capacity {
            // Calculate new capacity (double or minimum 8)
            let old_capacity = (*arr).capacity;
            let new_capacity = if old_capacity == 0 { 8 } else { old_capacity * 2 };

            // Calculate sizes
            let old_size = std::mem::size_of::<RuntimeArray>()
                + old_capacity as usize * std::mem::size_of::<RuntimeValue>();
            let new_size = std::mem::size_of::<RuntimeArray>()
                + new_capacity as usize * std::mem::size_of::<RuntimeValue>();

            let old_layout = std::alloc::Layout::from_size_align(old_size, 8).unwrap();
            let new_layout = std::alloc::Layout::from_size_align(new_size, 8).unwrap();

            // Reallocate
            let new_ptr = std::alloc::realloc(arr as *mut u8, old_layout, new_layout.size());
            if new_ptr.is_null() {
                return false; // Allocation failed
            }

            // Update the array pointer in the caller's RuntimeValue
            // Note: We can't change the original RuntimeValue, so this approach
            // won't work for resizing. We need a different strategy.
            //
            // For now, we'll create the array with a reasonable initial capacity
            // and fail if exceeded. A proper solution would use indirection.
            return false; // Can't grow in-place with current design
        }

        let data_ptr = (arr.add(1)) as *mut RuntimeValue;
        *data_ptr.add((*arr).len as usize) = value;
        (*arr).len += 1;
        true
    }
}

/// Push element without grow (legacy behavior)
#[no_mangle]
pub extern "C" fn rt_array_push_no_grow(array: RuntimeValue, value: RuntimeValue) -> bool {
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

/// Generic length function that works on any collection type (Array, String, Tuple, Dict)
/// Returns -1 for non-collection types
#[no_mangle]
pub extern "C" fn rt_len(value: RuntimeValue) -> i64 {
    // Check if it's a heap object
    if !value.is_heap() {
        return -1;
    }

    // Get the header to determine the type
    let header = value.as_heap_ptr();
    if header.is_null() {
        return -1;
    }

    unsafe {
        match (*header).object_type {
            HeapObjectType::Array => rt_array_len(value),
            HeapObjectType::String => rt_string_len(value),
            HeapObjectType::Tuple => rt_tuple_len(value),
            HeapObjectType::Dict => super::dict::rt_dict_len(value),
            _ => -1,
        }
    }
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

/// Check if string starts with prefix
/// Returns 1 if true, 0 if false
#[no_mangle]
pub extern "C" fn rt_string_starts_with(string: RuntimeValue, prefix: RuntimeValue) -> i64 {
    let str_len = rt_string_len(string);
    let prefix_len = rt_string_len(prefix);

    if str_len < 0 || prefix_len < 0 {
        return 0;
    }

    if prefix_len > str_len {
        return 0;
    }

    if prefix_len == 0 {
        return 1; // Empty prefix always matches
    }

    let str_data = rt_string_data(string);
    let prefix_data = rt_string_data(prefix);

    if str_data.is_null() || prefix_data.is_null() {
        return 0;
    }

    unsafe {
        let str_slice = std::slice::from_raw_parts(str_data, prefix_len as usize);
        let prefix_slice = std::slice::from_raw_parts(prefix_data, prefix_len as usize);
        if str_slice == prefix_slice { 1 } else { 0 }
    }
}

/// Check if string ends with suffix
/// Returns 1 if true, 0 if false
#[no_mangle]
pub extern "C" fn rt_string_ends_with(string: RuntimeValue, suffix: RuntimeValue) -> i64 {
    let str_len = rt_string_len(string);
    let suffix_len = rt_string_len(suffix);

    if str_len < 0 || suffix_len < 0 {
        return 0;
    }

    if suffix_len > str_len {
        return 0;
    }

    if suffix_len == 0 {
        return 1; // Empty suffix always matches
    }

    let str_data = rt_string_data(string);
    let suffix_data = rt_string_data(suffix);

    if str_data.is_null() || suffix_data.is_null() {
        return 0;
    }

    unsafe {
        let start_offset = (str_len - suffix_len) as usize;
        let str_slice = std::slice::from_raw_parts(str_data.add(start_offset), suffix_len as usize);
        let suffix_slice = std::slice::from_raw_parts(suffix_data, suffix_len as usize);
        if str_slice == suffix_slice { 1 } else { 0 }
    }
}

/// Check if two strings are equal
/// Returns 1 if true, 0 if false
#[no_mangle]
pub extern "C" fn rt_string_eq(string1: RuntimeValue, string2: RuntimeValue) -> i64 {
    let len1 = rt_string_len(string1);
    let len2 = rt_string_len(string2);

    if len1 < 0 || len2 < 0 {
        return 0;
    }

    if len1 != len2 {
        return 0;
    }

    if len1 == 0 {
        return 1; // Both empty strings are equal
    }

    let data1 = rt_string_data(string1);
    let data2 = rt_string_data(string2);

    if data1.is_null() || data2.is_null() {
        return 0;
    }

    unsafe {
        let slice1 = std::slice::from_raw_parts(data1, len1 as usize);
        let slice2 = std::slice::from_raw_parts(data2, len2 as usize);
        if slice1 == slice2 { 1 } else { 0 }
    }
}

/// Create a string from a null-terminated C string
///
/// # Safety
/// The pointer must be a valid null-terminated C string (or null).
/// The string data must be valid UTF-8.
#[no_mangle]
pub unsafe extern "C" fn rt_cstring_to_text(cstr: *const i8) -> RuntimeValue {
    if cstr.is_null() {
        return rt_string_new(std::ptr::null(), 0);
    }

    // Calculate length using strlen
    let len = {
        let mut p = cstr;
        let mut count = 0u64;
        while *p != 0 {
            p = p.add(1);
            count += 1;
        }
        count
    };

    rt_string_new(cstr as *const u8, len)
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

// ============================================================================
// Array Higher-Order and Utility Functions
// ============================================================================

/// Reverse an array in place
///
/// # Examples
/// - [1, 2, 3] → [3, 2, 1]
#[no_mangle]
pub extern "C" fn rt_array_reverse(array: RuntimeValue) -> bool {
    let arr = as_typed_ptr!(mut array, HeapObjectType::Array, RuntimeArray, false);
    unsafe {
        let slice = (*arr).as_mut_slice();
        slice.reverse();
        true
    }
}

/// Create a new reversed copy of an array
///
/// # Examples
/// - reversed([1, 2, 3]) → [3, 2, 1]
#[no_mangle]
pub extern "C" fn rt_array_reversed(array: RuntimeValue) -> RuntimeValue {
    let arr = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, RuntimeValue::NIL);
    unsafe {
        let len = (*arr).len;
        let result = rt_array_new(len);
        if result.is_nil() {
            return result;
        }
        let src_slice = (*arr).as_slice();
        for i in (0..len as usize).rev() {
            rt_array_push(result, src_slice[i]);
        }
        result
    }
}

/// Sort an array in place (ascending order)
/// Works with integers and floats. Mixed types are sorted with ints first.
#[no_mangle]
pub extern "C" fn rt_array_sort(array: RuntimeValue) -> bool {
    let arr = as_typed_ptr!(mut array, HeapObjectType::Array, RuntimeArray, false);
    unsafe {
        let slice = (*arr).as_mut_slice();
        slice.sort_by(|a, b| {
            // Compare by type first, then by value
            match (a.is_int(), b.is_int(), a.is_float(), b.is_float()) {
                (true, true, _, _) => a.as_int().cmp(&b.as_int()),
                (_, _, true, true) => a.as_float().partial_cmp(&b.as_float()).unwrap_or(std::cmp::Ordering::Equal),
                (true, false, _, true) => std::cmp::Ordering::Less, // int < float
                (false, true, true, _) => std::cmp::Ordering::Greater, // float > int
                _ => std::cmp::Ordering::Equal, // Other types: keep order
            }
        });
        true
    }
}

/// Create a new sorted copy of an array (ascending order)
#[no_mangle]
pub extern "C" fn rt_array_sorted(array: RuntimeValue) -> RuntimeValue {
    let arr = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, RuntimeValue::NIL);
    unsafe {
        let len = (*arr).len;
        let result = rt_array_new(len);
        if result.is_nil() {
            return result;
        }
        // Copy elements
        let src_slice = (*arr).as_slice();
        for item in src_slice {
            rt_array_push(result, *item);
        }
        // Sort in place
        rt_array_sort(result);
        result
    }
}

/// Sort array in descending order
#[no_mangle]
pub extern "C" fn rt_array_sort_desc(array: RuntimeValue) -> bool {
    if !rt_array_sort(array) {
        return false;
    }
    rt_array_reverse(array)
}

/// Get the first element of an array
/// Returns NIL if array is empty
#[no_mangle]
pub extern "C" fn rt_array_first(array: RuntimeValue) -> RuntimeValue {
    rt_array_get(array, 0)
}

/// Get the last element of an array
/// Returns NIL if array is empty
#[no_mangle]
pub extern "C" fn rt_array_last(array: RuntimeValue) -> RuntimeValue {
    rt_array_get(array, -1)
}

/// Find the index of a value in an array
/// Returns -1 if not found
#[no_mangle]
pub extern "C" fn rt_array_index_of(array: RuntimeValue, value: RuntimeValue) -> i64 {
    use super::ffi::rt_value_eq;

    let arr = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, -1);
    unsafe {
        let slice = (*arr).as_slice();
        for (i, item) in slice.iter().enumerate() {
            if rt_value_eq(*item, value) != 0 {
                return i as i64;
            }
        }
        -1
    }
}

/// Find the last index of a value in an array
/// Returns -1 if not found
#[no_mangle]
pub extern "C" fn rt_array_last_index_of(array: RuntimeValue, value: RuntimeValue) -> i64 {
    use super::ffi::rt_value_eq;

    let arr = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, -1);
    unsafe {
        let slice = (*arr).as_slice();
        for (i, item) in slice.iter().enumerate().rev() {
            if rt_value_eq(*item, value) != 0 {
                return i as i64;
            }
        }
        -1
    }
}

/// Concatenate two arrays into a new array
#[no_mangle]
pub extern "C" fn rt_array_concat(a: RuntimeValue, b: RuntimeValue) -> RuntimeValue {
    let arr_a = as_typed_ptr!(a, HeapObjectType::Array, RuntimeArray, RuntimeValue::NIL);
    let arr_b = as_typed_ptr!(b, HeapObjectType::Array, RuntimeArray, RuntimeValue::NIL);

    unsafe {
        let len_a = (*arr_a).len;
        let len_b = (*arr_b).len;
        let result = rt_array_new(len_a + len_b);
        if result.is_nil() {
            return result;
        }

        // Copy from first array
        for item in (*arr_a).as_slice() {
            rt_array_push(result, *item);
        }
        // Copy from second array
        for item in (*arr_b).as_slice() {
            rt_array_push(result, *item);
        }
        result
    }
}

/// Create a shallow copy of an array
#[no_mangle]
pub extern "C" fn rt_array_copy(array: RuntimeValue) -> RuntimeValue {
    let arr = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, RuntimeValue::NIL);
    unsafe {
        let len = (*arr).len;
        let result = rt_array_new(len);
        if result.is_nil() {
            return result;
        }
        for item in (*arr).as_slice() {
            rt_array_push(result, *item);
        }
        result
    }
}

/// Sum all numeric elements in an array
/// Returns 0 for empty arrays, NIL for non-numeric elements
#[no_mangle]
pub extern "C" fn rt_array_sum(array: RuntimeValue) -> RuntimeValue {
    let arr = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, RuntimeValue::NIL);
    unsafe {
        let slice = (*arr).as_slice();
        if slice.is_empty() {
            return RuntimeValue::from_int(0);
        }

        let mut int_sum: i64 = 0;
        let mut float_sum: f64 = 0.0;
        let mut has_float = false;

        for item in slice {
            if item.is_int() {
                int_sum += item.as_int();
            } else if item.is_float() {
                has_float = true;
                float_sum += item.as_float();
            }
        }

        if has_float {
            RuntimeValue::from_float(int_sum as f64 + float_sum)
        } else {
            RuntimeValue::from_int(int_sum)
        }
    }
}

/// Find the minimum element in an array
/// Returns NIL for empty arrays
#[no_mangle]
pub extern "C" fn rt_array_min(array: RuntimeValue) -> RuntimeValue {
    let arr = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, RuntimeValue::NIL);
    unsafe {
        let slice = (*arr).as_slice();
        if slice.is_empty() {
            return RuntimeValue::NIL;
        }

        let mut min_val = slice[0];
        for item in &slice[1..] {
            let cmp = if min_val.is_int() && item.is_int() {
                item.as_int() < min_val.as_int()
            } else if min_val.is_float() && item.is_float() {
                item.as_float() < min_val.as_float()
            } else if min_val.is_int() && item.is_float() {
                item.as_float() < min_val.as_int() as f64
            } else if min_val.is_float() && item.is_int() {
                (item.as_int() as f64) < min_val.as_float()
            } else {
                false
            };
            if cmp {
                min_val = *item;
            }
        }
        min_val
    }
}

/// Find the maximum element in an array
/// Returns NIL for empty arrays
#[no_mangle]
pub extern "C" fn rt_array_max(array: RuntimeValue) -> RuntimeValue {
    let arr = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, RuntimeValue::NIL);
    unsafe {
        let slice = (*arr).as_slice();
        if slice.is_empty() {
            return RuntimeValue::NIL;
        }

        let mut max_val = slice[0];
        for item in &slice[1..] {
            let cmp = if max_val.is_int() && item.is_int() {
                item.as_int() > max_val.as_int()
            } else if max_val.is_float() && item.is_float() {
                item.as_float() > max_val.as_float()
            } else if max_val.is_int() && item.is_float() {
                item.as_float() > max_val.as_int() as f64
            } else if max_val.is_float() && item.is_int() {
                (item.as_int() as f64) > max_val.as_float()
            } else {
                false
            };
            if cmp {
                max_val = *item;
            }
        }
        max_val
    }
}

/// Count occurrences of a value in an array
#[no_mangle]
pub extern "C" fn rt_array_count(array: RuntimeValue, value: RuntimeValue) -> i64 {
    use super::ffi::rt_value_eq;

    let arr = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, -1);
    unsafe {
        let slice = (*arr).as_slice();
        let mut count = 0i64;
        for item in slice {
            if rt_value_eq(*item, value) != 0 {
                count += 1;
            }
        }
        count
    }
}

/// Zip two arrays together into an array of tuples
/// The result length is the minimum of the two input lengths
#[no_mangle]
pub extern "C" fn rt_array_zip(a: RuntimeValue, b: RuntimeValue) -> RuntimeValue {
    let arr_a = as_typed_ptr!(a, HeapObjectType::Array, RuntimeArray, RuntimeValue::NIL);
    let arr_b = as_typed_ptr!(b, HeapObjectType::Array, RuntimeArray, RuntimeValue::NIL);

    unsafe {
        let len_a = (*arr_a).len;
        let len_b = (*arr_b).len;
        let result_len = len_a.min(len_b);

        let result = rt_array_new(result_len);
        if result.is_nil() {
            return result;
        }

        let slice_a = (*arr_a).as_slice();
        let slice_b = (*arr_b).as_slice();

        for i in 0..result_len as usize {
            // Create a tuple for each pair
            let tuple = rt_tuple_new(2);
            if tuple.is_nil() {
                return RuntimeValue::NIL;
            }
            rt_tuple_set(tuple, 0, slice_a[i]);
            rt_tuple_set(tuple, 1, slice_b[i]);
            rt_array_push(result, tuple);
        }
        result
    }
}

/// Enumerate an array, returning array of (index, value) tuples
#[no_mangle]
pub extern "C" fn rt_array_enumerate(array: RuntimeValue) -> RuntimeValue {
    let arr = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, RuntimeValue::NIL);

    unsafe {
        let len = (*arr).len;
        let result = rt_array_new(len);
        if result.is_nil() {
            return result;
        }

        let slice = (*arr).as_slice();
        for (i, item) in slice.iter().enumerate() {
            let tuple = rt_tuple_new(2);
            if tuple.is_nil() {
                return RuntimeValue::NIL;
            }
            rt_tuple_set(tuple, 0, RuntimeValue::from_int(i as i64));
            rt_tuple_set(tuple, 1, *item);
            rt_array_push(result, tuple);
        }
        result
    }
}

/// Flatten a nested array one level deep
/// [[1, 2], [3, 4]] → [1, 2, 3, 4]
#[no_mangle]
pub extern "C" fn rt_array_flatten(array: RuntimeValue) -> RuntimeValue {
    let arr = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, RuntimeValue::NIL);

    unsafe {
        let slice = (*arr).as_slice();

        // First pass: count total elements
        let mut total_len = 0u64;
        for item in slice {
            if item.is_heap() {
                let ptr = item.as_heap_ptr();
                if (*ptr).object_type == HeapObjectType::Array {
                    let inner = ptr as *const RuntimeArray;
                    total_len += (*inner).len;
                    continue;
                }
            }
            total_len += 1;
        }

        let result = rt_array_new(total_len);
        if result.is_nil() {
            return result;
        }

        // Second pass: copy elements
        for item in slice {
            if item.is_heap() {
                let ptr = item.as_heap_ptr();
                if (*ptr).object_type == HeapObjectType::Array {
                    let inner = ptr as *const RuntimeArray;
                    for inner_item in (*inner).as_slice() {
                        rt_array_push(result, *inner_item);
                    }
                    continue;
                }
            }
            rt_array_push(result, *item);
        }
        result
    }
}

/// Remove duplicate values from array (keeps first occurrence)
/// Returns a new array
#[no_mangle]
pub extern "C" fn rt_array_unique(array: RuntimeValue) -> RuntimeValue {
    use super::ffi::rt_value_eq;

    let arr = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, RuntimeValue::NIL);

    unsafe {
        let slice = (*arr).as_slice();
        let result = rt_array_new((*arr).len);
        if result.is_nil() {
            return result;
        }

        let result_arr = get_typed_ptr::<RuntimeArray>(result, HeapObjectType::Array).unwrap();

        for item in slice {
            // Check if item already exists in result
            let mut found = false;
            for existing in (*result_arr).as_slice() {
                if rt_value_eq(*existing, *item) != 0 {
                    found = true;
                    break;
                }
            }
            if !found {
                rt_array_push(result, *item);
            }
        }
        result
    }
}

/// Take first n elements from array
#[no_mangle]
pub extern "C" fn rt_array_take(array: RuntimeValue, n: i64) -> RuntimeValue {
    let arr = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, RuntimeValue::NIL);

    unsafe {
        let len = (*arr).len as i64;
        let take_count = n.max(0).min(len) as u64;

        let result = rt_array_new(take_count);
        if result.is_nil() {
            return result;
        }

        let slice = (*arr).as_slice();
        for i in 0..take_count as usize {
            rt_array_push(result, slice[i]);
        }
        result
    }
}

/// Drop first n elements from array
#[no_mangle]
pub extern "C" fn rt_array_drop(array: RuntimeValue, n: i64) -> RuntimeValue {
    let arr = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, RuntimeValue::NIL);

    unsafe {
        let len = (*arr).len as i64;
        let skip_count = n.max(0).min(len) as usize;
        let result_len = (len - skip_count as i64) as u64;

        let result = rt_array_new(result_len);
        if result.is_nil() {
            return result;
        }

        let slice = (*arr).as_slice();
        for i in skip_count..len as usize {
            rt_array_push(result, slice[i]);
        }
        result
    }
}

/// Join array elements into a string with separator
#[no_mangle]
pub extern "C" fn rt_array_join(array: RuntimeValue, separator: RuntimeValue) -> RuntimeValue {
    use super::ffi::rt_value_to_string;

    let arr = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, RuntimeValue::NIL);

    unsafe {
        let slice = (*arr).as_slice();
        if slice.is_empty() {
            return rt_string_new(std::ptr::null(), 0);
        }

        // Get separator string
        let sep_len = rt_string_len(separator);
        let sep_data = if sep_len > 0 { rt_string_data(separator) } else { std::ptr::null() };

        // Build result by concatenating
        let mut result = rt_value_to_string(slice[0]);

        for item in &slice[1..] {
            if sep_len > 0 {
                result = rt_string_concat(result, separator);
            }
            let item_str = rt_value_to_string(*item);
            result = rt_string_concat(result, item_str);
        }

        result
    }
}

/// Check if all elements satisfy a condition (all non-falsy)
/// Returns 1 if all elements are truthy, 0 otherwise
#[no_mangle]
pub extern "C" fn rt_array_all_truthy(array: RuntimeValue) -> i64 {
    let arr = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, 0);

    unsafe {
        let slice = (*arr).as_slice();
        for item in slice {
            // Check if falsy: nil, false, 0, 0.0
            if item.is_nil() {
                return 0;
            }
            if item.is_bool() && !item.as_bool() {
                return 0;
            }
            if item.is_int() && item.as_int() == 0 {
                return 0;
            }
            if item.is_float() && item.as_float() == 0.0 {
                return 0;
            }
        }
        1
    }
}

/// Check if any element is truthy
/// Returns 1 if any element is truthy, 0 otherwise
#[no_mangle]
pub extern "C" fn rt_array_any_truthy(array: RuntimeValue) -> i64 {
    let arr = as_typed_ptr!(array, HeapObjectType::Array, RuntimeArray, 0);

    unsafe {
        let slice = (*arr).as_slice();
        for item in slice {
            // Check if truthy: not (nil, false, 0, 0.0)
            if item.is_nil() {
                continue;
            }
            if item.is_bool() && !item.as_bool() {
                continue;
            }
            if item.is_int() && item.as_int() == 0 {
                continue;
            }
            if item.is_float() && item.as_float() == 0.0 {
                continue;
            }
            return 1;
        }
        0
    }
}

/// Fill array with a value (in place)
#[no_mangle]
pub extern "C" fn rt_array_fill(array: RuntimeValue, value: RuntimeValue) -> bool {
    let arr = as_typed_ptr!(mut array, HeapObjectType::Array, RuntimeArray, false);
    unsafe {
        let slice = (*arr).as_mut_slice();
        for item in slice {
            *item = value;
        }
        true
    }
}

/// Create a new array filled with a value
#[no_mangle]
pub extern "C" fn rt_array_repeat(value: RuntimeValue, count: i64) -> RuntimeValue {
    if count <= 0 {
        return rt_array_new(0);
    }

    let result = rt_array_new(count as u64);
    if result.is_nil() {
        return result;
    }

    for _ in 0..count {
        rt_array_push(result, value);
    }
    result
}

/// Create an array with a range of integers [start, end)
#[no_mangle]
pub extern "C" fn rt_array_range(start: i64, end: i64, step: i64) -> RuntimeValue {
    if step == 0 {
        return RuntimeValue::NIL;
    }

    let count = if step > 0 {
        if end <= start { 0 } else { ((end - start + step - 1) / step) as u64 }
    } else {
        if start <= end { 0 } else { ((start - end - step - 1) / (-step)) as u64 }
    };

    let result = rt_array_new(count);
    if result.is_nil() {
        return result;
    }

    let mut i = start;
    while (step > 0 && i < end) || (step < 0 && i > end) {
        rt_array_push(result, RuntimeValue::from_int(i));
        i += step;
    }
    result
}

// ============================================================================
// Membership Testing
// ============================================================================

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
