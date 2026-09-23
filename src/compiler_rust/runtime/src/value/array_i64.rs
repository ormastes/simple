//! Checked integer-array bridge for the C GPU adapters in the Rust runtime.
//! Matches runtime_native.c: boxed-element arrays of inline signed integers;
//! packed bytes, packed u64s, tuples, and noninteger elements are rejected.

use super::collections::RuntimeArray;
use super::core::RuntimeValue;
use super::heap::{get_typed_ptr, HeapObjectType};

fn checked_length(array: &RuntimeArray) -> Option<usize> {
    if array.len > array.capacity
        || array.len > (isize::MAX as usize / std::mem::size_of::<RuntimeValue>()) as u64
        || array.is_byte_packed()
        || array.is_u64_packed()
        || (array.len > 0 && array.data.is_null())
    {
        return None;
    }
    if !unsafe { array.as_slice() }.iter().all(|item| item.is_int()) {
        return None;
    }
    Some(array.len as usize)
}

/// Return the integer-array length, or -22 for an invalid representation.
/// Validation allocates nothing. As with the other array accessors, the caller
/// must keep the source alive and exclude concurrent mutation throughout.
#[no_mangle]
pub extern "C" fn rt_array_i64_validate(raw: i64) -> i64 {
    let Some(ptr) = get_typed_ptr::<RuntimeArray>(RuntimeValue(raw as u64), HeapObjectType::Array) else {
        return -22;
    };
    checked_length(unsafe { &*ptr }).map_or(-22, |length| length as i64)
}

/// Copy untagged integers without truncation or partial writes on rejection.
///
/// # Safety
/// For a nonempty accepted array, `out` must address at least `capacity` writable
/// i64 slots disjoint from the source. The caller must exclude source mutation
/// and freeing throughout the call.
#[no_mangle]
pub unsafe extern "C" fn rt_array_i64_copy_checked(raw: i64, out: *mut i64, capacity: i64) -> i64 {
    let Some(ptr) = get_typed_ptr::<RuntimeArray>(RuntimeValue(raw as u64), HeapObjectType::Array) else {
        return -22;
    };
    let array = &*ptr;
    let Some(length) = checked_length(array) else { return -22 };
    if capacity < length as i64 || (length > 0 && out.is_null()) {
        return -22;
    }
    for (index, item) in array.as_slice().iter().enumerate() {
        *out.add(index) = item.as_int();
    }
    length as i64
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::super::collections::{
        rt_array_free, rt_array_new, rt_array_new_with_cap_u64, rt_array_push,
        rt_byte_array_new_len, rt_tuple_new, rt_tuple_free,
    };
    use super::super::heap::get_typed_ptr_mut;

    #[test]
    fn signed_values_and_capacity_preserve_output() {
        let array = rt_array_new(3);
        let values = [-(1i64 << 60), -1, (1i64 << 60) - 1];
        for value in values { assert!(rt_array_push(array, RuntimeValue::from_int(value))); }
        let mut out = [99; 4];
        assert_eq!(rt_array_i64_validate(array.0 as i64), 3);
        for capacity in [-1, 0, 2] {
            assert_eq!(unsafe { rt_array_i64_copy_checked(array.0 as i64, out.as_mut_ptr(), capacity) }, -22);
            assert_eq!(out, [99; 4]);
        }
        assert_eq!(unsafe { rt_array_i64_copy_checked(array.0 as i64, std::ptr::null_mut(), 3) }, -22);
        assert_eq!(unsafe { rt_array_i64_copy_checked(array.0 as i64, out.as_mut_ptr(), 4) }, 3);
        assert_eq!(out, [values[0], values[1], values[2], 99]);
        rt_array_free(array);
    }

    #[test]
    fn empty_accepts_null_output_but_rejects_negative_capacity() {
        let array = rt_array_new(0);
        assert_eq!(rt_array_i64_validate(array.0 as i64), 0);
        assert_eq!(unsafe { rt_array_i64_copy_checked(array.0 as i64, std::ptr::null_mut(), 0) }, 0);
        assert_eq!(unsafe { rt_array_i64_copy_checked(array.0 as i64, std::ptr::null_mut(), -1) }, -22);
        rt_array_free(array);
    }

    #[test]
    fn rejects_invalid_handles_representations_and_late_noninteger() {
        for raw in [0, 3, 0x10001, -1] {
            assert_eq!(rt_array_i64_validate(raw), -22);
            assert_eq!(unsafe { rt_array_i64_copy_checked(raw, std::ptr::null_mut(), 0) }, -22);
        }
        for array in [rt_byte_array_new_len(2), rt_array_new_with_cap_u64(2)] {
            assert_eq!(rt_array_i64_validate(array.0 as i64), -22);
            rt_array_free(array);
        }
        let tuple = rt_tuple_new(0);
        assert_eq!(rt_array_i64_validate(tuple.0 as i64), -22);
        rt_tuple_free(tuple);
        let array = rt_array_new(2);
        assert!(rt_array_push(array, RuntimeValue::from_int(7)));
        assert!(rt_array_push(array, RuntimeValue::NIL));
        let mut out = [91, 92];
        assert_eq!(rt_array_i64_validate(array.0 as i64), -22);
        assert_eq!(unsafe { rt_array_i64_copy_checked(array.0 as i64, out.as_mut_ptr(), 2) }, -22);
        assert_eq!(out, [91, 92]);
        rt_array_free(array);
        assert_eq!(rt_array_i64_validate(array.0 as i64), -22);
    }

    #[test]
    fn rejects_corrupt_lengths_and_missing_storage() {
        let array = rt_array_new(1);
        assert!(rt_array_push(array, RuntimeValue::from_int(1)));
        let ptr = get_typed_ptr_mut::<RuntimeArray>(array, HeapObjectType::Array).unwrap();
        unsafe {
            let original_capacity = (*ptr).capacity;
            (*ptr).len = original_capacity + 1;
            assert_eq!(rt_array_i64_validate(array.0 as i64), -22);
            (*ptr).len = u64::MAX;
            (*ptr).capacity = u64::MAX;
            assert_eq!(rt_array_i64_validate(array.0 as i64), -22);
            (*ptr).len = 1;
            (*ptr).capacity = original_capacity;
            let data = (*ptr).data;
            (*ptr).data = std::ptr::null_mut();
            assert_eq!(rt_array_i64_validate(array.0 as i64), -22);
            (*ptr).len = 0;
            assert_eq!(rt_array_i64_validate(array.0 as i64), 0);
            (*ptr).data = data;
        }
        rt_array_free(array);
    }
}
