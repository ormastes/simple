//! SIMD vector operations for Simple language runtime
//!
//! Provides FFI functions for vector reduction, lane access, element-wise math,
//! and shuffle/blend operations on RuntimeValue arrays.

use super::collections::{rt_array_get, rt_array_len, rt_array_new, rt_array_push, RuntimeArray};
use super::core::RuntimeValue;
use super::heap::{get_typed_ptr, HeapObjectType};

// =============================================================================
// Helper Functions
// =============================================================================

/// Get array pointer from RuntimeValue, returning None if not an array
#[inline]
fn get_array(val: RuntimeValue) -> Option<*const RuntimeArray> {
    get_typed_ptr::<RuntimeArray>(val, HeapObjectType::Array)
}

/// Get element from array at index
#[inline]
fn array_get_element(arr: *const RuntimeArray, index: usize) -> RuntimeValue {
    unsafe {
        if index < (*arr).len as usize {
            let data_ptr = arr.add(1) as *const RuntimeValue;
            *data_ptr.add(index)
        } else {
            RuntimeValue::NIL
        }
    }
}

/// Get array length
#[inline]
fn array_len(arr: *const RuntimeArray) -> usize {
    unsafe { (*arr).len as usize }
}

/// Create a new array and populate it with elements
fn create_array_from_fn<F>(len: usize, mut f: F) -> RuntimeValue
where
    F: FnMut(usize) -> RuntimeValue,
{
    let arr_val = rt_array_new(len as u64);
    for i in 0..len {
        let elem = f(i);
        rt_array_push(arr_val, elem);
    }
    arr_val
}

// =============================================================================
// Reduction Operations
// =============================================================================

/// Sum all elements in a vector.
///
/// # Parameters
/// - `vec`: RuntimeValue containing an array of numbers
///
/// # Returns
/// Sum of all elements as RuntimeValue
#[no_mangle]
pub extern "C" fn rt_vec_sum(vec: RuntimeValue) -> RuntimeValue {
    let arr = match get_array(vec) {
        Some(a) => a,
        None => return RuntimeValue::from_int(0),
    };

    let len = array_len(arr);
    if len == 0 {
        return RuntimeValue::from_int(0);
    }

    let mut int_sum: i64 = 0;
    let mut float_sum: f64 = 0.0;
    let mut is_float = false;

    for i in 0..len {
        let elem = array_get_element(arr, i);
        if elem.is_float() {
            if !is_float {
                float_sum = int_sum as f64;
                is_float = true;
            }
            float_sum += elem.as_float();
        } else if elem.is_int() {
            if is_float {
                float_sum += elem.as_int() as f64;
            } else {
                int_sum = int_sum.wrapping_add(elem.as_int());
            }
        }
    }

    if is_float {
        RuntimeValue::from_float(float_sum)
    } else {
        RuntimeValue::from_int(int_sum)
    }
}

/// Multiply all elements in a vector.
///
/// # Parameters
/// - `vec`: RuntimeValue containing an array of numbers
///
/// # Returns
/// Product of all elements as RuntimeValue
#[no_mangle]
pub extern "C" fn rt_vec_product(vec: RuntimeValue) -> RuntimeValue {
    let arr = match get_array(vec) {
        Some(a) => a,
        None => return RuntimeValue::from_int(1),
    };

    let len = array_len(arr);
    if len == 0 {
        return RuntimeValue::from_int(1);
    }

    let mut int_product: i64 = 1;
    let mut float_product: f64 = 1.0;
    let mut is_float = false;

    for i in 0..len {
        let elem = array_get_element(arr, i);
        if elem.is_float() {
            if !is_float {
                float_product = int_product as f64;
                is_float = true;
            }
            float_product *= elem.as_float();
        } else if elem.is_int() {
            if is_float {
                float_product *= elem.as_int() as f64;
            } else {
                int_product = int_product.wrapping_mul(elem.as_int());
            }
        }
    }

    if is_float {
        RuntimeValue::from_float(float_product)
    } else {
        RuntimeValue::from_int(int_product)
    }
}

/// Find minimum element in a vector.
///
/// # Parameters
/// - `vec`: RuntimeValue containing an array of numbers
///
/// # Returns
/// Minimum element as RuntimeValue
#[no_mangle]
pub extern "C" fn rt_vec_min(vec: RuntimeValue) -> RuntimeValue {
    let arr = match get_array(vec) {
        Some(a) => a,
        None => return RuntimeValue::NIL,
    };

    let len = array_len(arr);
    if len == 0 {
        return RuntimeValue::NIL;
    }

    let mut min_val = array_get_element(arr, 0);

    for i in 1..len {
        let elem = array_get_element(arr, i);
        if compare_values(elem, min_val) < 0 {
            min_val = elem;
        }
    }

    min_val
}

/// Find maximum element in a vector.
///
/// # Parameters
/// - `vec`: RuntimeValue containing an array of numbers
///
/// # Returns
/// Maximum element as RuntimeValue
#[no_mangle]
pub extern "C" fn rt_vec_max(vec: RuntimeValue) -> RuntimeValue {
    let arr = match get_array(vec) {
        Some(a) => a,
        None => return RuntimeValue::NIL,
    };

    let len = array_len(arr);
    if len == 0 {
        return RuntimeValue::NIL;
    }

    let mut max_val = array_get_element(arr, 0);

    for i in 1..len {
        let elem = array_get_element(arr, i);
        if compare_values(elem, max_val) > 0 {
            max_val = elem;
        }
    }

    max_val
}

/// Check if all elements are truthy.
///
/// # Parameters
/// - `vec`: RuntimeValue containing an array
///
/// # Returns
/// true if all elements are truthy, false otherwise
#[no_mangle]
pub extern "C" fn rt_vec_all(vec: RuntimeValue) -> bool {
    let arr = match get_array(vec) {
        Some(a) => a,
        None => return false,
    };

    let len = array_len(arr);
    for i in 0..len {
        let elem = array_get_element(arr, i);
        if !elem.truthy() {
            return false;
        }
    }
    true
}

/// Check if any element is truthy.
///
/// # Parameters
/// - `vec`: RuntimeValue containing an array
///
/// # Returns
/// true if any element is truthy, false otherwise
#[no_mangle]
pub extern "C" fn rt_vec_any(vec: RuntimeValue) -> bool {
    let arr = match get_array(vec) {
        Some(a) => a,
        None => return false,
    };

    let len = array_len(arr);
    for i in 0..len {
        let elem = array_get_element(arr, i);
        if elem.truthy() {
            return true;
        }
    }
    false
}

// =============================================================================
// Lane Access Operations
// =============================================================================

/// Extract an element from a vector at the given index.
///
/// # Parameters
/// - `vec`: RuntimeValue containing an array
/// - `index`: Index to extract
///
/// # Returns
/// Element at index, or NIL if out of bounds
#[no_mangle]
pub extern "C" fn rt_vec_extract(vec: RuntimeValue, index: u64) -> RuntimeValue {
    let arr = match get_array(vec) {
        Some(a) => a,
        None => return RuntimeValue::NIL,
    };

    array_get_element(arr, index as usize)
}

/// Create a new vector with the element at the given index replaced.
///
/// # Parameters
/// - `vec`: RuntimeValue containing an array
/// - `index`: Index to replace
/// - `value`: New value
///
/// # Returns
/// New vector with the element replaced
#[no_mangle]
pub extern "C" fn rt_vec_with(vec: RuntimeValue, index: u64, value: RuntimeValue) -> RuntimeValue {
    let arr = match get_array(vec) {
        Some(a) => a,
        None => return RuntimeValue::NIL,
    };

    let len = array_len(arr);
    let idx = index as usize;

    create_array_from_fn(len, |i| if i == idx { value } else { array_get_element(arr, i) })
}

// =============================================================================
// Element-wise Math Operations
// =============================================================================

/// Apply sqrt to all elements in a vector.
#[no_mangle]
pub extern "C" fn rt_vec_sqrt(vec: RuntimeValue) -> RuntimeValue {
    apply_unary_op(vec, |v| {
        if v.is_int() {
            RuntimeValue::from_float((v.as_int() as f64).sqrt())
        } else if v.is_float() {
            RuntimeValue::from_float(v.as_float().sqrt())
        } else {
            v
        }
    })
}

/// Apply abs to all elements in a vector.
#[no_mangle]
pub extern "C" fn rt_vec_abs(vec: RuntimeValue) -> RuntimeValue {
    apply_unary_op(vec, |v| {
        if v.is_int() {
            RuntimeValue::from_int(v.as_int().abs())
        } else if v.is_float() {
            RuntimeValue::from_float(v.as_float().abs())
        } else {
            v
        }
    })
}

/// Apply floor to all elements in a vector.
#[no_mangle]
pub extern "C" fn rt_vec_floor(vec: RuntimeValue) -> RuntimeValue {
    apply_unary_op(vec, |v| {
        if v.is_int() {
            v
        } else if v.is_float() {
            RuntimeValue::from_float(v.as_float().floor())
        } else {
            v
        }
    })
}

/// Apply ceil to all elements in a vector.
#[no_mangle]
pub extern "C" fn rt_vec_ceil(vec: RuntimeValue) -> RuntimeValue {
    apply_unary_op(vec, |v| {
        if v.is_int() {
            v
        } else if v.is_float() {
            RuntimeValue::from_float(v.as_float().ceil())
        } else {
            v
        }
    })
}

/// Apply round to all elements in a vector.
#[no_mangle]
pub extern "C" fn rt_vec_round(vec: RuntimeValue) -> RuntimeValue {
    apply_unary_op(vec, |v| {
        if v.is_int() {
            v
        } else if v.is_float() {
            RuntimeValue::from_float(v.as_float().round())
        } else {
            v
        }
    })
}

// =============================================================================
// Shuffle/Blend Operations
// =============================================================================

/// Shuffle elements according to index vector.
///
/// # Parameters
/// - `vec`: Source vector
/// - `indices`: Index vector specifying the shuffle pattern
///
/// # Returns
/// New vector with shuffled elements
#[no_mangle]
pub extern "C" fn rt_vec_shuffle(vec: RuntimeValue, indices: RuntimeValue) -> RuntimeValue {
    let src = match get_array(vec) {
        Some(a) => a,
        None => return RuntimeValue::NIL,
    };
    let idx_arr = match get_array(indices) {
        Some(a) => a,
        None => return RuntimeValue::NIL,
    };

    let src_len = array_len(src);
    let idx_len = array_len(idx_arr);

    create_array_from_fn(idx_len, |i| {
        let idx_val = array_get_element(idx_arr, i);
        if idx_val.is_int() {
            let idx = idx_val.as_int();
            if idx >= 0 && (idx as usize) < src_len {
                array_get_element(src, idx as usize)
            } else {
                RuntimeValue::NIL
            }
        } else {
            RuntimeValue::NIL
        }
    })
}

/// Blend two vectors based on a mask.
///
/// # Parameters
/// - `v1`: First source vector
/// - `v2`: Second source vector
/// - `mask`: Mask vector (truthy = use v1, falsy = use v2)
///
/// # Returns
/// New vector with blended elements
#[no_mangle]
pub extern "C" fn rt_vec_blend(v1: RuntimeValue, v2: RuntimeValue, mask: RuntimeValue) -> RuntimeValue {
    let arr1 = match get_array(v1) {
        Some(a) => a,
        None => return RuntimeValue::NIL,
    };
    let arr2 = match get_array(v2) {
        Some(a) => a,
        None => return RuntimeValue::NIL,
    };
    let mask_arr = match get_array(mask) {
        Some(a) => a,
        None => return RuntimeValue::NIL,
    };

    let len = array_len(arr1).min(array_len(arr2)).min(array_len(mask_arr));

    create_array_from_fn(len, |i| {
        let use_first = array_get_element(mask_arr, i).truthy();
        if use_first {
            array_get_element(arr1, i)
        } else {
            array_get_element(arr2, i)
        }
    })
}

/// Select elements from two vectors based on a mask.
///
/// # Parameters
/// - `mask`: Mask vector (truthy = use if_true, falsy = use if_false)
/// - `if_true`: Values to use when mask is truthy
/// - `if_false`: Values to use when mask is falsy
///
/// # Returns
/// New vector with selected elements
#[no_mangle]
pub extern "C" fn rt_vec_select(mask: RuntimeValue, if_true: RuntimeValue, if_false: RuntimeValue) -> RuntimeValue {
    rt_vec_blend(if_true, if_false, mask)
}

// =============================================================================
// Load/Store Operations
// =============================================================================

/// Load elements from array starting at offset.
///
/// # Parameters
/// - `arr`: Source array
/// - `offset`: Starting offset
///
/// # Returns
/// New vector containing elements from arr[offset..]
#[no_mangle]
pub extern "C" fn rt_vec_load(arr: RuntimeValue, offset: i64) -> RuntimeValue {
    let src = match get_array(arr) {
        Some(a) => a,
        None => return RuntimeValue::NIL,
    };

    let src_len = array_len(src);
    let start = offset.max(0) as usize;

    if start >= src_len {
        return rt_array_new(0);
    }

    // Load 4 elements (typical SIMD width) or remaining elements
    let count = (src_len - start).min(4);
    create_array_from_fn(count, |i| array_get_element(src, start + i))
}

/// Store vector elements into array at offset.
///
/// # Parameters
/// - `vec`: Source vector to store
/// - `arr`: Target array
/// - `offset`: Starting offset in target array
#[no_mangle]
pub extern "C" fn rt_vec_store(vec: RuntimeValue, arr: RuntimeValue, offset: i64) {
    let src = match get_array(vec) {
        Some(a) => a,
        None => return,
    };
    let dst = match get_array(arr) {
        Some(a) => a,
        None => return,
    };

    let src_len = array_len(src);
    let dst_len = array_len(dst);
    let start = offset.max(0) as usize;

    // Store elements directly to the array data
    for i in 0..src_len {
        let idx = start + i;
        if idx >= dst_len {
            break;
        }
        let elem = array_get_element(src, i);
        // Use rt_array_set to store the element
        super::collections::rt_array_set(arr, idx as i64, elem);
    }
}

/// Gather elements from array at scattered indices.
///
/// # Parameters
/// - `arr`: Source array
/// - `indices`: Vector of indices
///
/// # Returns
/// New vector containing arr[indices[i]] for each i
#[no_mangle]
pub extern "C" fn rt_vec_gather(arr: RuntimeValue, indices: RuntimeValue) -> RuntimeValue {
    let src = match get_array(arr) {
        Some(a) => a,
        None => return RuntimeValue::NIL,
    };
    let idx_arr = match get_array(indices) {
        Some(a) => a,
        None => return RuntimeValue::NIL,
    };

    let src_len = array_len(src);
    let idx_len = array_len(idx_arr);

    create_array_from_fn(idx_len, |i| {
        let idx_val = array_get_element(idx_arr, i);
        if idx_val.is_int() {
            let idx = idx_val.as_int();
            if idx >= 0 && (idx as usize) < src_len {
                array_get_element(src, idx as usize)
            } else {
                RuntimeValue::NIL
            }
        } else {
            RuntimeValue::NIL
        }
    })
}

/// Scatter vector elements into array at scattered indices.
///
/// # Parameters
/// - `vec`: Source vector
/// - `arr`: Target array
/// - `indices`: Vector of target indices
#[no_mangle]
pub extern "C" fn rt_vec_scatter(vec: RuntimeValue, arr: RuntimeValue, indices: RuntimeValue) {
    let src = match get_array(vec) {
        Some(a) => a,
        None => return,
    };
    let idx_arr = match get_array(indices) {
        Some(a) => a,
        None => return,
    };

    let src_len = array_len(src);
    let dst_len = rt_array_len(arr);
    let idx_len = array_len(idx_arr);

    for i in 0..idx_len.min(src_len) {
        let idx_val = array_get_element(idx_arr, i);
        if idx_val.is_int() {
            let idx = idx_val.as_int();
            if idx >= 0 && idx < dst_len {
                let elem = array_get_element(src, i);
                super::collections::rt_array_set(arr, idx, elem);
            }
        }
    }
}

// =============================================================================
// Advanced Math Operations
// =============================================================================

/// Fused multiply-add: a * b + c (element-wise).
///
/// # Parameters
/// - `a`, `b`, `c`: Input vectors
///
/// # Returns
/// New vector with a[i] * b[i] + c[i] for each i
#[no_mangle]
pub extern "C" fn rt_vec_fma(a: RuntimeValue, b: RuntimeValue, c: RuntimeValue) -> RuntimeValue {
    let arr_a = match get_array(a) {
        Some(x) => x,
        None => return RuntimeValue::NIL,
    };
    let arr_b = match get_array(b) {
        Some(x) => x,
        None => return RuntimeValue::NIL,
    };
    let arr_c = match get_array(c) {
        Some(x) => x,
        None => return RuntimeValue::NIL,
    };

    let len = array_len(arr_a).min(array_len(arr_b)).min(array_len(arr_c));

    create_array_from_fn(len, |i| {
        let va = array_get_element(arr_a, i);
        let vb = array_get_element(arr_b, i);
        let vc = array_get_element(arr_c, i);

        // Convert to float for FMA operation
        let fa = if va.is_float() {
            va.as_float()
        } else if va.is_int() {
            va.as_int() as f64
        } else {
            0.0
        };
        let fb = if vb.is_float() {
            vb.as_float()
        } else if vb.is_int() {
            vb.as_int() as f64
        } else {
            0.0
        };
        let fc = if vc.is_float() {
            vc.as_float()
        } else if vc.is_int() {
            vc.as_int() as f64
        } else {
            0.0
        };

        RuntimeValue::from_float(fa.mul_add(fb, fc))
    })
}

/// Reciprocal: 1.0 / x (element-wise).
///
/// # Parameters
/// - `vec`: Input vector
///
/// # Returns
/// New vector with 1.0 / vec[i] for each i
#[no_mangle]
pub extern "C" fn rt_vec_recip(vec: RuntimeValue) -> RuntimeValue {
    apply_unary_op(vec, |v| {
        if v.is_float() {
            RuntimeValue::from_float(1.0 / v.as_float())
        } else if v.is_int() {
            RuntimeValue::from_float(1.0 / (v.as_int() as f64))
        } else {
            RuntimeValue::from_float(f64::INFINITY)
        }
    })
}

/// Masked load: load elements where mask is true, use default otherwise.
///
/// # Parameters
/// - `arr`: Source array
/// - `offset`: Starting offset
/// - `mask`: Boolean mask vector
/// - `default`: Default values for masked-out lanes
///
/// # Returns
/// New vector with loaded/default values
#[no_mangle]
pub extern "C" fn rt_vec_masked_load(
    arr: RuntimeValue,
    offset: i64,
    mask: RuntimeValue,
    default: RuntimeValue,
) -> RuntimeValue {
    let src = match get_array(arr) {
        Some(a) => a,
        None => return default,
    };
    let mask_arr = match get_array(mask) {
        Some(a) => a,
        None => return default,
    };
    let def_arr = match get_array(default) {
        Some(a) => a,
        None => return RuntimeValue::NIL,
    };

    let src_len = array_len(src);
    let mask_len = array_len(mask_arr);
    let def_len = array_len(def_arr);
    let start = offset.max(0) as usize;
    let len = mask_len.min(def_len);

    create_array_from_fn(len, |i| {
        let use_src = array_get_element(mask_arr, i).truthy();
        if use_src && (start + i) < src_len {
            array_get_element(src, start + i)
        } else {
            array_get_element(def_arr, i)
        }
    })
}

/// Masked store: store elements only where mask is true.
///
/// # Parameters
/// - `vec`: Source vector
/// - `arr`: Target array
/// - `offset`: Starting offset in target
/// - `mask`: Boolean mask vector
#[no_mangle]
pub extern "C" fn rt_vec_masked_store(vec: RuntimeValue, arr: RuntimeValue, offset: i64, mask: RuntimeValue) {
    let src = match get_array(vec) {
        Some(a) => a,
        None => return,
    };
    let mask_arr = match get_array(mask) {
        Some(a) => a,
        None => return,
    };

    let src_len = array_len(src);
    let dst_len = rt_array_len(arr);
    let mask_len = array_len(mask_arr);
    let start = offset.max(0) as usize;

    for i in 0..src_len.min(mask_len) {
        let use_src = array_get_element(mask_arr, i).truthy();
        if use_src {
            let idx = (start + i) as i64;
            if idx < dst_len {
                let elem = array_get_element(src, i);
                super::collections::rt_array_set(arr, idx, elem);
            }
        }
    }
}

/// Element-wise minimum of two vectors.
///
/// # Parameters
/// - `a`, `b`: Input vectors
///
/// # Returns
/// New vector with min(a[i], b[i]) for each i
#[no_mangle]
pub extern "C" fn rt_vec_min_vec(a: RuntimeValue, b: RuntimeValue) -> RuntimeValue {
    apply_binary_op(a, b, |va, vb| if compare_values(va, vb) <= 0 { va } else { vb })
}

/// Element-wise maximum of two vectors.
///
/// # Parameters
/// - `a`, `b`: Input vectors
///
/// # Returns
/// New vector with max(a[i], b[i]) for each i
#[no_mangle]
pub extern "C" fn rt_vec_max_vec(a: RuntimeValue, b: RuntimeValue) -> RuntimeValue {
    apply_binary_op(a, b, |va, vb| if compare_values(va, vb) >= 0 { va } else { vb })
}

/// Clamp elements to range [lo, hi].
///
/// # Parameters
/// - `vec`: Input vector
/// - `lo`: Lower bound vector
/// - `hi`: Upper bound vector
///
/// # Returns
/// New vector with clamped values
#[no_mangle]
pub extern "C" fn rt_vec_clamp(vec: RuntimeValue, lo: RuntimeValue, hi: RuntimeValue) -> RuntimeValue {
    let arr = match get_array(vec) {
        Some(a) => a,
        None => return RuntimeValue::NIL,
    };
    let lo_arr = match get_array(lo) {
        Some(a) => a,
        None => return RuntimeValue::NIL,
    };
    let hi_arr = match get_array(hi) {
        Some(a) => a,
        None => return RuntimeValue::NIL,
    };

    let len = array_len(arr).min(array_len(lo_arr)).min(array_len(hi_arr));

    create_array_from_fn(len, |i| {
        let v = array_get_element(arr, i);
        let lo_v = array_get_element(lo_arr, i);
        let hi_v = array_get_element(hi_arr, i);

        // clamp(v, lo, hi) = max(lo, min(v, hi))
        let clamped_hi = if compare_values(v, hi_v) <= 0 { v } else { hi_v };
        if compare_values(clamped_hi, lo_v) >= 0 {
            clamped_hi
        } else {
            lo_v
        }
    })
}

/// Load from neighbor index (for stencil operations).
///
/// # Parameters
/// - `arr`: Source array
/// - `direction`: 0 = previous (-1), 1 = next (+1)
///
/// # Returns
/// Value from neighboring index (wraps at boundaries)
#[no_mangle]
pub extern "C" fn rt_neighbor_load(arr: RuntimeValue, direction: i64) -> RuntimeValue {
    let src = match get_array(arr) {
        Some(a) => a,
        None => return RuntimeValue::NIL,
    };

    let len = array_len(src);
    if len == 0 {
        return RuntimeValue::NIL;
    }

    // For stencil operations, this would typically be called within a parallel
    // context where each thread has an implicit index. For now, we return NIL
    // since we don't have thread-local state to track the current index.
    // In a real SIMD/GPU implementation, the current lane index would be available.
    RuntimeValue::NIL
}

// =============================================================================
// Helper Functions
// =============================================================================

fn apply_binary_op<F>(a: RuntimeValue, b: RuntimeValue, op: F) -> RuntimeValue
where
    F: Fn(RuntimeValue, RuntimeValue) -> RuntimeValue,
{
    let arr_a = match get_array(a) {
        Some(x) => x,
        None => return RuntimeValue::NIL,
    };
    let arr_b = match get_array(b) {
        Some(x) => x,
        None => return RuntimeValue::NIL,
    };

    let len = array_len(arr_a).min(array_len(arr_b));
    create_array_from_fn(len, |i| {
        let va = array_get_element(arr_a, i);
        let vb = array_get_element(arr_b, i);
        op(va, vb)
    })
}

// =============================================================================
// Helper Functions
// =============================================================================

fn apply_unary_op<F>(vec: RuntimeValue, op: F) -> RuntimeValue
where
    F: Fn(RuntimeValue) -> RuntimeValue,
{
    let arr = match get_array(vec) {
        Some(a) => a,
        None => return RuntimeValue::NIL,
    };

    let len = array_len(arr);
    create_array_from_fn(len, |i| {
        let elem = array_get_element(arr, i);
        op(elem)
    })
}

fn compare_values(a: RuntimeValue, b: RuntimeValue) -> i32 {
    if a.is_int() && b.is_int() {
        let ai = a.as_int();
        let bi = b.as_int();
        if ai < bi {
            -1
        } else if ai > bi {
            1
        } else {
            0
        }
    } else if a.is_float() && b.is_float() {
        let af = a.as_float();
        let bf = b.as_float();
        if af < bf {
            -1
        } else if af > bf {
            1
        } else {
            0
        }
    } else if a.is_int() && b.is_float() {
        let af = a.as_int() as f64;
        let bf = b.as_float();
        if af < bf {
            -1
        } else if af > bf {
            1
        } else {
            0
        }
    } else if a.is_float() && b.is_int() {
        let af = a.as_float();
        let bf = b.as_int() as f64;
        if af < bf {
            -1
        } else if af > bf {
            1
        } else {
            0
        }
    } else {
        0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_vec_sum_empty() {
        let arr = rt_array_new(0);
        let result = rt_vec_sum(arr);
        assert!(result.is_int());
        assert_eq!(result.as_int(), 0);
    }

    #[test]
    fn test_vec_sum_ints() {
        let arr = rt_array_new(3);
        rt_array_push(arr, RuntimeValue::from_int(1));
        rt_array_push(arr, RuntimeValue::from_int(2));
        rt_array_push(arr, RuntimeValue::from_int(3));
        let result = rt_vec_sum(arr);
        assert!(result.is_int());
        assert_eq!(result.as_int(), 6);
    }

    #[test]
    fn test_vec_product_ints() {
        let arr = rt_array_new(3);
        rt_array_push(arr, RuntimeValue::from_int(2));
        rt_array_push(arr, RuntimeValue::from_int(3));
        rt_array_push(arr, RuntimeValue::from_int(4));
        let result = rt_vec_product(arr);
        assert!(result.is_int());
        assert_eq!(result.as_int(), 24);
    }

    #[test]
    fn test_vec_min() {
        let arr = rt_array_new(4);
        rt_array_push(arr, RuntimeValue::from_int(5));
        rt_array_push(arr, RuntimeValue::from_int(2));
        rt_array_push(arr, RuntimeValue::from_int(8));
        rt_array_push(arr, RuntimeValue::from_int(1));
        let result = rt_vec_min(arr);
        assert!(result.is_int());
        assert_eq!(result.as_int(), 1);
    }

    #[test]
    fn test_vec_max() {
        let arr = rt_array_new(4);
        rt_array_push(arr, RuntimeValue::from_int(5));
        rt_array_push(arr, RuntimeValue::from_int(2));
        rt_array_push(arr, RuntimeValue::from_int(8));
        rt_array_push(arr, RuntimeValue::from_int(1));
        let result = rt_vec_max(arr);
        assert!(result.is_int());
        assert_eq!(result.as_int(), 8);
    }

    #[test]
    fn test_vec_all_true() {
        let arr = rt_array_new(3);
        rt_array_push(arr, RuntimeValue::from_bool(true));
        rt_array_push(arr, RuntimeValue::from_int(1));
        rt_array_push(arr, RuntimeValue::from_int(42));
        assert!(rt_vec_all(arr));
    }

    #[test]
    fn test_vec_all_false() {
        let arr = rt_array_new(3);
        rt_array_push(arr, RuntimeValue::from_bool(true));
        rt_array_push(arr, RuntimeValue::from_int(0));
        rt_array_push(arr, RuntimeValue::from_int(42));
        assert!(!rt_vec_all(arr));
    }

    #[test]
    fn test_vec_any_true() {
        let arr = rt_array_new(3);
        rt_array_push(arr, RuntimeValue::from_bool(false));
        rt_array_push(arr, RuntimeValue::from_int(0));
        rt_array_push(arr, RuntimeValue::from_int(1));
        assert!(rt_vec_any(arr));
    }

    #[test]
    fn test_vec_any_false() {
        let arr = rt_array_new(3);
        rt_array_push(arr, RuntimeValue::from_bool(false));
        rt_array_push(arr, RuntimeValue::from_int(0));
        rt_array_push(arr, RuntimeValue::NIL);
        assert!(!rt_vec_any(arr));
    }

    #[test]
    fn test_vec_extract() {
        let arr = rt_array_new(3);
        rt_array_push(arr, RuntimeValue::from_int(10));
        rt_array_push(arr, RuntimeValue::from_int(20));
        rt_array_push(arr, RuntimeValue::from_int(30));

        assert_eq!(rt_vec_extract(arr, 0).as_int(), 10);
        assert_eq!(rt_vec_extract(arr, 1).as_int(), 20);
        assert_eq!(rt_vec_extract(arr, 2).as_int(), 30);
    }
}
