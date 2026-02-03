//! RC/ARC FFI wrappers for Simple language
//!
//! Thin wrappers around std::rc::Rc and std::sync::Arc.
//! Uses raw pointer approach where Simple manages allocation with sys_malloc/sys_free.
//!
//! Memory layout:
//! ```
//! RcBox<T> / ArcBox<T>:
//! ┌────────────────────────────────┐
//! │ strong_count: usize/AtomicUsize │
//! ├────────────────────────────────┤
//! │ weak_count: usize/AtomicUsize   │
//! ├────────────────────────────────┤
//! │ value: T                        │
//! └────────────────────────────────┘
//! ```
//!
//! Simple code calls sys_malloc() to allocate memory, then calls rc_box_init()
//! to initialize the box with counts and value.

use crate::error::CompileError;
use crate::value::Value;
use std::mem::{size_of, align_of};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::ptr;

// ============================================================================
// Rc Box Operations (Non-Atomic)
// ============================================================================

/// Get size of RcBox<T> for allocation
///
/// Returns: size_of(usize) * 2 + size_of(T)
pub fn rc_box_size(args: &[Value]) -> Result<Value, CompileError> {
    // For now, we return a fixed size since we don't have generic type info
    // In practice, Simple will pass the value and we calculate from that
    if args.is_empty() {
        // Generic call - return header size (2 * usize)
        Ok(Value::Int((size_of::<usize>() * 2) as i64))
    } else {
        // Calculate size based on value type
        let value_size = match &args[0] {
            Value::Int(_) => size_of::<i64>(),
            Value::Float(_) => size_of::<f64>(),
            Value::Bool(_) => size_of::<bool>(),
            Value::Str(s) => size_of::<usize>() * 2 + s.len(), // String size
            Value::Array(arr) => size_of::<usize>() * 2 + arr.len() * size_of::<Value>(),
            _ => size_of::<Value>(), // Default to Value size
        };
        let total = size_of::<usize>() * 2 + value_size;
        Ok(Value::Int(total as i64))
    }
}

/// Initialize RcBox with value and counts
///
/// Args: (ptr: Array<u8>, value: T, strong: Int, weak: Int)
pub fn rc_box_init(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 4 {
        return Err(CompileError::runtime("rc_box_init requires 4 arguments (ptr, value, strong, weak)"));
    }

    let ptr = match &args[0] {
        Value::Array(bytes) => {
            if bytes.is_empty() {
                return Err(CompileError::runtime("rc_box_init: ptr is null"));
            }
            // Get raw pointer from array
            bytes.as_ptr() as *mut u8
        }
        _ => return Err(CompileError::runtime("rc_box_init: first argument must be byte array")),
    };

    let value = args[1].clone();
    let strong = args[2].as_int()? as usize;
    let weak = args[3].as_int()? as usize;

    unsafe {
        // Write strong count at offset 0
        let strong_ptr = ptr as *mut usize;
        ptr::write(strong_ptr, strong);

        // Write weak count at offset sizeof(usize)
        let weak_ptr = ptr.add(size_of::<usize>()) as *mut usize;
        ptr::write(weak_ptr, weak);

        // Write value at offset sizeof(usize) * 2
        let value_ptr = ptr.add(size_of::<usize>() * 2) as *mut Value;
        ptr::write(value_ptr, value);
    }

    Ok(Value::Nil)
}

/// Get value from RcBox
///
/// Args: (ptr: Array<u8>)
/// Returns: T (cloned)
pub fn rc_box_get_value(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime("rc_box_get_value requires 1 argument (ptr)"));
    }

    let ptr = match &args[0] {
        Value::Array(bytes) => {
            if bytes.is_empty() {
                return Err(CompileError::runtime("rc_box_get_value: ptr is null"));
            }
            bytes.as_ptr() as *mut u8
        }
        _ => return Err(CompileError::runtime("rc_box_get_value: argument must be byte array")),
    };

    unsafe {
        // Read value at offset sizeof(usize) * 2
        let value_ptr = ptr.add(size_of::<usize>() * 2) as *const Value;
        Ok((*value_ptr).clone())
    }
}

/// Drop value in RcBox (run destructor)
///
/// Args: (ptr: Array<u8>)
pub fn rc_box_drop_value(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime("rc_box_drop_value requires 1 argument (ptr)"));
    }

    let ptr = match &args[0] {
        Value::Array(bytes) => {
            if bytes.is_empty() {
                return Err(CompileError::runtime("rc_box_drop_value: ptr is null"));
            }
            bytes.as_ptr() as *mut u8
        }
        _ => return Err(CompileError::runtime("rc_box_drop_value: argument must be byte array")),
    };

    unsafe {
        // Drop value at offset sizeof(usize) * 2
        let value_ptr = ptr.add(size_of::<usize>() * 2) as *mut Value;
        ptr::drop_in_place(value_ptr);
    }

    Ok(Value::Nil)
}

/// Get strong reference count
///
/// Args: (ptr: Array<u8>)
/// Returns: usize (strong count)
pub fn rc_box_strong_count(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime("rc_box_strong_count requires 1 argument (ptr)"));
    }

    let ptr = match &args[0] {
        Value::Array(bytes) => {
            if bytes.is_empty() {
                return Ok(Value::Int(0));
            }
            bytes.as_ptr() as *const u8
        }
        _ => return Err(CompileError::runtime("rc_box_strong_count: argument must be byte array")),
    };

    unsafe {
        let strong_ptr = ptr as *const usize;
        Ok(Value::Int(*strong_ptr as i64))
    }
}

/// Get weak reference count
///
/// Args: (ptr: Array<u8>)
/// Returns: usize (weak count)
pub fn rc_box_weak_count(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime("rc_box_weak_count requires 1 argument (ptr)"));
    }

    let ptr = match &args[0] {
        Value::Array(bytes) => {
            if bytes.is_empty() {
                return Ok(Value::Int(0));
            }
            bytes.as_ptr() as *const u8
        }
        _ => return Err(CompileError::runtime("rc_box_weak_count: argument must be byte array")),
    };

    unsafe {
        let weak_ptr = ptr.add(size_of::<usize>()) as *const usize;
        Ok(Value::Int(*weak_ptr as i64))
    }
}

/// Increment strong reference count
///
/// Args: (ptr: Array<u8>)
pub fn rc_box_inc_strong(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime("rc_box_inc_strong requires 1 argument (ptr)"));
    }

    let ptr = match &args[0] {
        Value::Array(bytes) => {
            if bytes.is_empty() {
                return Err(CompileError::runtime("rc_box_inc_strong: ptr is null"));
            }
            bytes.as_ptr() as *mut u8
        }
        _ => return Err(CompileError::runtime("rc_box_inc_strong: argument must be byte array")),
    };

    unsafe {
        let strong_ptr = ptr as *mut usize;
        *strong_ptr += 1;
    }

    Ok(Value::Nil)
}

/// Decrement strong reference count
///
/// Args: (ptr: Array<u8>)
/// Returns: usize (count after decrement)
pub fn rc_box_dec_strong(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime("rc_box_dec_strong requires 1 argument (ptr)"));
    }

    let ptr = match &args[0] {
        Value::Array(bytes) => {
            if bytes.is_empty() {
                return Ok(Value::Int(0));
            }
            bytes.as_ptr() as *mut u8
        }
        _ => return Err(CompileError::runtime("rc_box_dec_strong: argument must be byte array")),
    };

    unsafe {
        let strong_ptr = ptr as *mut usize;
        *strong_ptr -= 1;
        Ok(Value::Int(*strong_ptr as i64))
    }
}

/// Increment weak reference count
///
/// Args: (ptr: Array<u8>)
pub fn rc_box_inc_weak(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime("rc_box_inc_weak requires 1 argument (ptr)"));
    }

    let ptr = match &args[0] {
        Value::Array(bytes) => {
            if bytes.is_empty() {
                return Err(CompileError::runtime("rc_box_inc_weak: ptr is null"));
            }
            bytes.as_ptr() as *mut u8
        }
        _ => return Err(CompileError::runtime("rc_box_inc_weak: argument must be byte array")),
    };

    unsafe {
        let weak_ptr = ptr.add(size_of::<usize>()) as *mut usize;
        *weak_ptr += 1;
    }

    Ok(Value::Nil)
}

/// Decrement weak reference count
///
/// Args: (ptr: Array<u8>)
/// Returns: usize (count after decrement)
pub fn rc_box_dec_weak(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime("rc_box_dec_weak requires 1 argument (ptr)"));
    }

    let ptr = match &args[0] {
        Value::Array(bytes) => {
            if bytes.is_empty() {
                return Ok(Value::Int(0));
            }
            bytes.as_ptr() as *mut u8
        }
        _ => return Err(CompileError::runtime("rc_box_dec_weak: argument must be byte array")),
    };

    unsafe {
        let weak_ptr = ptr.add(size_of::<usize>()) as *mut usize;
        *weak_ptr -= 1;
        Ok(Value::Int(*weak_ptr as i64))
    }
}

// ============================================================================
// Arc Box Operations (Atomic)
// ============================================================================

/// Get size of ArcBox<T> for allocation
///
/// Returns: size_of(AtomicUsize) * 2 + size_of(T)
pub fn arc_box_size(args: &[Value]) -> Result<Value, CompileError> {
    // Same as rc_box_size since AtomicUsize has same size as usize
    rc_box_size(args)
}

/// Initialize ArcBox with value and counts (atomic)
///
/// Args: (ptr: Array<u8>, value: T, strong: Int, weak: Int)
pub fn arc_box_init(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 4 {
        return Err(CompileError::runtime("arc_box_init requires 4 arguments (ptr, value, strong, weak)"));
    }

    let ptr = match &args[0] {
        Value::Array(bytes) => {
            if bytes.is_empty() {
                return Err(CompileError::runtime("arc_box_init: ptr is null"));
            }
            bytes.as_ptr() as *mut u8
        }
        _ => return Err(CompileError::runtime("arc_box_init: first argument must be byte array")),
    };

    let value = args[1].clone();
    let strong = args[2].as_int()? as usize;
    let weak = args[3].as_int()? as usize;

    unsafe {
        // Write atomic strong count at offset 0
        let strong_ptr = ptr as *mut AtomicUsize;
        ptr::write(strong_ptr, AtomicUsize::new(strong));

        // Write atomic weak count at offset sizeof(AtomicUsize)
        let weak_ptr = ptr.add(size_of::<AtomicUsize>()) as *mut AtomicUsize;
        ptr::write(weak_ptr, AtomicUsize::new(weak));

        // Write value at offset sizeof(AtomicUsize) * 2
        let value_ptr = ptr.add(size_of::<AtomicUsize>() * 2) as *mut Value;
        ptr::write(value_ptr, value);
    }

    Ok(Value::Nil)
}

/// Get value from ArcBox
///
/// Args: (ptr: Array<u8>)
/// Returns: T (cloned)
pub fn arc_box_get_value(args: &[Value]) -> Result<Value, CompileError> {
    // Same as rc_box_get_value - value access doesn't need atomics
    rc_box_get_value(args)
}

/// Drop value in ArcBox (run destructor)
///
/// Args: (ptr: Array<u8>)
pub fn arc_box_drop_value(args: &[Value]) -> Result<Value, CompileError> {
    // Same as rc_box_drop_value
    rc_box_drop_value(args)
}

/// Get strong reference count (atomic load)
///
/// Args: (ptr: Array<u8>)
/// Returns: usize (strong count)
pub fn arc_box_strong_count(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime("arc_box_strong_count requires 1 argument (ptr)"));
    }

    let ptr = match &args[0] {
        Value::Array(bytes) => {
            if bytes.is_empty() {
                return Ok(Value::Int(0));
            }
            bytes.as_ptr() as *const u8
        }
        _ => return Err(CompileError::runtime("arc_box_strong_count: argument must be byte array")),
    };

    unsafe {
        let strong_ptr = ptr as *const AtomicUsize;
        let count = (*strong_ptr).load(Ordering::Acquire);
        Ok(Value::Int(count as i64))
    }
}

/// Get weak reference count (atomic load)
///
/// Args: (ptr: Array<u8>)
/// Returns: usize (weak count)
pub fn arc_box_weak_count(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime("arc_box_weak_count requires 1 argument (ptr)"));
    }

    let ptr = match &args[0] {
        Value::Array(bytes) => {
            if bytes.is_empty() {
                return Ok(Value::Int(0));
            }
            bytes.as_ptr() as *const u8
        }
        _ => return Err(CompileError::runtime("arc_box_weak_count: argument must be byte array")),
    };

    unsafe {
        let weak_ptr = ptr.add(size_of::<AtomicUsize>()) as *const AtomicUsize;
        let count = (*weak_ptr).load(Ordering::Acquire);
        Ok(Value::Int(count as i64))
    }
}

/// Increment strong reference count (atomic)
///
/// Args: (ptr: Array<u8>)
pub fn arc_box_inc_strong(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime("arc_box_inc_strong requires 1 argument (ptr)"));
    }

    let ptr = match &args[0] {
        Value::Array(bytes) => {
            if bytes.is_empty() {
                return Err(CompileError::runtime("arc_box_inc_strong: ptr is null"));
            }
            bytes.as_ptr() as *mut u8
        }
        _ => return Err(CompileError::runtime("arc_box_inc_strong: argument must be byte array")),
    };

    unsafe {
        let strong_ptr = ptr as *const AtomicUsize;
        (*strong_ptr).fetch_add(1, Ordering::Release);
    }

    Ok(Value::Nil)
}

/// Decrement strong reference count (atomic)
///
/// Args: (ptr: Array<u8>)
/// Returns: usize (count after decrement)
pub fn arc_box_dec_strong(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime("arc_box_dec_strong requires 1 argument (ptr)"));
    }

    let ptr = match &args[0] {
        Value::Array(bytes) => {
            if bytes.is_empty() {
                return Ok(Value::Int(0));
            }
            bytes.as_ptr() as *mut u8
        }
        _ => return Err(CompileError::runtime("arc_box_dec_strong: argument must be byte array")),
    };

    unsafe {
        let strong_ptr = ptr as *const AtomicUsize;
        let prev = (*strong_ptr).fetch_sub(1, Ordering::Release);
        Ok(Value::Int((prev - 1) as i64))
    }
}

/// Increment weak reference count (atomic)
///
/// Args: (ptr: Array<u8>)
pub fn arc_box_inc_weak(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime("arc_box_inc_weak requires 1 argument (ptr)"));
    }

    let ptr = match &args[0] {
        Value::Array(bytes) => {
            if bytes.is_empty() {
                return Err(CompileError::runtime("arc_box_inc_weak: ptr is null"));
            }
            bytes.as_ptr() as *mut u8
        }
        _ => return Err(CompileError::runtime("arc_box_inc_weak: argument must be byte array")),
    };

    unsafe {
        let weak_ptr = ptr.add(size_of::<AtomicUsize>()) as *const AtomicUsize;
        (*weak_ptr).fetch_add(1, Ordering::Release);
    }

    Ok(Value::Nil)
}

/// Decrement weak reference count (atomic)
///
/// Args: (ptr: Array<u8>)
/// Returns: usize (count after decrement)
pub fn arc_box_dec_weak(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime("arc_box_dec_weak requires 1 argument (ptr)"));
    }

    let ptr = match &args[0] {
        Value::Array(bytes) => {
            if bytes.is_empty() {
                return Ok(Value::Int(0));
            }
            bytes.as_ptr() as *mut u8
        }
        _ => return Err(CompileError::runtime("arc_box_dec_weak: argument must be byte array")),
    };

    unsafe {
        let weak_ptr = ptr.add(size_of::<AtomicUsize>()) as *const AtomicUsize;
        let prev = (*weak_ptr).fetch_sub(1, Ordering::Release);
        Ok(Value::Int((prev - 1) as i64))
    }
}
