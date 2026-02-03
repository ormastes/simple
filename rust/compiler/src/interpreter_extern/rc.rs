//! RC/ARC FFI wrappers for Simple language
//!
//! Provides reference counting operations for Rc<T> and Arc<T>.
//! Uses raw pointers where Simple manages allocation with sys_malloc/sys_free.
//!
//! Memory layout:
//! ```
//! RcBox<T> / ArcBox<T>:
//! ┌────────────────────────────────┐
//! │ strong_count: usize/AtomicUsize │
//! ├────────────────────────────────┤
//! │ weak_count: usize/AtomicUsize   │
//! ├────────────────────────────────┤
//! │ value: T (Value enum)           │
//! └────────────────────────────────┘
//! ```
//!
//! Simple code calls sys_malloc() to allocate memory (returns Int pointer),
//! then calls rc_box_init() to initialize the box with counts and value.

use crate::error::CompileError;
use crate::value::Value;
use std::mem::size_of;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::ptr;

// ============================================================================
// Helper Functions
// ============================================================================

/// Extract raw pointer from Value (Int or Array)
fn get_ptr(val: &Value, func_name: &str) -> Result<*mut u8, CompileError> {
    match val {
        Value::Int(addr) => {
            if *addr == 0 {
                return Err(CompileError::runtime(&format!("{}: ptr is null", func_name)));
            }
            Ok(*addr as *mut u8)
        }
        Value::Array(bytes) => {
            if bytes.is_empty() {
                return Err(CompileError::runtime(&format!("{}: ptr is null", func_name)));
            }
            Ok(bytes.as_ptr() as *mut u8)
        }
        _ => Err(CompileError::runtime(&format!("{}: ptr must be Int or Array", func_name))),
    }
}

/// Extract raw pointer, allowing null
fn get_ptr_nullable(val: &Value) -> *mut u8 {
    match val {
        Value::Int(addr) => *addr as *mut u8,
        Value::Array(bytes) if !bytes.is_empty() => bytes.as_ptr() as *mut u8,
        _ => std::ptr::null_mut(),
    }
}

// ============================================================================
// Rc Box Operations (Non-Atomic)
// ============================================================================

/// Get size of RcBox<T> for allocation
///
/// Returns: size_of(usize) * 2 + size_of(Value)
pub fn rc_box_size(_args: &[Value]) -> Result<Value, CompileError> {
    // RcBox header: strong_count + weak_count + Value
    let total = size_of::<usize>() * 2 + size_of::<Value>();
    Ok(Value::Int(total as i64))
}

/// Initialize RcBox with value and counts
///
/// Args: (ptr: Int, value: T, strong: Int, weak: Int)
pub fn rc_box_init(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 4 {
        return Err(CompileError::runtime("rc_box_init requires 4 arguments (ptr, value, strong, weak)"));
    }

    let ptr = get_ptr(&args[0], "rc_box_init")?;
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
/// Args: (ptr: Int)
/// Returns: T (cloned)
pub fn rc_box_get_value(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime("rc_box_get_value requires 1 argument (ptr)"));
    }

    let ptr = get_ptr(&args[0], "rc_box_get_value")?;

    unsafe {
        // Read value at offset sizeof(usize) * 2
        let value_ptr = ptr.add(size_of::<usize>() * 2) as *const Value;
        Ok((*value_ptr).clone())
    }
}

/// Drop value in RcBox (run destructor)
///
/// Args: (ptr: Int)
pub fn rc_box_drop_value(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime("rc_box_drop_value requires 1 argument (ptr)"));
    }

    let ptr = get_ptr(&args[0], "rc_box_drop_value")?;

    unsafe {
        // Drop value at offset sizeof(usize) * 2
        let value_ptr = ptr.add(size_of::<usize>() * 2) as *mut Value;
        ptr::drop_in_place(value_ptr);
    }

    Ok(Value::Nil)
}

/// Get strong reference count
///
/// Args: (ptr: Int)
/// Returns: usize (strong count)
pub fn rc_box_strong_count(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime("rc_box_strong_count requires 1 argument (ptr)"));
    }

    let ptr = get_ptr_nullable(&args[0]);
    if ptr.is_null() {
        return Ok(Value::Int(0));
    }

    unsafe {
        let strong_ptr = ptr as *const usize;
        Ok(Value::Int(*strong_ptr as i64))
    }
}

/// Get weak reference count
///
/// Args: (ptr: Int)
/// Returns: usize (weak count)
pub fn rc_box_weak_count(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime("rc_box_weak_count requires 1 argument (ptr)"));
    }

    let ptr = get_ptr_nullable(&args[0]);
    if ptr.is_null() {
        return Ok(Value::Int(0));
    }

    unsafe {
        let weak_ptr = ptr.add(size_of::<usize>()) as *const usize;
        Ok(Value::Int(*weak_ptr as i64))
    }
}

/// Increment strong reference count
///
/// Args: (ptr: Int)
pub fn rc_box_inc_strong(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime("rc_box_inc_strong requires 1 argument (ptr)"));
    }

    let ptr = get_ptr(&args[0], "rc_box_inc_strong")?;

    unsafe {
        let strong_ptr = ptr as *mut usize;
        *strong_ptr += 1;
    }

    Ok(Value::Nil)
}

/// Decrement strong reference count
///
/// Args: (ptr: Int)
/// Returns: usize (count after decrement)
pub fn rc_box_dec_strong(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime("rc_box_dec_strong requires 1 argument (ptr)"));
    }

    let ptr = get_ptr_nullable(&args[0]);
    if ptr.is_null() {
        return Ok(Value::Int(0));
    }

    unsafe {
        let strong_ptr = ptr as *mut usize;
        *strong_ptr -= 1;
        Ok(Value::Int(*strong_ptr as i64))
    }
}

/// Increment weak reference count
///
/// Args: (ptr: Int)
pub fn rc_box_inc_weak(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime("rc_box_inc_weak requires 1 argument (ptr)"));
    }

    let ptr = get_ptr(&args[0], "rc_box_inc_weak")?;

    unsafe {
        let weak_ptr = ptr.add(size_of::<usize>()) as *mut usize;
        *weak_ptr += 1;
    }

    Ok(Value::Nil)
}

/// Decrement weak reference count
///
/// Args: (ptr: Int)
/// Returns: usize (count after decrement)
pub fn rc_box_dec_weak(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime("rc_box_dec_weak requires 1 argument (ptr)"));
    }

    let ptr = get_ptr_nullable(&args[0]);
    if ptr.is_null() {
        return Ok(Value::Int(0));
    }

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
/// Returns: size_of(AtomicUsize) * 2 + size_of(Value)
pub fn arc_box_size(_args: &[Value]) -> Result<Value, CompileError> {
    // ArcBox header: AtomicUsize strong + AtomicUsize weak + Value
    // AtomicUsize has same size as usize
    let total = size_of::<AtomicUsize>() * 2 + size_of::<Value>();
    Ok(Value::Int(total as i64))
}

/// Initialize ArcBox with value and counts (atomic)
///
/// Args: (ptr: Int, value: T, strong: Int, weak: Int)
pub fn arc_box_init(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 4 {
        return Err(CompileError::runtime("arc_box_init requires 4 arguments (ptr, value, strong, weak)"));
    }

    let ptr = get_ptr(&args[0], "arc_box_init")?;
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
/// Args: (ptr: Int)
/// Returns: T (cloned)
pub fn arc_box_get_value(args: &[Value]) -> Result<Value, CompileError> {
    // Value access doesn't need atomics
    rc_box_get_value(args)
}

/// Drop value in ArcBox (run destructor)
///
/// Args: (ptr: Int)
pub fn arc_box_drop_value(args: &[Value]) -> Result<Value, CompileError> {
    // Drop doesn't need atomics
    rc_box_drop_value(args)
}

/// Get strong reference count (atomic load)
///
/// Args: (ptr: Int)
/// Returns: usize (strong count)
pub fn arc_box_strong_count(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime("arc_box_strong_count requires 1 argument (ptr)"));
    }

    let ptr = get_ptr_nullable(&args[0]);
    if ptr.is_null() {
        return Ok(Value::Int(0));
    }

    unsafe {
        let strong_ptr = ptr as *const AtomicUsize;
        let count = (*strong_ptr).load(Ordering::Acquire);
        Ok(Value::Int(count as i64))
    }
}

/// Get weak reference count (atomic load)
///
/// Args: (ptr: Int)
/// Returns: usize (weak count)
pub fn arc_box_weak_count(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime("arc_box_weak_count requires 1 argument (ptr)"));
    }

    let ptr = get_ptr_nullable(&args[0]);
    if ptr.is_null() {
        return Ok(Value::Int(0));
    }

    unsafe {
        let weak_ptr = ptr.add(size_of::<AtomicUsize>()) as *const AtomicUsize;
        let count = (*weak_ptr).load(Ordering::Acquire);
        Ok(Value::Int(count as i64))
    }
}

/// Increment strong reference count (atomic)
///
/// Args: (ptr: Int)
pub fn arc_box_inc_strong(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime("arc_box_inc_strong requires 1 argument (ptr)"));
    }

    let ptr = get_ptr(&args[0], "arc_box_inc_strong")?;

    unsafe {
        let strong_ptr = ptr as *const AtomicUsize;
        (*strong_ptr).fetch_add(1, Ordering::Release);
    }

    Ok(Value::Nil)
}

/// Decrement strong reference count (atomic)
///
/// Args: (ptr: Int)
/// Returns: usize (count after decrement)
pub fn arc_box_dec_strong(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime("arc_box_dec_strong requires 1 argument (ptr)"));
    }

    let ptr = get_ptr_nullable(&args[0]);
    if ptr.is_null() {
        return Ok(Value::Int(0));
    }

    unsafe {
        let strong_ptr = ptr as *const AtomicUsize;
        let prev = (*strong_ptr).fetch_sub(1, Ordering::Release);
        Ok(Value::Int((prev - 1) as i64))
    }
}

/// Increment weak reference count (atomic)
///
/// Args: (ptr: Int)
pub fn arc_box_inc_weak(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime("arc_box_inc_weak requires 1 argument (ptr)"));
    }

    let ptr = get_ptr(&args[0], "arc_box_inc_weak")?;

    unsafe {
        let weak_ptr = ptr.add(size_of::<AtomicUsize>()) as *const AtomicUsize;
        (*weak_ptr).fetch_add(1, Ordering::Release);
    }

    Ok(Value::Nil)
}

/// Decrement weak reference count (atomic)
///
/// Args: (ptr: Int)
/// Returns: usize (count after decrement)
pub fn arc_box_dec_weak(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime("arc_box_dec_weak requires 1 argument (ptr)"));
    }

    let ptr = get_ptr_nullable(&args[0]);
    if ptr.is_null() {
        return Ok(Value::Int(0));
    }

    unsafe {
        let weak_ptr = ptr.add(size_of::<AtomicUsize>()) as *const AtomicUsize;
        let prev = (*weak_ptr).fetch_sub(1, Ordering::Release);
        Ok(Value::Int((prev - 1) as i64))
    }
}
