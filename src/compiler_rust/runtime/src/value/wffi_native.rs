//! Native implementations of spl_dlopen/spl_dlsym/spl_dlclose/spl_wffi_call_i64.
//!
//! These accept tagged RuntimeValues (as Cranelift/LLVM passes them) and decode
//! text arguments to raw C strings before calling libc. This bridges the gap
//! between the Simple extern fn declarations and the C ABI.

use super::core::RuntimeValue;
use super::collections::{rt_string_data, rt_string_len, rt_array_get};

/// spl_dlopen(path: text) -> i64
///
/// Decodes the tagged text RuntimeValue to a raw C string, calls dlopen.
/// Returns the handle as a raw i64 (not tagged).
#[no_mangle]
pub extern "C" fn spl_dlopen(path_rv: RuntimeValue) -> i64 {
    let raw_ptr = rt_string_data(path_rv);
    if raw_ptr.is_null() {
        return 0;
    }

    // rt_string_data returns a pointer to the string bytes (not necessarily
    // null-terminated). We need a null-terminated C string for dlopen.
    let len = rt_string_len(path_rv);
    if len < 0 {
        return 0;
    }

    // Build a null-terminated copy
    let slice = unsafe { std::slice::from_raw_parts(raw_ptr, len as usize) };
    let mut buf = Vec::with_capacity(len as usize + 1);
    buf.extend_from_slice(slice);
    buf.push(0); // null terminator

    let handle = unsafe { libc::dlopen(buf.as_ptr() as *const libc::c_char, libc::RTLD_NOW) };
    handle as i64
}

/// spl_dlsym(handle: i64, name: text) -> i64
///
/// `handle` is a raw pointer-as-i64 returned by spl_dlopen.
/// `name_rv` is a tagged RuntimeValue text.
/// Returns the symbol address as a raw i64.
#[no_mangle]
pub extern "C" fn spl_dlsym(handle: i64, name_rv: RuntimeValue) -> i64 {
    let raw_ptr = rt_string_data(name_rv);
    if raw_ptr.is_null() || handle == 0 {
        return 0;
    }

    let len = rt_string_len(name_rv);
    if len < 0 {
        return 0;
    }

    // Build a null-terminated copy
    let slice = unsafe { std::slice::from_raw_parts(raw_ptr, len as usize) };
    let mut buf = Vec::with_capacity(len as usize + 1);
    buf.extend_from_slice(slice);
    buf.push(0);

    let result = unsafe { libc::dlsym(handle as *mut libc::c_void, buf.as_ptr() as *const libc::c_char) };
    result as i64
}

/// spl_dlclose(handle: i64) -> i64
///
/// Closes a dynamic library handle. Returns 0 on success, non-zero on error.
#[no_mangle]
pub extern "C" fn spl_dlclose(handle: i64) -> i64 {
    if handle == 0 {
        return 0;
    }
    let result = unsafe { libc::dlclose(handle as *mut libc::c_void) };
    result as i64
}

/// spl_wffi_call_i64(fptr: i64, args: RuntimeValue_array, nargs: i64) -> i64
///
/// `fptr` is a raw function pointer (not tagged).
/// `args_rv` is a tagged RuntimeValue representing an Array of i64 values.
/// `nargs` is the argument count.
///
/// Each element in the array is a RuntimeValue whose raw `.0` field is the
/// i64 value to pass (since Simple pushes raw i64s into the array).
#[no_mangle]
pub extern "C" fn spl_wffi_call_i64(fptr: i64, args_rv: RuntimeValue, nargs: i64) -> i64 {
    if fptr == 0 {
        return 0;
    }

    let n = nargs as usize;
    let mut raw_args: [i64; 8] = [0; 8];
    for i in 0..n.min(8) {
        let val = rt_array_get(args_rv, i as i64);
        // The array elements are RuntimeValues containing the raw i64 values.
        // Extract the underlying u64 and reinterpret as i64.
        raw_args[i] = val.0 as i64;
    }

    type Fn0 = unsafe extern "C" fn() -> i64;
    type Fn1 = unsafe extern "C" fn(i64) -> i64;
    type Fn2 = unsafe extern "C" fn(i64, i64) -> i64;
    type Fn3 = unsafe extern "C" fn(i64, i64, i64) -> i64;
    type Fn4 = unsafe extern "C" fn(i64, i64, i64, i64) -> i64;
    type Fn5 = unsafe extern "C" fn(i64, i64, i64, i64, i64) -> i64;
    type Fn6 = unsafe extern "C" fn(i64, i64, i64, i64, i64, i64) -> i64;
    type Fn7 = unsafe extern "C" fn(i64, i64, i64, i64, i64, i64, i64) -> i64;
    type Fn8 = unsafe extern "C" fn(i64, i64, i64, i64, i64, i64, i64, i64) -> i64;

    unsafe {
        match n {
            0 => std::mem::transmute::<usize, Fn0>(fptr as usize)(),
            1 => std::mem::transmute::<usize, Fn1>(fptr as usize)(raw_args[0]),
            2 => std::mem::transmute::<usize, Fn2>(fptr as usize)(raw_args[0], raw_args[1]),
            3 => std::mem::transmute::<usize, Fn3>(fptr as usize)(raw_args[0], raw_args[1], raw_args[2]),
            4 => std::mem::transmute::<usize, Fn4>(fptr as usize)(raw_args[0], raw_args[1], raw_args[2], raw_args[3]),
            5 => std::mem::transmute::<usize, Fn5>(fptr as usize)(
                raw_args[0],
                raw_args[1],
                raw_args[2],
                raw_args[3],
                raw_args[4],
            ),
            6 => std::mem::transmute::<usize, Fn6>(fptr as usize)(
                raw_args[0],
                raw_args[1],
                raw_args[2],
                raw_args[3],
                raw_args[4],
                raw_args[5],
            ),
            7 => std::mem::transmute::<usize, Fn7>(fptr as usize)(
                raw_args[0],
                raw_args[1],
                raw_args[2],
                raw_args[3],
                raw_args[4],
                raw_args[5],
                raw_args[6],
            ),
            8 => std::mem::transmute::<usize, Fn8>(fptr as usize)(
                raw_args[0],
                raw_args[1],
                raw_args[2],
                raw_args[3],
                raw_args[4],
                raw_args[5],
                raw_args[6],
                raw_args[7],
            ),
            _ => 0,
        }
    }
}
