//! Native implementations of spl_dlopen/spl_dlsym/spl_dlclose/spl_wffi_call_i64
//! and spl_wffi_call_f64.
//!
//! These accept tagged RuntimeValues (as Cranelift/LLVM passes them) and decode
//! text arguments to raw C strings before calling libc. This bridges the gap
//! between the Simple extern fn declarations and the C ABI.

use super::core::RuntimeValue;
use super::collections::{byte_array_bytes, rt_array_get, rt_array_len, rt_string_data, rt_string_len};

fn raw_text_cstring(ptr: *const u8, len: i64) -> Option<std::ffi::CString> {
    if ptr.is_null() || len <= 0 || len > 1024 * 1024 {
        return None;
    }
    let bytes = unsafe { std::slice::from_raw_parts(ptr, len as usize) };
    std::ffi::CString::new(bytes).ok()
}

#[no_mangle]
pub extern "C" fn rt_host_dynlib_open(path_ptr: *const u8, path_len: i64, mode: i64) -> i64 {
    let Some(path) = raw_text_cstring(path_ptr, path_len) else {
        return 0;
    };
    #[cfg(unix)]
    unsafe {
        let flags = if mode & 2 != 0 { libc::RTLD_NOW } else { libc::RTLD_LAZY } | libc::RTLD_LOCAL;
        libc::dlopen(path.as_ptr(), flags) as i64
    }
    #[cfg(windows)]
    unsafe {
        use windows_sys::Win32::System::LibraryLoader::LoadLibraryA;
        LoadLibraryA(path.as_ptr() as *const u8) as i64
    }
}

#[no_mangle]
pub extern "C" fn rt_host_dynlib_symbol(handle: i64, name_ptr: *const u8, name_len: i64) -> i64 {
    if handle <= 0 {
        return 0;
    }
    let Some(name) = raw_text_cstring(name_ptr, name_len) else {
        return 0;
    };
    #[cfg(unix)]
    unsafe {
        libc::dlsym(handle as *mut libc::c_void, name.as_ptr()) as i64
    }
    #[cfg(windows)]
    unsafe {
        use windows_sys::Win32::System::LibraryLoader::GetProcAddress;
        GetProcAddress(handle as _, name.as_ptr() as *const u8)
            .map(|symbol| symbol as *const () as i64)
            .unwrap_or(0)
    }
}

#[no_mangle]
pub extern "C" fn rt_host_dynlib_close(handle: i64) -> i64 {
    if handle <= 0 {
        return -1;
    }
    #[cfg(unix)]
    unsafe {
        libc::dlclose(handle as *mut libc::c_void) as i64
    }
    #[cfg(windows)]
    unsafe {
        use windows_sys::Win32::Foundation::FreeLibrary;
        if FreeLibrary(handle as _) != 0 {
            0
        } else {
            -1
        }
    }
}

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

    #[cfg(unix)]
    {
        let handle = unsafe { libc::dlopen(buf.as_ptr() as *const libc::c_char, libc::RTLD_NOW) };
        handle as i64
    }
    #[cfg(windows)]
    {
        use windows_sys::Win32::System::LibraryLoader::LoadLibraryA;
        unsafe { LoadLibraryA(buf.as_ptr()) as i64 }
    }
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

    #[cfg(unix)]
    {
        let result = unsafe { libc::dlsym(handle as *mut libc::c_void, buf.as_ptr() as *const libc::c_char) };
        result as i64
    }
    #[cfg(windows)]
    {
        use windows_sys::Win32::System::LibraryLoader::GetProcAddress;
        unsafe { GetProcAddress(handle as _, buf.as_ptr()) }
            .map(|symbol| symbol as *const () as i64)
            .unwrap_or(0)
    }
}

/// spl_dlclose(handle: i64) -> i64
///
/// Closes a dynamic library handle. Returns 0 on success, non-zero on error.
#[no_mangle]
pub extern "C" fn spl_dlclose(handle: i64) -> i64 {
    if handle == 0 {
        return 0;
    }
    #[cfg(unix)]
    {
        let result = unsafe { libc::dlclose(handle as *mut libc::c_void) };
        result as i64
    }
    #[cfg(windows)]
    {
        use windows_sys::Win32::Foundation::FreeLibrary;
        if unsafe { FreeLibrary(handle as _) } != 0 {
            0
        } else {
            -1
        }
    }
}

/// spl_wffi_call_i64(fptr: i64, args: RuntimeValue_array, nargs: i64) -> i64
///
/// `fptr` is a raw function pointer (not tagged).
/// `args_rv` is a tagged RuntimeValue representing an Array of i64 values.
/// `nargs` is the argument count.
///
/// Each element in the array is a tagged Simple integer. Decode it before
/// crossing the C ABI; forwarding `.0` would shift every argument left by the
/// integer tag width.
#[no_mangle]
pub extern "C" fn spl_wffi_call_i64(fptr: i64, args_rv: RuntimeValue, nargs: i64) -> i64 {
    if fptr == 0 {
        return 0;
    }

    let n = nargs as usize;
    let mut raw_args: [i64; 8] = [0; 8];
    for (i, slot) in raw_args.iter_mut().enumerate().take(n.min(8)) {
        let val = rt_array_get(args_rv, i as i64);
        *slot = val.as_int();
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

unsafe fn call_i64_raw(fptr: i64, args: &[i64]) -> i64 {
    type Fn0 = unsafe extern "C" fn() -> i64;
    type Fn1 = unsafe extern "C" fn(i64) -> i64;
    type Fn2 = unsafe extern "C" fn(i64, i64) -> i64;
    type Fn3 = unsafe extern "C" fn(i64, i64, i64) -> i64;
    type Fn4 = unsafe extern "C" fn(i64, i64, i64, i64) -> i64;
    type Fn5 = unsafe extern "C" fn(i64, i64, i64, i64, i64) -> i64;
    type Fn6 = unsafe extern "C" fn(i64, i64, i64, i64, i64, i64) -> i64;
    type Fn7 = unsafe extern "C" fn(i64, i64, i64, i64, i64, i64, i64) -> i64;
    type Fn8 = unsafe extern "C" fn(i64, i64, i64, i64, i64, i64, i64, i64) -> i64;
    match args {
        [] => std::mem::transmute::<usize, Fn0>(fptr as usize)(),
        [a] => std::mem::transmute::<usize, Fn1>(fptr as usize)(*a),
        [a, b] => std::mem::transmute::<usize, Fn2>(fptr as usize)(*a, *b),
        [a, b, c] => std::mem::transmute::<usize, Fn3>(fptr as usize)(*a, *b, *c),
        [a, b, c, d] => std::mem::transmute::<usize, Fn4>(fptr as usize)(*a, *b, *c, *d),
        [a, b, c, d, e] => std::mem::transmute::<usize, Fn5>(fptr as usize)(*a, *b, *c, *d, *e),
        [a, b, c, d, e, f] => std::mem::transmute::<usize, Fn6>(fptr as usize)(*a, *b, *c, *d, *e, *f),
        [a, b, c, d, e, f, g] => std::mem::transmute::<usize, Fn7>(fptr as usize)(*a, *b, *c, *d, *e, *f, *g),
        [a, b, c, d, e, f, g, h] => {
            std::mem::transmute::<usize, Fn8>(fptr as usize)(*a, *b, *c, *d, *e, *f, *g, *h)
        }
        _ => 0,
    }
}

fn runtime_i64_values(value: RuntimeValue) -> Option<Vec<i64>> {
    let len = usize::try_from(rt_array_len(value)).ok()?;
    if len > 6 {
        return None;
    }
    Some((0..len).map(|index| rt_array_get(value, index as i64).as_int()).collect())
}

/// One-call dynamic dispatch with a byte descriptor inserted between scalar
/// prefix and suffix arguments. The byte address exists only in this frame.
#[no_mangle]
pub extern "C" fn spl_wffi_call_i64_with_bytes(
    fptr: i64,
    prefix_args: RuntimeValue,
    bytes: RuntimeValue,
    offset: i64,
    length: i64,
    suffix_args: RuntimeValue,
) -> i64 {
    if fptr == 0 {
        return 0;
    }
    let Some(owner) = byte_array_bytes(bytes) else {
        return 0;
    };
    let (Ok(offset), Ok(length)) = (usize::try_from(offset), usize::try_from(length)) else {
        return 0;
    };
    let Some(end) = offset.checked_add(length) else {
        return 0;
    };
    if end > owner.len() {
        return 0;
    }
    let (Some(mut args), Some(suffix)) = (runtime_i64_values(prefix_args), runtime_i64_values(suffix_args)) else {
        return 0;
    };
    if args.len() + 2 + suffix.len() > 8 {
        return 0;
    }
    let ptr = if length == 0 { 0 } else { owner[offset..end].as_ptr() as i64 };
    args.push(ptr);
    args.push(length as i64);
    args.extend_from_slice(&suffix);
    unsafe { call_i64_raw(fptr, &args) }
}

#[no_mangle]
pub extern "C" fn spl_fonts_call_init_blob(fptr: i64, blob: RuntimeValue, digest: RuntimeValue) -> i64 {
    if fptr == 0 {
        return 0;
    }
    let (Some(blob), Some(digest)) = (byte_array_bytes(blob), byte_array_bytes(digest)) else {
        return 0;
    };
    let args = [blob.as_ptr() as i64, blob.len() as i64, digest.as_ptr() as i64, digest.len() as i64];
    unsafe { call_i64_raw(fptr, &args) }
}

#[no_mangle]
pub extern "C" fn spl_fonts_call_init_path(fptr: i64, path: RuntimeValue) -> i64 {
    if fptr == 0 {
        return 0;
    }
    let Some(path) = byte_array_bytes(path) else {
        return 0;
    };
    let args = [path.as_ptr() as i64, path.len() as i64];
    unsafe { call_i64_raw(fptr, &args) }
}

#[no_mangle]
pub extern "C" fn spl_fonts_call_layout_text(
    fptr: i64,
    text: RuntimeValue,
    size_px: i64,
    max_width: i64,
) -> i64 {
    if fptr == 0 {
        return 0;
    }
    let Some(text) = byte_array_bytes(text) else {
        return 0;
    };
    let args = [text.as_ptr() as i64, text.len() as i64, size_px, max_width];
    unsafe { call_i64_raw(fptr, &args) }
}

/// spl_wffi_call_f64(fptr: i64, args: RuntimeValue_array, nargs: i64) -> f64
#[no_mangle]
pub extern "C" fn spl_wffi_call_f64(fptr: i64, args_rv: RuntimeValue, nargs: i64) -> f64 {
    if fptr == 0 {
        return 0.0;
    }

    let n = nargs as usize;
    let mut raw_args: [f64; 8] = [0.0; 8];
    for (i, slot) in raw_args.iter_mut().enumerate().take(n.min(8)) {
        let val = rt_array_get(args_rv, i as i64);
        *slot = runtime_value_to_f64(val);
    }

    type Fn0 = unsafe extern "C" fn() -> f64;
    type Fn1 = unsafe extern "C" fn(f64) -> f64;
    type Fn2 = unsafe extern "C" fn(f64, f64) -> f64;
    type Fn3 = unsafe extern "C" fn(f64, f64, f64) -> f64;
    type Fn4 = unsafe extern "C" fn(f64, f64, f64, f64) -> f64;
    type Fn5 = unsafe extern "C" fn(f64, f64, f64, f64, f64) -> f64;
    type Fn6 = unsafe extern "C" fn(f64, f64, f64, f64, f64, f64) -> f64;
    type Fn7 = unsafe extern "C" fn(f64, f64, f64, f64, f64, f64, f64) -> f64;
    type Fn8 = unsafe extern "C" fn(f64, f64, f64, f64, f64, f64, f64, f64) -> f64;

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
            _ => 0.0,
        }
    }
}

fn runtime_value_to_f64(value: RuntimeValue) -> f64 {
    if value.is_float() {
        return value.as_float();
    }
    if value.0 & 0x7 == 0 {
        return value.as_int() as f64;
    }
    0.0
}

/// spl_str_ptr(s: text) -> i64
///
/// Decodes a tagged text RuntimeValue to a NUL-terminated C-string pointer for
/// Simple code that hands raw pointers to dynamically loaded C functions
/// (GuiRenderer window titles, TRACE32 ctypes bridge). The pointer aliases a
/// thread-local buffer valid until the next spl_str_ptr call on the same
/// thread — callers pass it straight into the C call. Non-text values pass
/// through unchanged, matching the runtime_native.c provider.
#[no_mangle]
pub extern "C" fn spl_str_ptr(value_rv: RuntimeValue) -> i64 {
    let raw_ptr = rt_string_data(value_rv);
    if raw_ptr.is_null() {
        return value_rv.0 as i64;
    }
    let len = rt_string_len(value_rv);
    if len < 0 {
        return value_rv.0 as i64;
    }
    thread_local! {
        static STR_PTR_BUF: std::cell::RefCell<Vec<u8>> = const { std::cell::RefCell::new(Vec::new()) };
    }
    STR_PTR_BUF.with(|buf| {
        let mut buf = buf.borrow_mut();
        buf.clear();
        buf.extend_from_slice(unsafe { std::slice::from_raw_parts(raw_ptr, len as usize) });
        buf.push(0);
        buf.as_ptr() as i64
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::super::collections::{rt_array_new, rt_array_push};

    unsafe extern "C" fn i64_two_args(a: i64, b: i64) -> i64 {
        a + b
    }

    #[test]
    fn spl_wffi_call_i64_decodes_tagged_integer_arguments() {
        let args = rt_array_new(2);
        assert!(rt_array_push(args, RuntimeValue::from_int(0x24c_7468)));
        assert!(rt_array_push(args, RuntimeValue::from_int(7)));

        let result = spl_wffi_call_i64(i64_two_args as usize as i64, args, 2);

        assert_eq!(result, 0x24c_746f);
    }

    unsafe extern "C" fn f64_no_args() -> f64 {
        6.25
    }

    #[test]
    fn spl_wffi_call_f64_invokes_no_arg_function_pointer() {
        let result = spl_wffi_call_f64(f64_no_args as usize as i64, RuntimeValue::NIL, 0);
        assert_eq!(result, 6.25);
    }
}
