//! Native implementations of spl_dlopen/spl_dlsym/spl_dlclose/spl_wffi_call_i64
//! and spl_wffi_call_f64.
//!
//! These accept tagged RuntimeValues (as Cranelift/LLVM passes them) and decode
//! text arguments to raw C strings before calling libc. This bridges the gap
//! between the Simple extern fn declarations and the C ABI.

use super::core::RuntimeValue;
use super::collections::{byte_array_bytes, rt_array_get, rt_array_len, rt_string_data, rt_string_len};

const WFFI_OK: i64 = 0;
const WFFI_INVALID_ARGUMENT: i64 = 1;
const WFFI_NULL_FUNCTION: i64 = 2;
const WFFI_UNSUPPORTED_SIGNATURE: i64 = 3;
const WFFI_INVALID_OUTPUT: i64 = 4;

fn store_i64_output(out: RuntimeValue, value: i64) -> bool {
    if rt_array_len(out) < 1 {
        return false;
    }
    super::collections::rt_array_set(out, 0, RuntimeValue::from_int(value))
}

fn checked_i64_result(status: i64, value: i64) -> RuntimeValue {
    let result = super::collections::rt_array_new(2);
    if result.is_nil() {
        return RuntimeValue::NIL;
    }
    if !super::collections::rt_array_push(result, RuntimeValue::from_int(status))
        || !super::collections::rt_array_push(result, RuntimeValue::from_int(value))
    {
        return RuntimeValue::NIL;
    }
    result
}

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

/// Copy a provider into a sealed Linux memfd. Returns -1 on failure.
#[no_mangle]
pub extern "C" fn spl_dynlib_snapshot_linux(path_rv: RuntimeValue) -> i64 {
    #[cfg(target_os = "linux")]
    unsafe {
        let raw_ptr = rt_string_data(path_rv);
        let len = rt_string_len(path_rv);
        if raw_ptr.is_null() || len <= 0 || len > 1024 * 1024 {
            return -1;
        }
        let path = match std::ffi::CString::new(std::slice::from_raw_parts(raw_ptr, len as usize)) {
            Ok(path) => path,
            Err(_) => return -1,
        };
        let source = libc::open(
            path.as_ptr(),
            libc::O_RDONLY | libc::O_CLOEXEC | libc::O_NOFOLLOW | libc::O_NONBLOCK,
        );
        if source < 0 { return -1; }
        let mut source_stat = std::mem::MaybeUninit::<libc::stat>::uninit();
        if libc::fstat(source, source_stat.as_mut_ptr()) != 0 {
            libc::close(source);
            return -1;
        }
        let source_stat = source_stat.assume_init();
        if source_stat.st_mode & libc::S_IFMT != libc::S_IFREG
            || source_stat.st_size < 0
            || source_stat.st_size as u64 > 1_073_741_824
        {
            libc::close(source);
            return -1;
        }
        let name = b"simple-sffi-provider\0";
        let snapshot = libc::syscall(
            libc::SYS_memfd_create,
            name.as_ptr() as *const libc::c_char,
            libc::MFD_CLOEXEC | libc::MFD_ALLOW_SEALING,
        ) as libc::c_int;
        if snapshot < 0 {
            libc::close(source);
            return -1;
        }
        let mut buffer = [0u8; 65536];
        let mut total = 0u64;
        loop {
            let got = libc::read(source, buffer.as_mut_ptr().cast(), buffer.len());
            if got == 0 { break; }
            if got < 0 {
                if std::io::Error::last_os_error().kind() == std::io::ErrorKind::Interrupted { continue; }
                libc::close(source); libc::close(snapshot);
                return -1;
            }
            if got as u64 > 1_073_741_824 - total {
                libc::close(source); libc::close(snapshot);
                return -1;
            }
            total += got as u64;
            let mut offset = 0isize;
            while offset < got {
                let put = libc::write(
                    snapshot,
                    buffer.as_ptr().offset(offset).cast(),
                    (got - offset) as usize,
                );
                if put < 0 && std::io::Error::last_os_error().kind() == std::io::ErrorKind::Interrupted {
                    continue;
                }
                if put <= 0 {
                    libc::close(source); libc::close(snapshot);
                    return -1;
                }
                offset += put;
            }
        }
        let seals = libc::F_SEAL_WRITE | libc::F_SEAL_GROW | libc::F_SEAL_SHRINK | libc::F_SEAL_SEAL;
        if total != source_stat.st_size as u64
            || libc::close(source) != 0
            || libc::lseek(snapshot, 0, libc::SEEK_SET) < 0
            || libc::fcntl(snapshot, libc::F_ADD_SEALS, seals) != 0
        {
            libc::close(snapshot);
            return -1;
        }
        snapshot as i64
    }

    #[cfg(not(target_os = "linux"))]
    {
        let _ = path_rv;
        -1
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
        // This ABI is status-valued: zero means that a library was closed.
        // A null handle closes nothing, so returning success would fabricate
        // an operation result and hide an invalid-handle defect.
        return -1;
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
    try_call_i64_value(fptr, args_rv, nargs).unwrap_or(0)
}

/// Checked integer WFFI transport.
///
/// Returns a bridge status and writes the foreign result to `out[0]` only on
/// success. This keeps a legitimate foreign zero distinct from a bridge error.
#[no_mangle]
pub extern "C" fn spl_wffi_try_call_i64(fptr: i64, args_rv: RuntimeValue, nargs: i64, out: RuntimeValue) -> i64 {
    let result = match try_call_i64_value(fptr, args_rv, nargs) {
        Ok(result) => result,
        Err(status) => return status,
    };
    if store_i64_output(out, result) {
        WFFI_OK
    } else {
        WFFI_INVALID_OUTPUT
    }
}

#[inline]
fn try_call_i64_value(fptr: i64, args_rv: RuntimeValue, nargs: i64) -> Result<i64, i64> {
    if fptr == 0 {
        return Err(WFFI_NULL_FUNCTION);
    }
    let Ok(n) = usize::try_from(nargs) else {
        return Err(WFFI_INVALID_ARGUMENT);
    };
    let Ok(available) = usize::try_from(rt_array_len(args_rv)) else {
        return Err(WFFI_INVALID_ARGUMENT);
    };
    if n > 8 {
        return Err(WFFI_UNSUPPORTED_SIGNATURE);
    }
    if n > available {
        return Err(WFFI_INVALID_ARGUMENT);
    }

    let mut raw_args: [i64; 8] = [0; 8];
    for (i, slot) in raw_args.iter_mut().enumerate().take(n) {
        let val = rt_array_get(args_rv, i as i64);
        if !val.is_int() {
            return Err(WFFI_INVALID_ARGUMENT);
        }
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

    Ok(unsafe {
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
            _ => unreachable!("argument count validated above"),
        }
    })
}

/// Interpreter/native-equivalent checked transport returning `[status, value]`.
/// The value slot is meaningful only when status is `WFFI_OK`.
#[no_mangle]
pub extern "C" fn spl_wffi_call_i64_checked(fptr: i64, args_rv: RuntimeValue, nargs: i64) -> RuntimeValue {
    match try_call_i64_value(fptr, args_rv, nargs) {
        Ok(value) => checked_i64_result(WFFI_OK, value),
        Err(status) => checked_i64_result(status, 0),
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
        [a, b, c, d, e, f, g, h] => std::mem::transmute::<usize, Fn8>(fptr as usize)(*a, *b, *c, *d, *e, *f, *g, *h),
        _ => 0,
    }
}

fn runtime_i64_values(value: RuntimeValue) -> Option<Vec<i64>> {
    let len = usize::try_from(rt_array_len(value)).ok()?;
    if len > 6 {
        return None;
    }
    Some(
        (0..len)
            .map(|index| rt_array_get(value, index as i64).as_int())
            .collect(),
    )
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
    let checked = spl_wffi_call_i64_with_bytes_checked(fptr, prefix_args, bytes, offset, length, suffix_args);
    if checked.is_nil() || rt_array_get(checked, 0).as_int() != WFFI_OK {
        return 0;
    }
    rt_array_get(checked, 1).as_int()
}

/// Checked byte-descriptor dispatch returning `[status, value]`.
#[no_mangle]
pub extern "C" fn spl_wffi_call_i64_with_bytes_checked(
    fptr: i64,
    prefix_args: RuntimeValue,
    bytes: RuntimeValue,
    offset: i64,
    length: i64,
    suffix_args: RuntimeValue,
) -> RuntimeValue {
    if fptr == 0 {
        return checked_i64_result(WFFI_NULL_FUNCTION, 0);
    }
    let Some(owner) = byte_array_bytes(bytes) else {
        return checked_i64_result(WFFI_INVALID_ARGUMENT, 0);
    };
    let (Ok(offset), Ok(length)) = (usize::try_from(offset), usize::try_from(length)) else {
        return checked_i64_result(WFFI_INVALID_ARGUMENT, 0);
    };
    let Some(end) = offset.checked_add(length) else {
        return checked_i64_result(WFFI_INVALID_ARGUMENT, 0);
    };
    if end > owner.len() {
        return checked_i64_result(WFFI_INVALID_ARGUMENT, 0);
    }
    let (Some(mut args), Some(suffix)) = (runtime_i64_values(prefix_args), runtime_i64_values(suffix_args)) else {
        return checked_i64_result(WFFI_INVALID_ARGUMENT, 0);
    };
    if args.len() + 2 + suffix.len() > 8 {
        return checked_i64_result(WFFI_UNSUPPORTED_SIGNATURE, 0);
    }
    let ptr = if length == 0 {
        0
    } else {
        owner[offset..end].as_ptr() as i64
    };
    args.push(ptr);
    args.push(length as i64);
    args.extend_from_slice(&suffix);
    checked_i64_result(WFFI_OK, unsafe { call_i64_raw(fptr, &args) })
}

#[no_mangle]
pub extern "C" fn spl_fonts_call_init_blob(fptr: i64, blob: RuntimeValue, digest: RuntimeValue) -> i64 {
    if fptr == 0 {
        return 0;
    }
    let (Some(blob), Some(digest)) = (byte_array_bytes(blob), byte_array_bytes(digest)) else {
        return 0;
    };
    let args = [
        blob.as_ptr() as i64,
        blob.len() as i64,
        digest.as_ptr() as i64,
        digest.len() as i64,
    ];
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
pub extern "C" fn spl_fonts_call_layout_text(fptr: i64, text: RuntimeValue, size_px: i64, max_width: i64) -> i64 {
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
    try_call_f64_value(fptr, args_rv, nargs).unwrap_or(0.0)
}

/// Interpreter/native-equivalent checked float transport. The second element
/// is the exact IEEE-754 bit pattern and is meaningful only for status zero.
#[no_mangle]
pub extern "C" fn spl_wffi_call_f64_checked(fptr: i64, args_rv: RuntimeValue, nargs: i64) -> RuntimeValue {
    match try_call_f64_value(fptr, args_rv, nargs) {
        Ok(value) => checked_i64_result(WFFI_OK, value.to_bits() as i64),
        Err(status) => checked_i64_result(status, 0),
    }
}

#[inline]
fn try_call_f64_value(fptr: i64, args_rv: RuntimeValue, nargs: i64) -> Result<f64, i64> {
    if fptr == 0 {
        return Err(WFFI_NULL_FUNCTION);
    }

    let Ok(n) = usize::try_from(nargs) else {
        return Err(WFFI_INVALID_ARGUMENT);
    };
    let Ok(available) = usize::try_from(rt_array_len(args_rv)) else {
        return Err(WFFI_INVALID_ARGUMENT);
    };
    if n > 8 {
        return Err(WFFI_UNSUPPORTED_SIGNATURE);
    }
    if n > available {
        return Err(WFFI_INVALID_ARGUMENT);
    }
    let mut raw_args: [f64; 8] = [0.0; 8];
    for (i, slot) in raw_args.iter_mut().enumerate().take(n) {
        let val = rt_array_get(args_rv, i as i64);
        let Some(value) = runtime_value_to_f64(val) else {
            return Err(WFFI_INVALID_ARGUMENT);
        };
        *slot = value;
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

    Ok(unsafe {
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
            _ => unreachable!("argument count validated above"),
        }
    })
}

fn runtime_value_to_f64(value: RuntimeValue) -> Option<f64> {
    if value.is_float() {
        return Some(value.as_float());
    }
    if value.0 & 0x7 == 0 {
        return Some(value.as_int() as f64);
    }
    None
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
    use super::super::collections::{rt_array_new, rt_array_push, rt_string_new};

    unsafe extern "C" fn i64_two_args(a: i64, b: i64) -> i64 {
        a + b
    }

    unsafe extern "C" fn i64_zero() -> i64 {
        0
    }

    #[test]
    fn spl_wffi_call_i64_decodes_tagged_integer_arguments() {
        let args = rt_array_new(2);
        assert!(rt_array_push(args, RuntimeValue::from_int(0x24c_7468)));
        assert!(rt_array_push(args, RuntimeValue::from_int(7)));

        let result = spl_wffi_call_i64(i64_two_args as usize as i64, args, 2);

        assert_eq!(result, 0x24c_746f);
    }

    #[test]
    fn checked_i64_transport_distinguishes_zero_from_bridge_failure() {
        let args = rt_array_new(0);
        let ok = spl_wffi_call_i64_checked(i64_zero as usize as i64, args, 0);
        assert_eq!(rt_array_len(ok), 2);
        assert_eq!(rt_array_get(ok, 0).as_int(), WFFI_OK);
        assert_eq!(rt_array_get(ok, 1).as_int(), 0);

        let rejected = spl_wffi_call_i64_checked(0, args, 0);
        assert_eq!(rt_array_get(rejected, 0).as_int(), WFFI_NULL_FUNCTION);
    }

    #[test]
    fn checked_i64_transport_rejects_count_beyond_array_without_calling() {
        let args = rt_array_new(0);
        let rejected = spl_wffi_call_i64_checked(i64_zero as usize as i64, args, 1);
        assert_eq!(rt_array_get(rejected, 0).as_int(), WFFI_INVALID_ARGUMENT);
    }

    unsafe extern "C" fn f64_no_args() -> f64 {
        6.25
    }

    unsafe extern "C" fn f64_zero() -> f64 {
        0.0
    }

    #[test]
    fn spl_wffi_call_f64_invokes_no_arg_function_pointer() {
        let result = spl_wffi_call_f64(f64_no_args as usize as i64, RuntimeValue::NIL, 0);
        assert_eq!(result, 6.25);
    }

    #[test]
    fn checked_f64_transport_distinguishes_zero_from_bridge_failure() {
        let args = rt_array_new(0);
        let ok = spl_wffi_call_f64_checked(f64_zero as usize as i64, args, 0);
        assert_eq!(rt_array_get(ok, 0).as_int(), WFFI_OK);
        assert_eq!(f64::from_bits(rt_array_get(ok, 1).as_int() as u64), 0.0);

        let rejected = spl_wffi_call_f64_checked(0, args, 0);
        assert_eq!(rt_array_get(rejected, 0).as_int(), WFFI_NULL_FUNCTION);
    }

    #[test]
    fn spl_dlclose_rejects_null_handle_instead_of_fabricating_success() {
        assert_eq!(spl_dlclose(0), -1);
        assert_eq!(rt_host_dynlib_close(0), -1);
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn native_dynlib_snapshot_is_sealed_and_preserves_bytes() {
        let path = std::env::temp_dir().join(format!(
            "simple-native-sffi-snapshot-{}",
            std::process::id(),
        ));
        std::fs::write(&path, b"provider-a").unwrap();
        let path_text = path.to_string_lossy();
        let path_rv = rt_string_new(path_text.as_ptr(), path_text.len() as u64);
        let fd = spl_dynlib_snapshot_linux(path_rv) as libc::c_int;
        assert!(fd >= 0);
        std::fs::write(&path, b"provider-b").unwrap();

        let seals = unsafe { libc::fcntl(fd, libc::F_GET_SEALS) };
        let required = libc::F_SEAL_WRITE | libc::F_SEAL_GROW | libc::F_SEAL_SHRINK | libc::F_SEAL_SEAL;
        assert_eq!(seals & required, required);
        let mut bytes = [0u8; 10];
        let got = unsafe { libc::pread(fd, bytes.as_mut_ptr().cast(), bytes.len(), 0) };
        assert_eq!(got, bytes.len() as isize);
        assert_eq!(&bytes, b"provider-a");
        assert_eq!(unsafe { libc::write(fd, b"x".as_ptr().cast(), 1) }, -1);
        assert_eq!(std::io::Error::last_os_error().raw_os_error(), Some(libc::EPERM));

        unsafe { libc::close(fd) };
        std::fs::remove_file(path).unwrap();
    }

    #[test]
    fn font_init_status_bridges_report_failure_for_null_function_pointer() {
        // The font initialization contract uses 1 for success and 0 for
        // failure, so zero is an explicit failure status here, not a
        // fabricated value-return sentinel.
        assert_eq!(spl_fonts_call_init_blob(0, RuntimeValue::NIL, RuntimeValue::NIL), 0);
        assert_eq!(spl_fonts_call_init_path(0, RuntimeValue::NIL), 0);
    }
}
