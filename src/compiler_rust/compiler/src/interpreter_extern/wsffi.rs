//! Wrapped SFFI (WFFI) functions for dynamic library loading
//!
//! Provides spl_dlopen, spl_dlsym, spl_dlclose, spl_wffi_call_i64,
//! spl_wffi_call_f64,
//! spl_f64_to_bits, spl_bits_to_f64, spl_str_ptr, and rt_cstring_to_text
//! for the interpreter, enabling dynamic loading of native shared libraries
//! (e.g., libspl_torch.so) at runtime.

use crate::error::CompileError;
use crate::value::Value;
use std::collections::HashMap;
use std::ffi::{CStr, CString};
use std::sync::Mutex;

/// Global registry of loaded libraries to prevent double-loading
static LOADED_LIBS: std::sync::LazyLock<Mutex<HashMap<String, usize>>> =
    std::sync::LazyLock::new(|| Mutex::new(HashMap::new()));

const BACKEND_PLUGIN_ABI_V1: u32 = 1;
const BACKEND_BRIDGE_MAGIC_V1: u32 = 0x3150_4253;
const BACKEND_BRIDGE_HEADER_SIZE_V1: usize = 32;

#[repr(C)]
#[derive(Clone, Copy, Default)]
struct BackendSliceV1 {
    data: *const u8,
    size: u64,
}

#[repr(C)]
#[derive(Clone, Copy, Default)]
struct BackendOwnedBufferV1 {
    data: *const u8,
    size: u64,
    owner_token: u64,
}

#[repr(C)]
#[derive(Clone, Copy, Default)]
struct BackendRequestV1 {
    abi_version: u32,
    struct_size: u32,
    role: u32,
    reserved0: u32,
    backend_name: BackendSliceV1,
    target: BackendSliceV1,
    cpu: BackendSliceV1,
    features_wire: BackendSliceV1,
    optimization: BackendSliceV1,
    mir_abi_digest: BackendSliceV1,
    required_capabilities: u64,
}

#[repr(C)]
#[derive(Clone, Copy, Default)]
struct BackendCompileResultV1 {
    abi_version: u32,
    struct_size: u32,
    result_kind: u32,
    status: i32,
    payload: BackendOwnedBufferV1,
}

type BackendOpenV1 = unsafe extern "C" fn(*const BackendRequestV1, *mut u64) -> i32;
type BackendCompileV1 = unsafe extern "C" fn(u64, BackendSliceV1, *mut BackendCompileResultV1) -> i32;
type BackendFinalizeV1 = unsafe extern "C" fn(u64, *mut BackendCompileResultV1) -> i32;
type BackendDiagnosticsV1 = unsafe extern "C" fn(u64, *mut BackendOwnedBufferV1) -> i32;
type BackendCloseV1 = unsafe extern "C" fn(u64) -> i32;
type BackendReleaseV1 = unsafe extern "C" fn(u64, BackendOwnedBufferV1) -> i32;

#[repr(C)]
struct BackendVtableV1 {
    abi_version: u32,
    struct_size: u32,
    open_session: Option<BackendOpenV1>,
    compile_module: Option<BackendCompileV1>,
    finalize_object: Option<BackendFinalizeV1>,
    diagnostics: Option<BackendDiagnosticsV1>,
    close_session: Option<BackendCloseV1>,
    release_buffer: Option<BackendReleaseV1>,
}

#[repr(C)]
struct BackendDescriptorV1 {
    abi_version: u32,
    struct_size: u32,
    provider_identity: BackendSliceV1,
    provider_version: BackendSliceV1,
    build_id: BackendSliceV1,
    mir_abi_digest: BackendSliceV1,
    roles: u64,
    capabilities: u64,
    targets_wire: BackendSliceV1,
    vtable: *const BackendVtableV1,
}

fn backend_bytes(value: &Value) -> Option<Vec<u8>> {
    if let Some(bytes) = value.byte_array_view() {
        return Some(bytes.to_vec());
    }
    let values = match value {
        Value::Array(values) | Value::FrozenArray(values) => values,
        _ => return None,
    };
    values
        .iter()
        .map(|value| match value {
            Value::Int(value) if (0..=255).contains(value) => Some(*value as u8),
            Value::UInt { value, .. } if *value <= 255 => Some(*value as u8),
            _ => None,
        })
        .collect()
}

fn backend_envelope(status: i32, result_kind: u32, payload: &[u8], diagnostic: &[u8]) -> Value {
    let mut wire = Vec::with_capacity(BACKEND_BRIDGE_HEADER_SIZE_V1 + payload.len() + diagnostic.len());
    wire.extend_from_slice(&BACKEND_BRIDGE_MAGIC_V1.to_le_bytes());
    wire.extend_from_slice(&BACKEND_PLUGIN_ABI_V1.to_le_bytes());
    wire.extend_from_slice(&status.to_le_bytes());
    wire.extend_from_slice(&result_kind.to_le_bytes());
    wire.extend_from_slice(&(payload.len() as u64).to_le_bytes());
    wire.extend_from_slice(&(diagnostic.len() as u64).to_le_bytes());
    wire.extend_from_slice(payload);
    wire.extend_from_slice(diagnostic);
    Value::byte_array(wire)
}

unsafe fn copy_backend_buffer(buffer: BackendOwnedBufferV1) -> Option<Vec<u8>> {
    if buffer.size == 0 {
        return Some(Vec::new());
    }
    if buffer.data.is_null() || buffer.size > isize::MAX as u64 {
        return None;
    }
    Some(unsafe { std::slice::from_raw_parts(buffer.data, buffer.size as usize) }.to_vec())
}

/// Interpreter twin of the native backend-plugin bridge. All arguments and
/// the result use packed Simple `[u8]` values.
pub fn spl_backend_plugin_run_v1(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 3 {
        return Ok(backend_envelope(100, 0, &[], &[]));
    }
    let (Some(path_bytes), Some(request), Some(mir)) = (
        backend_bytes(&args[0]),
        backend_bytes(&args[1]),
        backend_bytes(&args[2]),
    ) else {
        return Ok(backend_envelope(100, 0, &[], &[]));
    };
    if path_bytes.is_empty() || request.len() < 16 || mir.is_empty() {
        return Ok(backend_envelope(100, 0, &[], &[]));
    }
    let Ok(path) = CString::new(path_bytes) else {
        return Ok(backend_envelope(100, 0, &[], &[]));
    };

    #[cfg(unix)]
    unsafe {
        let library = libc::dlopen(path.as_ptr(), libc::RTLD_NOW | libc::RTLD_LOCAL);
        if library.is_null() {
            return Ok(backend_envelope(103, 0, &[], &[]));
        }
        let finish = |value| {
            libc::dlclose(library);
            Ok(value)
        };
        let symbol = libc::dlsym(library, c"simple_backend_plugin_v1".as_ptr());
        if symbol.is_null() {
            return finish(backend_envelope(104, 0, &[], &[]));
        }
        let entry: unsafe extern "C" fn() -> *const BackendDescriptorV1 = std::mem::transmute(symbol);
        let descriptor = entry();
        let abi = u32::from_le_bytes(request[0..4].try_into().unwrap());
        let role = u32::from_le_bytes(request[4..8].try_into().unwrap());
        let capabilities = u64::from_le_bytes(request[8..16].try_into().unwrap());
        if descriptor.is_null()
            || abi != BACKEND_PLUGIN_ABI_V1
            || (*descriptor).abi_version != BACKEND_PLUGIN_ABI_V1
            || (*descriptor).struct_size < std::mem::size_of::<BackendDescriptorV1>() as u32
            || (*descriptor).vtable.is_null()
            || (*(*descriptor).vtable).abi_version != BACKEND_PLUGIN_ABI_V1
            || (*(*descriptor).vtable).struct_size < std::mem::size_of::<BackendVtableV1>() as u32
        {
            return finish(backend_envelope(105, 0, &[], &[]));
        }
        let vtable = &*(*descriptor).vtable;
        let (Some(open), Some(compile), Some(finalize), Some(diagnostics), Some(close), Some(release)) = (
            vtable.open_session,
            vtable.compile_module,
            vtable.finalize_object,
            vtable.diagnostics,
            vtable.close_session,
            vtable.release_buffer,
        ) else {
            return finish(backend_envelope(105, 0, &[], &[]));
        };
        let request = BackendRequestV1 {
            abi_version: abi,
            struct_size: std::mem::size_of::<BackendRequestV1>() as u32,
            role,
            required_capabilities: capabilities,
            ..Default::default()
        };
        let mut session = 0;
        let status = open(&request, &mut session);
        if status != 0 || session == 0 {
            return finish(backend_envelope(if status != 0 { status } else { 106 }, 0, &[], &[]));
        }
        let mut module = BackendCompileResultV1::default();
        let mut object = BackendCompileResultV1::default();
        let mut diagnostic = BackendOwnedBufferV1::default();
        let mut status = compile(
            session,
            BackendSliceV1 {
                data: mir.as_ptr(),
                size: mir.len() as u64,
            },
            &mut module,
        );
        if status == 0 {
            status = finalize(session, &mut object);
        }
        if status == 0 {
            status = diagnostics(session, &mut diagnostic);
        }
        let payload_bytes = if status == 0 {
            copy_backend_buffer(object.payload).unwrap_or_default()
        } else {
            Vec::new()
        };
        let diagnostic_bytes = copy_backend_buffer(diagnostic).unwrap_or_default();
        let result = backend_envelope(status, object.result_kind, &payload_bytes, &diagnostic_bytes);
        if !module.payload.data.is_null() {
            let _ = release(session, module.payload);
        }
        if !object.payload.data.is_null() {
            let _ = release(session, object.payload);
        }
        if !diagnostic.data.is_null() {
            let _ = release(session, diagnostic);
        }
        let close_status = close(session);
        if close_status != 0 {
            return finish(backend_envelope(close_status, 0, &[], &[]));
        }
        finish(result)
    }

    #[cfg(not(unix))]
    {
        let _ = path;
        Ok(backend_envelope(102, 0, &[], &[]))
    }
}

/// Open a shared library and return its handle as i64.
///
/// Callable from Simple as: `spl_dlopen(path: text) -> i64`
/// Boundary failures are typed interpreter errors; they never become a handle.
pub fn spl_dlopen(args: &[Value]) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Err(CompileError::runtime("spl_dlopen requires 1 argument (path)"));
    }

    let path = match &args[0] {
        Value::Str(s) => s.clone(),
        _ => return Err(CompileError::runtime("spl_dlopen: path must be a string")),
    };

    #[cfg(unix)]
    {
        let c_path = match CString::new(path.as_str()) {
            Ok(c) => c,
            Err(_) => return Err(CompileError::runtime("spl_dlopen: path contains an interior NUL")),
        };

        let handle = unsafe { libc::dlopen(c_path.as_ptr(), libc::RTLD_LAZY | libc::RTLD_LOCAL) };

        if handle.is_null() {
            let err = unsafe { libc::dlerror() };
            if !err.is_null() {
                let err_str = unsafe { CStr::from_ptr(err) }.to_string_lossy();
                tracing::warn!("spl_dlopen failed for '{}': {}", path, err_str);
            }
            Err(CompileError::runtime(format!("spl_dlopen failed for '{path}'")))
        } else {
            Ok(Value::Int(handle as usize as i64))
        }
    }

    #[cfg(windows)]
    {
        use windows_sys::Win32::System::LibraryLoader::LoadLibraryW;
        if path.contains('\0') {
            return Err(CompileError::runtime("spl_dlopen: path contains an interior NUL"));
        }
        let wide: Vec<u16> = path.encode_utf16().chain(std::iter::once(0)).collect();
        let handle = unsafe { LoadLibraryW(wide.as_ptr()) };
        if handle.is_null() {
            tracing::warn!("spl_dlopen failed for '{}'", path);
            Err(CompileError::runtime(format!("spl_dlopen failed for '{path}'")))
        } else {
            Ok(Value::Int(handle as usize as i64))
        }
    }

    #[cfg(not(any(unix, windows)))]
    {
        tracing::warn!("spl_dlopen not supported on this platform");
        Err(CompileError::runtime("spl_dlopen is unsupported on this platform"))
    }
}

/// Status/out dynload ABI. Failure initializes the output and returns a
/// non-zero status, preserving a legitimate foreign integer zero elsewhere.
pub fn spl_dlopen_checked(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 2 {
        return Err(CompileError::runtime(
            "spl_dlopen_checked requires 2 arguments (path, out_handle)",
        ));
    }
    let output = match &args[1] {
        Value::BorrowMut(value) => value,
        _ => return Err(CompileError::runtime("spl_dlopen_checked: output must be &mut i64")),
    };
    *output.inner_mut() = Value::Int(0);
    match spl_dlopen(&args[..1]) {
        Ok(Value::Int(handle)) if handle != 0 => {
            *output.inner_mut() = Value::Int(handle);
            Ok(Value::Int(0))
        }
        _ => Ok(Value::Int(2)),
    }
}

/// Look up a symbol in a loaded library by name.
///
/// Callable from Simple as: `spl_dlsym(handle: i64, name: text) -> i64`
/// Boundary failures are typed interpreter errors; they never become a symbol.
pub fn spl_dlsym(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 2 {
        return Err(CompileError::runtime("spl_dlsym requires 2 arguments (handle, name)"));
    }

    let handle_val = match &args[0] {
        Value::Int(h) => *h as usize,
        _ => return Err(CompileError::runtime("spl_dlsym: handle must be an integer")),
    };
    if handle_val == 0 {
        return Err(CompileError::runtime("spl_dlsym: null provider handle"));
    }

    let name = match &args[1] {
        Value::Str(s) => s.clone(),
        _ => return Err(CompileError::runtime("spl_dlsym: name must be a string")),
    };

    let c_name = match CString::new(name.as_str()) {
        Ok(c) => c,
        Err(_) => return Err(CompileError::runtime("spl_dlsym: name contains an interior NUL")),
    };

    #[cfg(unix)]
    {
        let handle = handle_val as *mut libc::c_void;
        let sym = unsafe { libc::dlsym(handle, c_name.as_ptr()) };
        if sym.is_null() {
            Err(CompileError::runtime(format!("spl_dlsym: unresolved symbol '{name}'")))
        } else {
            Ok(Value::Int(sym as usize as i64))
        }
    }

    #[cfg(windows)]
    {
        extern "system" {
            fn GetProcAddress(hModule: isize, lpProcName: *const u8) -> *mut std::ffi::c_void;
        }
        let sym = unsafe { GetProcAddress(handle_val as isize, c_name.as_ptr() as *const u8) };
        if sym.is_null() {
            Err(CompileError::runtime(format!("spl_dlsym: unresolved symbol '{name}'")))
        } else {
            Ok(Value::Int(sym as usize as i64))
        }
    }

    #[cfg(not(any(unix, windows)))]
    {
        Err(CompileError::runtime("spl_dlsym is unsupported on this platform"))
    }
}

/// Status/out symbol-resolution ABI.
pub fn spl_dlsym_checked(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 3 {
        return Err(CompileError::runtime(
            "spl_dlsym_checked requires 3 arguments (handle, name, out_symbol)",
        ));
    }
    let output = match &args[2] {
        Value::BorrowMut(value) => value,
        _ => return Err(CompileError::runtime("spl_dlsym_checked: output must be &mut i64")),
    };
    *output.inner_mut() = Value::Int(0);
    match spl_dlsym(&args[..2]) {
        Ok(Value::Int(symbol)) if symbol != 0 => {
            *output.inner_mut() = Value::Int(symbol);
            Ok(Value::Int(0))
        }
        _ => Ok(Value::Int(3)),
    }
}

/// Checked current-process symbol resolution, separate from null-handle lookup.
pub fn spl_dlsym_process_checked(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 2 {
        return Err(CompileError::runtime(
            "spl_dlsym_process_checked requires 2 arguments (name, out_symbol)",
        ));
    }
    let output = match &args[1] {
        Value::BorrowMut(value) => value,
        _ => {
            return Err(CompileError::runtime(
                "spl_dlsym_process_checked: output must be &mut i64",
            ))
        }
    };
    *output.inner_mut() = Value::Int(0);
    let name = match &args[0] {
        Value::Str(value) if !value.is_empty() => value,
        _ => return Ok(Value::Int(1)),
    };
    let c_name = match CString::new(name.as_str()) {
        Ok(value) => value,
        Err(_) => return Ok(Value::Int(1)),
    };

    #[cfg(unix)]
    let symbol = unsafe { libc::dlsym(std::ptr::null_mut(), c_name.as_ptr()) };
    #[cfg(windows)]
    let symbol = unsafe {
        extern "system" {
            fn GetModuleHandleW(name: *const u16) -> isize;
            fn GetProcAddress(module: isize, name: *const u8) -> *mut std::ffi::c_void;
        }
        let process = GetModuleHandleW(std::ptr::null());
        if process == 0 {
            std::ptr::null_mut()
        } else {
            GetProcAddress(process, c_name.as_ptr() as *const u8)
        }
    };
    #[cfg(not(any(unix, windows)))]
    let symbol: *mut std::ffi::c_void = std::ptr::null_mut();

    if symbol.is_null() {
        return Ok(Value::Int(3));
    }
    *output.inner_mut() = Value::Int(symbol as usize as i64);
    Ok(Value::Int(0))
}

/// Close a loaded library.
///
/// Callable from Simple as: `spl_dlclose(handle: i64) -> i64`
/// Returns 0 on success.
pub fn spl_dlclose(args: &[Value]) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Err(CompileError::runtime("spl_dlclose requires 1 argument (handle)"));
    }

    let handle_val = match &args[0] {
        Value::Int(h) => *h as usize,
        _ => return Err(CompileError::runtime("spl_dlclose: handle must be an integer")),
    };

    #[cfg(unix)]
    {
        let handle = handle_val as *mut libc::c_void;
        let result = unsafe { libc::dlclose(handle) };
        Ok(Value::Int(result as i64))
    }

    #[cfg(windows)]
    {
        extern "system" {
            fn FreeLibrary(hLibModule: isize) -> i32;
        }
        let result = unsafe { FreeLibrary(handle_val as isize) };
        Ok(Value::Int(if result != 0 { 0 } else { 1 }))
    }

    #[cfg(not(any(unix, windows)))]
    {
        Ok(Value::Int(1))
    }
}

/// Call a function pointer with i64 arguments and return an i64 result.
///
/// Callable from Simple as: `spl_wffi_call_i64(fptr: i64, args: [i64], nargs: i64) -> i64`
///
/// This is the core WFFI dispatch function that enables calling arbitrary
/// C functions loaded via dlsym. Supports 0-8 arguments.
pub fn spl_wffi_call_i64(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 3 {
        return Err(CompileError::runtime(
            "spl_wffi_call_i64 requires 3 arguments (fptr, args, nargs)",
        ));
    }

    let fptr = match &args[0] {
        Value::Int(p) => *p as usize,
        _ => return Err(CompileError::runtime("spl_wffi_call_i64: fptr must be an integer")),
    };

    if fptr == 0 {
        return Err(CompileError::runtime("spl_wffi_call_i64: null function pointer"));
    }

    let supplied = match &args[1] {
        Value::Array(arr) => arr,
        _ => return Err(CompileError::runtime("spl_wffi_call_i64: args must be an array")),
    };

    let nargs = match &args[2] {
        Value::Int(n) => {
            usize::try_from(*n).map_err(|_| CompileError::runtime("spl_wffi_call_i64: nargs must be non-negative"))?
        }
        _ => return Err(CompileError::runtime("spl_wffi_call_i64: nargs must be an integer")),
    };
    if nargs > 8 {
        return Err(CompileError::runtime("spl_wffi_call_i64: max 8 arguments supported"));
    }
    if nargs > supplied.len() {
        return Err(CompileError::runtime(
            "spl_wffi_call_i64: nargs exceeds supplied argument array",
        ));
    }
    let mut call_args = [0i64; 8];
    for (index, value) in supplied.iter().take(nargs).enumerate() {
        call_args[index] = match value {
            Value::Int(number) => *number,
            _ => return Err(CompileError::runtime("spl_wffi_call_i64: args must be integers")),
        };
    }

    // Safety: we trust the caller has provided a valid function pointer
    // and the correct number of arguments. This is inherently unsafe SFFI.
    let result: i64 = unsafe {
        match nargs {
            0 => {
                let f: extern "C" fn() -> i64 = std::mem::transmute(fptr);
                f()
            }
            1 => {
                let f: extern "C" fn(i64) -> i64 = std::mem::transmute(fptr);
                f(call_args[0])
            }
            2 => {
                let f: extern "C" fn(i64, i64) -> i64 = std::mem::transmute(fptr);
                f(call_args[0], call_args[1])
            }
            3 => {
                let f: extern "C" fn(i64, i64, i64) -> i64 = std::mem::transmute(fptr);
                f(call_args[0], call_args[1], call_args[2])
            }
            4 => {
                let f: extern "C" fn(i64, i64, i64, i64) -> i64 = std::mem::transmute(fptr);
                f(call_args[0], call_args[1], call_args[2], call_args[3])
            }
            5 => {
                let f: extern "C" fn(i64, i64, i64, i64, i64) -> i64 = std::mem::transmute(fptr);
                f(call_args[0], call_args[1], call_args[2], call_args[3], call_args[4])
            }
            6 => {
                let f: extern "C" fn(i64, i64, i64, i64, i64, i64) -> i64 = std::mem::transmute(fptr);
                f(
                    call_args[0],
                    call_args[1],
                    call_args[2],
                    call_args[3],
                    call_args[4],
                    call_args[5],
                )
            }
            7 => {
                let f: extern "C" fn(i64, i64, i64, i64, i64, i64, i64) -> i64 = std::mem::transmute(fptr);
                f(
                    call_args[0],
                    call_args[1],
                    call_args[2],
                    call_args[3],
                    call_args[4],
                    call_args[5],
                    call_args[6],
                )
            }
            8 => {
                let f: extern "C" fn(i64, i64, i64, i64, i64, i64, i64, i64) -> i64 = std::mem::transmute(fptr);
                f(
                    call_args[0],
                    call_args[1],
                    call_args[2],
                    call_args[3],
                    call_args[4],
                    call_args[5],
                    call_args[6],
                    call_args[7],
                )
            }
            _ => {
                return Err(CompileError::runtime("spl_wffi_call_i64: max 8 arguments supported"));
            }
        }
    };

    Ok(Value::Int(result))
}

/// Allocation-free typed C-boolean call with no arguments.
pub fn spl_wffi_call_bool0_checked(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 2 {
        return Ok(Value::Int(1));
    }
    let fptr = match args[0] {
        Value::Int(value) if value != 0 => value as usize,
        _ => return Ok(Value::Int(2)),
    };
    let output = match &args[1] {
        Value::BorrowMut(value) => value,
        _ => return Ok(Value::Int(1)),
    };
    *output.inner_mut() = Value::Bool(false);
    let function: extern "C" fn() -> bool = unsafe { std::mem::transmute(fptr) };
    *output.inner_mut() = Value::Bool(function());
    Ok(Value::Int(0))
}

/// Allocation-free typed C-boolean call with one i64 argument.
pub fn spl_wffi_call_bool1_checked(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 3 {
        return Ok(Value::Int(1));
    }
    let fptr = match args[0] {
        Value::Int(value) if value != 0 => value as usize,
        _ => return Ok(Value::Int(2)),
    };
    let arg0 = match args[1] {
        Value::Int(value) => value,
        _ => return Ok(Value::Int(1)),
    };
    let output = match &args[2] {
        Value::BorrowMut(value) => value,
        _ => return Ok(Value::Int(1)),
    };
    *output.inner_mut() = Value::Bool(false);
    let function: extern "C" fn(i64) -> bool = unsafe { std::mem::transmute(fptr) };
    *output.inner_mut() = Value::Bool(function(arg0));
    Ok(Value::Int(0))
}

/// Checked WFFI transport. Returns `[status, value]`; value is meaningful only
/// for status zero. Bridge failures never masquerade as a foreign zero result.
pub fn spl_wffi_call_i64_checked(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 3 {
        return Ok(Value::array(vec![Value::Int(1), Value::Int(0)]));
    }
    if !matches!(args[0], Value::Int(p) if p != 0) {
        return Ok(Value::array(vec![Value::Int(2), Value::Int(0)]));
    }
    let supplied = match &args[1] {
        Value::Array(values) if values.iter().all(|value| matches!(value, Value::Int(_))) => values.len(),
        _ => return Ok(Value::array(vec![Value::Int(1), Value::Int(0)])),
    };
    let nargs = match args[2] {
        Value::Int(n) => match usize::try_from(n) {
            Ok(n) => n,
            Err(_) => return Ok(Value::array(vec![Value::Int(1), Value::Int(0)])),
        },
        _ => return Ok(Value::array(vec![Value::Int(1), Value::Int(0)])),
    };
    if nargs > 8 {
        return Ok(Value::array(vec![Value::Int(3), Value::Int(0)]));
    }
    if nargs > supplied {
        return Ok(Value::array(vec![Value::Int(1), Value::Int(0)]));
    }
    let value = spl_wffi_call_i64(args)?;
    Ok(Value::array(vec![Value::Int(0), value]))
}

/// Allocation-free checked integer transport with caller-owned scalar output.
pub fn spl_wffi_try_call_i64_out(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 4 {
        return Ok(Value::Int(1));
    }
    let output = match &args[3] {
        Value::BorrowMut(value) => value,
        _ => return Ok(Value::Int(1)),
    };
    *output.inner_mut() = Value::Int(0);
    if !matches!(args[0], Value::Int(pointer) if pointer != 0) {
        return Ok(Value::Int(2));
    }
    let supplied = match &args[1] {
        Value::Array(values) if values.iter().all(|value| matches!(value, Value::Int(_))) => values.len(),
        _ => return Ok(Value::Int(1)),
    };
    let nargs = match args[2] {
        Value::Int(value) => match usize::try_from(value) {
            Ok(value) => value,
            Err(_) => return Ok(Value::Int(1)),
        },
        _ => return Ok(Value::Int(1)),
    };
    if nargs > 8 {
        return Ok(Value::Int(3));
    }
    if nargs > supplied {
        return Ok(Value::Int(1));
    }
    match spl_wffi_call_i64(&args[..3])? {
        Value::Int(value) => {
            *output.inner_mut() = Value::Int(value);
            Ok(Value::Int(0))
        }
        _ => Ok(Value::Int(1)),
    }
}

/// Call a function pointer with f64 arguments and return an f64 result.
///
/// Callable from Simple as: `spl_wffi_call_f64(fptr: i64, args: [f64], nargs: i64) -> f64`
///
/// Supports 0-8 arguments. Integer arguments are accepted and widened to f64
/// for parity with normal Simple numeric conversion.
pub fn spl_wffi_call_f64(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 3 {
        return Err(CompileError::runtime(
            "spl_wffi_call_f64 requires 3 arguments (fptr, args, nargs)",
        ));
    }

    let fptr = match &args[0] {
        Value::Int(p) => *p as usize,
        _ => return Err(CompileError::runtime("spl_wffi_call_f64: fptr must be an integer")),
    };

    if fptr == 0 {
        return Err(CompileError::runtime("spl_wffi_call_f64: null function pointer"));
    }

    let call_args: Vec<f64> = match &args[1] {
        Value::Array(arr) => arr.iter().map(Value::as_float).collect::<Result<Vec<_>, _>>()?,
        _ => return Err(CompileError::runtime("spl_wffi_call_f64: args must be an array")),
    };

    let nargs = match &args[2] {
        Value::Int(n) => {
            usize::try_from(*n).map_err(|_| CompileError::runtime("spl_wffi_call_f64: nargs must be non-negative"))?
        }
        _ => return Err(CompileError::runtime("spl_wffi_call_f64: nargs must be an integer")),
    };
    if nargs > 8 {
        return Err(CompileError::runtime("spl_wffi_call_f64: max 8 arguments supported"));
    }
    if nargs > call_args.len() {
        return Err(CompileError::runtime(
            "spl_wffi_call_f64: nargs exceeds supplied argument array",
        ));
    }

    let result: f64 = unsafe {
        match nargs {
            0 => {
                let f: extern "C" fn() -> f64 = std::mem::transmute(fptr);
                f()
            }
            1 => {
                let f: extern "C" fn(f64) -> f64 = std::mem::transmute(fptr);
                f(call_args[0])
            }
            2 => {
                let f: extern "C" fn(f64, f64) -> f64 = std::mem::transmute(fptr);
                f(call_args[0], call_args[1])
            }
            3 => {
                let f: extern "C" fn(f64, f64, f64) -> f64 = std::mem::transmute(fptr);
                f(call_args[0], call_args[1], call_args[2])
            }
            4 => {
                let f: extern "C" fn(f64, f64, f64, f64) -> f64 = std::mem::transmute(fptr);
                f(call_args[0], call_args[1], call_args[2], call_args[3])
            }
            5 => {
                let f: extern "C" fn(f64, f64, f64, f64, f64) -> f64 = std::mem::transmute(fptr);
                f(call_args[0], call_args[1], call_args[2], call_args[3], call_args[4])
            }
            6 => {
                let f: extern "C" fn(f64, f64, f64, f64, f64, f64) -> f64 = std::mem::transmute(fptr);
                f(
                    call_args[0],
                    call_args[1],
                    call_args[2],
                    call_args[3],
                    call_args[4],
                    call_args[5],
                )
            }
            7 => {
                let f: extern "C" fn(f64, f64, f64, f64, f64, f64, f64) -> f64 = std::mem::transmute(fptr);
                f(
                    call_args[0],
                    call_args[1],
                    call_args[2],
                    call_args[3],
                    call_args[4],
                    call_args[5],
                    call_args[6],
                )
            }
            8 => {
                let f: extern "C" fn(f64, f64, f64, f64, f64, f64, f64, f64) -> f64 = std::mem::transmute(fptr);
                f(
                    call_args[0],
                    call_args[1],
                    call_args[2],
                    call_args[3],
                    call_args[4],
                    call_args[5],
                    call_args[6],
                    call_args[7],
                )
            }
            _ => {
                return Err(CompileError::runtime("spl_wffi_call_f64: max 8 arguments supported"));
            }
        }
    };

    Ok(Value::Float(result))
}

pub fn spl_wffi_call_f64_checked(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 3 {
        return Ok(Value::array(vec![Value::Int(1), Value::Int(0)]));
    }
    if !matches!(args[0], Value::Int(p) if p != 0) {
        return Ok(Value::array(vec![Value::Int(2), Value::Int(0)]));
    }
    let supplied = match &args[1] {
        Value::Array(values)
            if values
                .iter()
                .all(|value| matches!(value, Value::Float(_) | Value::Int(_))) =>
        {
            values.len()
        }
        _ => return Ok(Value::array(vec![Value::Int(1), Value::Int(0)])),
    };
    let nargs = match args[2] {
        Value::Int(n) => match usize::try_from(n) {
            Ok(n) => n,
            Err(_) => return Ok(Value::array(vec![Value::Int(1), Value::Int(0)])),
        },
        _ => return Ok(Value::array(vec![Value::Int(1), Value::Int(0)])),
    };
    if nargs > 8 {
        return Ok(Value::array(vec![Value::Int(3), Value::Int(0)]));
    }
    if nargs > supplied {
        return Ok(Value::array(vec![Value::Int(1), Value::Int(0)]));
    }
    match spl_wffi_call_f64(args)? {
        Value::Float(value) => Ok(Value::array(vec![Value::Int(0), Value::Int(value.to_bits() as i64)])),
        _ => Ok(Value::array(vec![Value::Int(1), Value::Int(0)])),
    }
}

/// Convert f64 to its bit representation as i64.
///
/// Callable from Simple as: `spl_f64_to_bits(f: f64) -> i64`
pub fn spl_f64_to_bits(args: &[Value]) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Err(CompileError::runtime("spl_f64_to_bits requires 1 argument"));
    }

    let f = match &args[0] {
        Value::Float(f) => *f,
        Value::Int(n) => *n as f64,
        _ => return Err(CompileError::runtime("spl_f64_to_bits: argument must be a number")),
    };

    Ok(Value::Int(f.to_bits() as i64))
}

/// Convert i64 bit representation back to f64.
///
/// Callable from Simple as: `spl_bits_to_f64(bits: i64) -> f64`
pub fn spl_bits_to_f64(args: &[Value]) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Err(CompileError::runtime("spl_bits_to_f64 requires 1 argument"));
    }

    let bits = match &args[0] {
        Value::Int(n) => *n as u64,
        _ => return Err(CompileError::runtime("spl_bits_to_f64: argument must be an integer")),
    };

    Ok(Value::Float(f64::from_bits(bits)))
}

/// Get a pointer to the string data as i64.
///
/// Callable from Simple as: `spl_str_ptr(s: text) -> i64`
///
/// NOTE: The returned pointer is only valid as long as the string lives.
/// For SFFI calls, use it immediately within the same expression.
pub fn spl_str_ptr(args: &[Value]) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Err(CompileError::runtime("spl_str_ptr requires 1 argument"));
    }

    let s = match &args[0] {
        Value::Str(s) => s.clone(),
        _ => return Err(CompileError::runtime("spl_str_ptr: argument must be a string")),
    };

    // We need to create a null-terminated copy for C compatibility
    let c_str = match CString::new(s.as_str()) {
        Ok(c) => c,
        Err(_) => return Ok(Value::Int(0)),
    };

    // Leak the CString so the pointer stays valid
    let ptr = c_str.into_raw();
    Ok(Value::Int(ptr as usize as i64))
}

/// Convert a C string pointer to a Simple text value.
///
/// Callable from Simple as: `rt_cstring_to_text(ptr: i64) -> text`
pub fn rt_cstring_to_text(args: &[Value]) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Err(CompileError::runtime("rt_cstring_to_text requires 1 argument"));
    }

    let ptr = match &args[0] {
        Value::Int(p) => *p as usize as *const std::os::raw::c_char,
        _ => return Err(CompileError::runtime("rt_cstring_to_text: argument must be an integer")),
    };

    if ptr.is_null() {
        return Ok(Value::text(""));
    }

    let c_str = unsafe { CStr::from_ptr(ptr) };
    let s = c_str.to_string_lossy().into_owned();
    Ok(Value::text(s))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    extern "C" fn return_i64(value: i64) -> i64 {
        value
    }

    extern "C" fn add_scaled(a: f64, b: f64, scale: f64) -> f64 {
        (a + b) * scale
    }

    #[test]
    fn spl_wffi_call_f64_invokes_function_pointer() {
        let fptr = add_scaled as usize as i64;
        let args = Value::Array(Arc::new(vec![
            Value::Float(1.25),
            Value::Float(2.75),
            Value::Float(0.5),
        ]));

        let result = spl_wffi_call_f64(&[Value::Int(fptr), args, Value::Int(3)]).unwrap();

        match result {
            Value::Float(v) => assert_eq!(v, 2.0),
            other => panic!("expected float result, got {other:?}"),
        }
    }

    #[test]
    fn dynload_rejects_interior_nul_instead_of_returning_zero() {
        assert!(spl_dlopen(&[Value::text("invalid\0library")]).is_err());
    }

    #[test]
    fn symbol_lookup_rejects_null_handle_instead_of_returning_zero() {
        assert!(spl_dlsym(&[Value::Int(0), Value::text("missing")]).is_err());
    }

    #[test]
    fn integer_bridge_rejects_boolean_coercion() {
        let values = Value::Array(Arc::new(vec![Value::Bool(true)]));
        assert!(spl_wffi_call_i64(&[Value::Int(return_i64 as usize as i64), values, Value::Int(1),]).is_err());
    }

    #[cfg(unix)]
    #[test]
    fn backend_plugin_bridge_runs_real_v1_fixture_and_packs_canonical_envelope() {
        let repo = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../..");
        let fixture = repo.join("test/01_unit/compiler/backend_plugin/fixtures/backend_plugin_v1_fixture.c");
        let abi = repo.join("src/compiler/70.backend/backend_plugin/abi");
        let output = std::env::temp_dir().join(format!("simple-backend-plugin-v1-{}.so", std::process::id()));
        let status = std::process::Command::new("cc")
            .args(["-std=c11", "-fPIC", "-shared", "-I"])
            .arg(&abi)
            .arg(&fixture)
            .arg("-o")
            .arg(&output)
            .status()
            .expect("compile real backend plugin fixture");
        assert!(status.success());

        let mut request = Vec::new();
        request.extend_from_slice(&1u32.to_le_bytes());
        request.extend_from_slice(&2u32.to_le_bytes());
        request.extend_from_slice(&2u64.to_le_bytes());
        let result = spl_backend_plugin_run_v1(&[
            Value::byte_array(output.as_os_str().as_encoded_bytes().to_vec()),
            Value::byte_array(request),
            Value::byte_array(vec![1, 2, 3, 4]),
        ])
        .expect("interpreter bridge result");
        let wire = result.byte_array_view().expect("packed byte envelope");
        assert_eq!(
            u32::from_le_bytes(wire[0..4].try_into().unwrap()),
            BACKEND_BRIDGE_MAGIC_V1
        );
        assert_eq!(u32::from_le_bytes(wire[4..8].try_into().unwrap()), 1);
        assert_eq!(i32::from_le_bytes(wire[8..12].try_into().unwrap()), 0);
        assert_eq!(u32::from_le_bytes(wire[12..16].try_into().unwrap()), 2);
        assert_eq!(u64::from_le_bytes(wire[16..24].try_into().unwrap()), 9);
        assert_eq!(u64::from_le_bytes(wire[24..32].try_into().unwrap()), 18);
        assert_eq!(&wire[32..41], b"object-ok");
        assert_eq!(&wire[41..], b"fixture-diagnostic");
        let _ = std::fs::remove_file(output);
    }

    #[test]
    fn f64_bits_boundary_preserves_float_and_int_but_propagates_wrappers_as_errors() {
        let float = spl_f64_to_bits(&[Value::Float(0.1)]).expect("float boundary");
        assert_eq!(float, Value::Int(0.1f64.to_bits() as i64));

        let integer = spl_f64_to_bits(&[Value::Int(7)]).expect("integer boundary");
        assert_eq!(integer, Value::Int((7.0f64).to_bits() as i64));

        let wrapped = Value::Enum {
            enum_name: "Fixture".to_string(),
            variant: "Number".to_string(),
            payload: Some(Box::new(Value::Float(0.1))),
        };
        assert!(spl_f64_to_bits(&[wrapped]).is_err());
        assert!(spl_f64_to_bits(&[Value::Nil]).is_err());
    }

    #[cfg(unix)]
    #[test]
    fn backend_plugin_bridge_runs_real_v1_fixture_and_packs_canonical_envelope() {
        let repo = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../..");
        let fixture = repo.join("test/01_unit/compiler/backend_plugin/fixtures/backend_plugin_v1_fixture.c");
        let abi = repo.join("src/compiler/70.backend/backend_plugin/abi");
        let output = std::env::temp_dir().join(format!("simple-backend-plugin-v1-{}.so", std::process::id()));
        let status = std::process::Command::new("cc")
            .args(["-std=c11", "-fPIC", "-shared", "-I"])
            .arg(&abi)
            .arg(&fixture)
            .arg("-o")
            .arg(&output)
            .status()
            .expect("compile real backend plugin fixture");
        assert!(status.success());

        let mut request = Vec::new();
        request.extend_from_slice(&1u32.to_le_bytes());
        request.extend_from_slice(&2u32.to_le_bytes());
        request.extend_from_slice(&2u64.to_le_bytes());
        let result = spl_backend_plugin_run_v1(&[
            Value::byte_array(output.as_os_str().as_encoded_bytes().to_vec()),
            Value::byte_array(request),
            Value::byte_array(vec![1, 2, 3, 4]),
        ])
        .expect("interpreter bridge result");
        let wire = result.byte_array_view().expect("packed byte envelope");
        assert_eq!(
            u32::from_le_bytes(wire[0..4].try_into().unwrap()),
            BACKEND_BRIDGE_MAGIC_V1
        );
        assert_eq!(u32::from_le_bytes(wire[4..8].try_into().unwrap()), 1);
        assert_eq!(i32::from_le_bytes(wire[8..12].try_into().unwrap()), 0);
        assert_eq!(u32::from_le_bytes(wire[12..16].try_into().unwrap()), 2);
        assert_eq!(u64::from_le_bytes(wire[16..24].try_into().unwrap()), 9);
        assert_eq!(u64::from_le_bytes(wire[24..32].try_into().unwrap()), 18);
        assert_eq!(&wire[32..41], b"object-ok");
        assert_eq!(&wire[41..], b"fixture-diagnostic");
        let _ = std::fs::remove_file(output);
    }
}
