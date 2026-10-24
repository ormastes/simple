//! Interpreter registrations for the direct Win64 ABI externs declared in
//! `src/lib/nogc_sync_mut/io/windows_process_owner_abi.spl`.
//!
//! The native link path admits these names (see `is_windows_system_prefix`
//! in the native project tooling), but the seed interpreter's extern
//! dispatch had no implementation for them, so any JIT/interpreter path
//! that reached `windows_pty_owner.spl` died with
//! "function not found: GetProcessHeap" once stub fallback was disabled.
//! This module implements every extern that ABI module declares with real
//! Win32 FFI, mirroring the raw `#[link(name = "kernel32")]` declaration
//! style already used by `pty.rs` in this directory. (The crate's
//! `windows-sys` dependency does not enable the `Win32_System_JobObjects`,
//! `Win32_Storage_FileSystem`, or `Win32_Security_Cryptography` features,
//! so those families are linked directly here instead.)
//!
//! Pointer-valued ABI slots are `i64` on the Simple side; DWORD/BOOL slots
//! are `u32`/`i32`. All numeric returns are delivered as `Value::Int` (the
//! interpreter's `as_int` accepts both `Int` and `UInt` arguments, and the
//! `.spl` side compares against `u32` literals numerically).

use crate::error::CompileError;
use crate::value::Value;

use std::os::raw::c_void;

type Handle = *mut c_void;

#[link(name = "kernel32")]
unsafe extern "system" {
    fn GetProcessHeap() -> Handle;
    fn GetModuleFileNameW(module: Handle, buffer: *mut u16, capacity: u32) -> u32;
    fn GlobalMemoryStatusEx(status: *mut c_void) -> i32;
    fn GetSystemTimes(idle: *mut i64, kernel: *mut i64, user: *mut i64) -> i32;
    fn HeapAlloc(heap: Handle, flags: u32, size: usize) -> *mut c_void;
    fn HeapFree(heap: Handle, flags: u32, allocation: *mut c_void) -> i32;
    fn CreateProcessW(
        application: *const u16,
        command_line: *mut u16,
        process_security: *mut c_void,
        thread_security: *mut c_void,
        inherit_handles: i32,
        flags: u32,
        environment: *mut c_void,
        directory: *const u16,
        startup_info: *mut c_void,
        process_info: *mut c_void,
    ) -> i32;
    fn CreateJobObjectW(attributes: *mut c_void, name: *const u16) -> Handle;
    fn SetInformationJobObject(job: Handle, kind: i32, information: *mut c_void, size: u32) -> i32;
    fn AssignProcessToJobObject(job: Handle, process: Handle) -> i32;
    fn ResumeThread(thread: Handle) -> u32;
    fn WaitForSingleObject(handle: Handle, milliseconds: u32) -> u32;
    fn TerminateJobObject(job: Handle, exit_code: u32) -> i32;
    fn TerminateProcess(process: Handle, exit_code: u32) -> i32;
    fn CloseHandle(handle: Handle) -> i32;
    fn GetExitCodeProcess(process: Handle, status: *mut u32) -> i32;
    fn QueryInformationJobObject(
        job: Handle,
        kind: i32,
        information: *mut c_void,
        size: u32,
        returned: *mut u32,
    ) -> i32;
    fn GetTickCount64() -> u64;
    fn Sleep(milliseconds: u32);
    fn CreateFileW(
        path: *const u16,
        access: u32,
        sharing: u32,
        security: *mut c_void,
        disposition: u32,
        attributes: u32,
        template_file: Handle,
    ) -> Handle;
    fn InitializeProcThreadAttributeList(attributes: *mut c_void, count: u32, flags: u32, size: *mut usize) -> i32;
    fn UpdateProcThreadAttribute(
        attributes: *mut c_void,
        flags: u32,
        kind: usize,
        value: *mut c_void,
        size: usize,
        previous: *mut c_void,
        returned: *mut usize,
    ) -> i32;
    fn DeleteProcThreadAttributeList(attributes: *mut c_void);
    fn GetLastError() -> u32;
    fn GetFileInformationByHandleEx(file: Handle, kind: i32, information: *mut c_void, size: u32) -> i32;
    fn ReadFile(file: Handle, buffer: *mut c_void, capacity: u32, count: *mut u32, overlapped: *mut c_void) -> i32;
    fn GetFinalPathNameByHandleW(handle: Handle, buffer: *mut u16, capacity: u32, flags: u32) -> u32;
    fn GetFileAttributesW(path: *const u16) -> u32;
}

#[link(name = "bcrypt")]
unsafe extern "system" {
    fn BCryptOpenAlgorithmProvider(
        provider: *mut c_void,
        algorithm: *const u16,
        implementation: *const u16,
        flags: u32,
    ) -> i32;
    fn BCryptCreateHash(
        provider: Handle,
        hash_out: *mut c_void,
        object_buffer: *mut c_void,
        object_size: u32,
        secret: *mut c_void,
        secret_size: u32,
        flags: u32,
    ) -> i32;
    fn BCryptHashData(hash: Handle, buffer: *const u8, count: u32, flags: u32) -> i32;
    fn BCryptFinishHash(hash: Handle, digest: *mut u8, digest_size: u32, flags: u32) -> i32;
    fn BCryptDestroyHash(hash: Handle) -> i32;
    fn BCryptCloseAlgorithmProvider(provider: Handle, flags: u32) -> i32;
}

/// Every extern name declared by `windows_process_owner_abi.spl`.
const NAMES: &[&str] = &[
    "GetProcessHeap",
    "GetModuleFileNameW",
    "GlobalMemoryStatusEx",
    "GetSystemTimes",
    "HeapAlloc",
    "HeapFree",
    "CreateProcessW",
    "CreateJobObjectW",
    "SetInformationJobObject",
    "AssignProcessToJobObject",
    "ResumeThread",
    "WaitForSingleObject",
    "TerminateJobObject",
    "TerminateProcess",
    "CloseHandle",
    "GetExitCodeProcess",
    "QueryInformationJobObject",
    "GetTickCount64",
    "Sleep",
    "CreateFileW",
    "InitializeProcThreadAttributeList",
    "UpdateProcThreadAttribute",
    "DeleteProcThreadAttributeList",
    "GetLastError",
    "GetFileInformationByHandleEx",
    "ReadFile",
    "BCryptOpenAlgorithmProvider",
    "BCryptCreateHash",
    "BCryptHashData",
    "BCryptFinishHash",
    "BCryptDestroyHash",
    "BCryptCloseAlgorithmProvider",
    // std.nogc_sync_mut.io.path_identity_abi (Windows branch): reached by the
    // same JIT interp-splice during native-build cache/path identity checks.
    "GetFinalPathNameByHandleW",
    "GetFileAttributesW",
];

/// True when `name` is one of the direct Win64 ABI externs this module implements.
pub fn is_supported_name(name: &str) -> bool {
    NAMES.contains(&name)
}

fn trace(name: &str, args: &[Value]) {
    if std::env::var_os("SIMPLE_WINDOWS_ABI_TRACE").is_some() {
        eprintln!("[windows-abi] {name} argc={} args={args:?}", args.len());
    }
}

fn arg_i64(args: &[Value], index: usize, func_name: &str) -> Result<i64, CompileError> {
    match args.get(index) {
        Some(value) => value.as_int(),
        None => Err(CompileError::semantic(format!(
            "{func_name}: expected at least {} argument(s), got {}",
            index + 1,
            args.len()
        ))),
    }
}

/// The `.spl` ABI passes optional pointers as literal `0`; map those to null
/// so the Win32 APIs see the conventional null pointer.
#[inline]
fn opt_ptr(value: i64) -> *mut c_void {
    if value == 0 {
        std::ptr::null_mut()
    } else {
        value as *mut c_void
    }
}

/// Dispatch a Win64 ABI extern by name against pre-evaluated argument values.
pub fn dispatch(name: &str, args: &[Value]) -> Result<Value, CompileError> {
    trace(name, args);
    match name {
        "GetProcessHeap" => Ok(Value::Int(unsafe { GetProcessHeap() } as i64)),
        "GetModuleFileNameW" => {
            let module = opt_ptr(arg_i64(args, 0, name)?);
            let buffer = opt_ptr(arg_i64(args, 1, name)?);
            let capacity = arg_i64(args, 2, name)? as u32;
            Ok(Value::Int(unsafe {
                GetModuleFileNameW(module, buffer.cast(), capacity)
            } as i64))
        }
        "GlobalMemoryStatusEx" => {
            let status = opt_ptr(arg_i64(args, 0, name)?);
            Ok(Value::Int(unsafe { GlobalMemoryStatusEx(status) } as i64))
        }
        "GetSystemTimes" => {
            let idle = opt_ptr(arg_i64(args, 0, name)?);
            let kernel = opt_ptr(arg_i64(args, 1, name)?);
            let user = opt_ptr(arg_i64(args, 2, name)?);
            Ok(Value::Int(unsafe {
                GetSystemTimes(idle.cast(), kernel.cast(), user.cast())
            } as i64))
        }
        "HeapAlloc" => {
            let heap = opt_ptr(arg_i64(args, 0, name)?);
            let flags = arg_i64(args, 1, name)? as u32;
            let size = arg_i64(args, 2, name)? as u64 as usize;
            Ok(Value::Int(unsafe { HeapAlloc(heap, flags, size) } as i64))
        }
        "HeapFree" => {
            let heap = opt_ptr(arg_i64(args, 0, name)?);
            let flags = arg_i64(args, 1, name)? as u32;
            let allocation = opt_ptr(arg_i64(args, 2, name)?);
            Ok(Value::Int(unsafe { HeapFree(heap, flags, allocation) } as i64))
        }
        "CreateProcessW" => {
            let application = opt_ptr(arg_i64(args, 0, name)?);
            let command_line = opt_ptr(arg_i64(args, 1, name)?);
            let process_security = opt_ptr(arg_i64(args, 2, name)?);
            let thread_security = opt_ptr(arg_i64(args, 3, name)?);
            let inherit_handles = arg_i64(args, 4, name)? as i32;
            let flags = arg_i64(args, 5, name)? as u32;
            let environment = opt_ptr(arg_i64(args, 6, name)?);
            let directory = opt_ptr(arg_i64(args, 7, name)?);
            let startup_info = opt_ptr(arg_i64(args, 8, name)?);
            let process_info = opt_ptr(arg_i64(args, 9, name)?);
            // The caller-owned STARTUPINFOW/STARTUPINFOEXW and
            // PROCESS_INFORMATION buffers are sized and initialized on the
            // Simple side (see windows_pty_owner.spl / the abi proof); this
            // call only forwards their addresses, exactly as the pty lane
            // does for its own stack-allocated copies.
            Ok(Value::Int(unsafe {
                CreateProcessW(
                    application.cast(),
                    command_line.cast(),
                    process_security,
                    thread_security,
                    inherit_handles,
                    flags,
                    environment,
                    directory.cast(),
                    startup_info,
                    process_info,
                )
            } as i64))
        }
        "CreateJobObjectW" => {
            let attributes = opt_ptr(arg_i64(args, 0, name)?);
            let name_ptr = opt_ptr(arg_i64(args, 1, name)?);
            Ok(Value::Int(unsafe { CreateJobObjectW(attributes, name_ptr.cast()) } as i64))
        }
        "SetInformationJobObject" => {
            let job = opt_ptr(arg_i64(args, 0, name)?);
            let kind = arg_i64(args, 1, name)? as i32;
            let information = opt_ptr(arg_i64(args, 2, name)?);
            let size = arg_i64(args, 3, name)? as u32;
            Ok(Value::Int(unsafe { SetInformationJobObject(job, kind, information, size) } as i64))
        }
        "AssignProcessToJobObject" => {
            let job = opt_ptr(arg_i64(args, 0, name)?);
            let process = opt_ptr(arg_i64(args, 1, name)?);
            Ok(Value::Int(unsafe { AssignProcessToJobObject(job, process) } as i64))
        }
        "ResumeThread" => {
            let thread = opt_ptr(arg_i64(args, 0, name)?);
            Ok(Value::Int(unsafe { ResumeThread(thread) } as i64))
        }
        "WaitForSingleObject" => {
            let handle = opt_ptr(arg_i64(args, 0, name)?);
            let milliseconds = arg_i64(args, 1, name)? as u32;
            Ok(Value::Int(unsafe { WaitForSingleObject(handle, milliseconds) } as i64))
        }
        "TerminateJobObject" => {
            let job = opt_ptr(arg_i64(args, 0, name)?);
            let exit_code = arg_i64(args, 1, name)? as u32;
            Ok(Value::Int(unsafe { TerminateJobObject(job, exit_code) } as i64))
        }
        "TerminateProcess" => {
            let process = opt_ptr(arg_i64(args, 0, name)?);
            let exit_code = arg_i64(args, 1, name)? as u32;
            Ok(Value::Int(unsafe { TerminateProcess(process, exit_code) } as i64))
        }
        "CloseHandle" => {
            let handle = opt_ptr(arg_i64(args, 0, name)?);
            Ok(Value::Int(unsafe { CloseHandle(handle) } as i64))
        }
        "GetExitCodeProcess" => {
            let process = opt_ptr(arg_i64(args, 0, name)?);
            let status = opt_ptr(arg_i64(args, 1, name)?);
            Ok(Value::Int(unsafe { GetExitCodeProcess(process, status.cast()) } as i64))
        }
        "QueryInformationJobObject" => {
            let job = opt_ptr(arg_i64(args, 0, name)?);
            let kind = arg_i64(args, 1, name)? as i32;
            let information = opt_ptr(arg_i64(args, 2, name)?);
            let size = arg_i64(args, 3, name)? as u32;
            let returned = opt_ptr(arg_i64(args, 4, name)?);
            Ok(Value::Int(unsafe {
                QueryInformationJobObject(job, kind, information, size, returned.cast())
            } as i64))
        }
        "GetTickCount64" => Ok(Value::Int(unsafe { GetTickCount64() } as i64)),
        "Sleep" => {
            let milliseconds = arg_i64(args, 0, name)? as u32;
            unsafe { Sleep(milliseconds) };
            Ok(Value::Nil)
        }
        "CreateFileW" => {
            let path = opt_ptr(arg_i64(args, 0, name)?);
            let access = arg_i64(args, 1, name)? as u32;
            let sharing = arg_i64(args, 2, name)? as u32;
            let security = opt_ptr(arg_i64(args, 3, name)?);
            let disposition = arg_i64(args, 4, name)? as u32;
            let attributes = arg_i64(args, 5, name)? as u32;
            let template_file = opt_ptr(arg_i64(args, 6, name)?);
            Ok(Value::Int(unsafe {
                CreateFileW(
                    path.cast(),
                    access,
                    sharing,
                    security,
                    disposition,
                    attributes,
                    template_file,
                )
            } as i64))
        }
        "InitializeProcThreadAttributeList" => {
            let attributes = opt_ptr(arg_i64(args, 0, name)?);
            let count = arg_i64(args, 1, name)? as u32;
            let flags = arg_i64(args, 2, name)? as u32;
            let size = opt_ptr(arg_i64(args, 3, name)?);
            Ok(Value::Int(unsafe { InitializeProcThreadAttributeList(attributes, count, flags, size.cast()) } as i64))
        }
        "UpdateProcThreadAttribute" => {
            let attributes = opt_ptr(arg_i64(args, 0, name)?);
            let flags = arg_i64(args, 1, name)? as u32;
            let kind = arg_i64(args, 2, name)? as u64 as usize;
            let value = opt_ptr(arg_i64(args, 3, name)?);
            let size = arg_i64(args, 4, name)? as u64 as usize;
            let previous = opt_ptr(arg_i64(args, 5, name)?);
            let returned = opt_ptr(arg_i64(args, 6, name)?);
            Ok(Value::Int(unsafe {
                UpdateProcThreadAttribute(attributes, flags, kind, value, size, previous, returned.cast())
            } as i64))
        }
        "DeleteProcThreadAttributeList" => {
            let attributes = opt_ptr(arg_i64(args, 0, name)?);
            unsafe { DeleteProcThreadAttributeList(attributes) };
            Ok(Value::Nil)
        }
        "GetLastError" => Ok(Value::Int(unsafe { GetLastError() } as i64)),
        "GetFinalPathNameByHandleW" => {
            let handle = opt_ptr(arg_i64(args, 0, name)?);
            let buffer = opt_ptr(arg_i64(args, 1, name)?);
            let capacity = arg_i64(args, 2, name)? as u32;
            let flags = arg_i64(args, 3, name)? as u32;
            Ok(Value::Int(unsafe { GetFinalPathNameByHandleW(handle, buffer.cast(), capacity, flags) } as i64))
        }
        "GetFileInformationByHandleEx" => {
            let file = opt_ptr(arg_i64(args, 0, name)?);
            let kind = arg_i64(args, 1, name)? as i32;
            let information = opt_ptr(arg_i64(args, 2, name)?);
            let size = arg_i64(args, 3, name)? as u32;
            Ok(Value::Int(unsafe { GetFileInformationByHandleEx(file, kind, information, size) } as i64))
        }
        "ReadFile" => {
            let file = opt_ptr(arg_i64(args, 0, name)?);
            let buffer = opt_ptr(arg_i64(args, 1, name)?);
            let capacity = arg_i64(args, 2, name)? as u32;
            let count = opt_ptr(arg_i64(args, 3, name)?);
            let overlapped = opt_ptr(arg_i64(args, 4, name)?);
            Ok(Value::Int(unsafe { ReadFile(file, buffer, capacity, count.cast(), overlapped) } as i64))
        }
        "GetFileAttributesW" => {
            let path = opt_ptr(arg_i64(args, 0, name)?);
            Ok(Value::Int(unsafe { GetFileAttributesW(path.cast()) } as i64))
        }
        "BCryptOpenAlgorithmProvider" => {
            let provider = opt_ptr(arg_i64(args, 0, name)?);
            let algorithm = opt_ptr(arg_i64(args, 1, name)?);
            let implementation = opt_ptr(arg_i64(args, 2, name)?);
            let flags = arg_i64(args, 3, name)? as u32;
            Ok(Value::Int(unsafe {
                BCryptOpenAlgorithmProvider(provider, algorithm.cast(), implementation.cast(), flags)
            } as i64))
        }
        "BCryptCreateHash" => {
            let provider = opt_ptr(arg_i64(args, 0, name)?);
            let hash_out = opt_ptr(arg_i64(args, 1, name)?);
            let object_buffer = opt_ptr(arg_i64(args, 2, name)?);
            let object_size = arg_i64(args, 3, name)? as u32;
            let secret = opt_ptr(arg_i64(args, 4, name)?);
            let secret_size = arg_i64(args, 5, name)? as u32;
            let flags = arg_i64(args, 6, name)? as u32;
            Ok(Value::Int(unsafe {
                BCryptCreateHash(provider, hash_out, object_buffer, object_size, secret, secret_size, flags)
            } as i64))
        }
        "BCryptHashData" => {
            let hash = opt_ptr(arg_i64(args, 0, name)?);
            let buffer = opt_ptr(arg_i64(args, 1, name)?);
            let count = arg_i64(args, 2, name)? as u32;
            let flags = arg_i64(args, 3, name)? as u32;
            Ok(Value::Int(unsafe { BCryptHashData(hash, buffer.cast(), count, flags) } as i64))
        }
        "BCryptFinishHash" => {
            let hash = opt_ptr(arg_i64(args, 0, name)?);
            let digest = opt_ptr(arg_i64(args, 1, name)?);
            let digest_size = arg_i64(args, 2, name)? as u32;
            let flags = arg_i64(args, 3, name)? as u32;
            Ok(Value::Int(unsafe { BCryptFinishHash(hash, digest.cast(), digest_size, flags) } as i64))
        }
        "BCryptDestroyHash" => {
            let hash = opt_ptr(arg_i64(args, 0, name)?);
            Ok(Value::Int(unsafe { BCryptDestroyHash(hash) } as i64))
        }
        "BCryptCloseAlgorithmProvider" => {
            let provider = opt_ptr(arg_i64(args, 0, name)?);
            let flags = arg_i64(args, 1, name)? as u32;
            Ok(Value::Int(unsafe { BCryptCloseAlgorithmProvider(provider, flags) } as i64))
        }
        _ => Err(CompileError::semantic(format!("unknown Win64 ABI extern: {name}"))),
    }
}
