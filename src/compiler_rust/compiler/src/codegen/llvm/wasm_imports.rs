//! WASI (WebAssembly System Interface) import declarations for LLVM backend
//!
//! This module provides WASI syscall declarations for wasm32-wasi targets.
//! WASI is a POSIX-like interface that allows WebAssembly modules to interact
//! with the host system for file I/O, environment variables, arguments, etc.
//!
//! Reference: https://github.com/WebAssembly/WASI/blob/main/legacy/preview1/docs.md

use crate::error::{codes, CompileError, ErrorContext};

#[cfg(feature = "llvm")]
use inkwell::module::Module;
#[cfg(feature = "llvm")]
use inkwell::AddressSpace;

/// WASI import module name
pub const WASI_MODULE_NAME: &str = "wasi_snapshot_preview1";

/// WASI errno type (u16)
pub type WasiErrno = u16;

/// WASI file descriptor type (u32)
pub type WasiFd = u32;

/// WASI pointer type (u32 for wasm32)
pub type WasiPtr = u32;

/// WASI size type (u32 for wasm32)
pub type WasiSize = u32;

/// WASI file size type (u64)
pub type WasiFilesize = u64;

/// WASI timestamp type (u64 nanoseconds since epoch)
pub type WasiTimestamp = u64;

/// WASI clock ID type
pub type WasiClockid = u32;

/// Clock IDs for clock_time_get
#[allow(dead_code)]
pub mod clock_id {
    use super::WasiClockid;

    /// Realtime clock (wall clock time)
    pub const REALTIME: WasiClockid = 0;

    /// Monotonic clock (time since arbitrary point)
    pub const MONOTONIC: WasiClockid = 1;

    /// Process CPU time
    pub const PROCESS_CPUTIME: WasiClockid = 2;

    /// Thread CPU time
    pub const THREAD_CPUTIME: WasiClockid = 3;
}

/// Standard file descriptors
#[allow(dead_code)]
pub mod fd {
    use super::WasiFd;

    /// Standard input
    pub const STDIN: WasiFd = 0;

    /// Standard output
    pub const STDOUT: WasiFd = 1;

    /// Standard error
    pub const STDERR: WasiFd = 2;
}

/// Declare WASI imports in an LLVM module
///
/// This function adds external function declarations for all WASI syscalls
/// to the LLVM module when compiling for wasm32-wasi target.
#[cfg(feature = "llvm")]
pub fn declare_wasi_imports(module: &Module) -> Result<(), CompileError> {
    let context = module.get_context();
    let i32_type = context.i32_type();
    let i64_type = context.i64_type();
    let ptr_type = context.ptr_type(AddressSpace::default());

    // ===== File I/O Functions =====

    // fd_write: Write to a file descriptor
    // i32 fd_write(fd: i32, iovs: *const iovec, iovs_len: i32, nwritten: *mut i32) -> errno
    let fd_write_type = i32_type.fn_type(
        &[
            i32_type.into(), // fd
            ptr_type.into(), // iovs (array of iovec)
            i32_type.into(), // iovs_len
            ptr_type.into(), // nwritten (out param)
        ],
        false,
    );
    module.add_function("fd_write", fd_write_type, None);

    // fd_read: Read from a file descriptor
    // i32 fd_read(fd: i32, iovs: *const iovec, iovs_len: i32, nread: *mut i32) -> errno
    let fd_read_type = i32_type.fn_type(
        &[
            i32_type.into(), // fd
            ptr_type.into(), // iovs (array of iovec)
            i32_type.into(), // iovs_len
            ptr_type.into(), // nread (out param)
        ],
        false,
    );
    module.add_function("fd_read", fd_read_type, None);

    // fd_close: Close a file descriptor
    // i32 fd_close(fd: i32) -> errno
    let fd_close_type = i32_type.fn_type(&[i32_type.into()], false);
    module.add_function("fd_close", fd_close_type, None);

    // fd_seek: Seek in a file
    // i32 fd_seek(fd: i32, offset: i64, whence: i32, newoffset: *mut i64) -> errno
    let fd_seek_type = i32_type.fn_type(
        &[
            i32_type.into(), // fd
            i64_type.into(), // offset
            i32_type.into(), // whence
            ptr_type.into(), // newoffset (out param)
        ],
        false,
    );
    module.add_function("fd_seek", fd_seek_type, None);

    // fd_prestat_get: Get file descriptor pre-opened directory info
    // i32 fd_prestat_get(fd: i32, prestat: *mut prestat) -> errno
    let fd_prestat_get_type = i32_type.fn_type(&[i32_type.into(), ptr_type.into()], false);
    module.add_function("fd_prestat_get", fd_prestat_get_type, None);

    // fd_prestat_dir_name: Get pre-opened directory name
    // i32 fd_prestat_dir_name(fd: i32, path: *mut u8, path_len: i32) -> errno
    let fd_prestat_dir_name_type = i32_type.fn_type(
        &[
            i32_type.into(), // fd
            ptr_type.into(), // path buffer
            i32_type.into(), // path_len
        ],
        false,
    );
    module.add_function("fd_prestat_dir_name", fd_prestat_dir_name_type, None);

    // ===== Environment & Arguments =====

    // environ_sizes_get: Get environment variable sizes
    // i32 environ_sizes_get(count: *mut i32, buf_size: *mut i32) -> errno
    let environ_sizes_get_type = i32_type.fn_type(&[ptr_type.into(), ptr_type.into()], false);
    module.add_function("environ_sizes_get", environ_sizes_get_type, None);

    // environ_get: Get environment variables
    // i32 environ_get(environ: *mut *mut u8, environ_buf: *mut u8) -> errno
    let environ_get_type = i32_type.fn_type(&[ptr_type.into(), ptr_type.into()], false);
    module.add_function("environ_get", environ_get_type, None);

    // args_sizes_get: Get command-line argument sizes
    // i32 args_sizes_get(count: *mut i32, buf_size: *mut i32) -> errno
    let args_sizes_get_type = i32_type.fn_type(&[ptr_type.into(), ptr_type.into()], false);
    module.add_function("args_sizes_get", args_sizes_get_type, None);

    // args_get: Get command-line arguments
    // i32 args_get(argv: *mut *mut u8, argv_buf: *mut u8) -> errno
    let args_get_type = i32_type.fn_type(&[ptr_type.into(), ptr_type.into()], false);
    module.add_function("args_get", args_get_type, None);

    // ===== Process Control =====

    // proc_exit: Exit the process
    // void proc_exit(exit_code: i32) -> !
    let proc_exit_type = context.void_type().fn_type(&[i32_type.into()], false);
    module.add_function("proc_exit", proc_exit_type, None);

    // ===== Time & Random =====

    // clock_time_get: Get current time
    // i32 clock_time_get(clock_id: i32, precision: i64, timestamp: *mut i64) -> errno
    let clock_time_get_type = i32_type.fn_type(
        &[
            i32_type.into(), // clock_id
            i64_type.into(), // precision
            ptr_type.into(), // timestamp (out param)
        ],
        false,
    );
    module.add_function("clock_time_get", clock_time_get_type, None);

    // random_get: Get random bytes
    // i32 random_get(buf: *mut u8, buf_len: i32) -> errno
    let random_get_type = i32_type.fn_type(&[ptr_type.into(), i32_type.into()], false);
    module.add_function("random_get", random_get_type, None);

    // ===== Path Operations =====

    // path_open: Open a file or directory
    // i32 path_open(
    //     dirfd: i32,
    //     dirflags: i32,
    //     path: *const u8,
    //     path_len: i32,
    //     oflags: i32,
    //     fs_rights_base: i64,
    //     fs_rights_inheriting: i64,
    //     fdflags: i32,
    //     opened_fd: *mut i32
    // ) -> errno
    let path_open_type = i32_type.fn_type(
        &[
            i32_type.into(), // dirfd
            i32_type.into(), // dirflags
            ptr_type.into(), // path
            i32_type.into(), // path_len
            i32_type.into(), // oflags
            i64_type.into(), // fs_rights_base
            i64_type.into(), // fs_rights_inheriting
            i32_type.into(), // fdflags
            ptr_type.into(), // opened_fd (out param)
        ],
        false,
    );
    module.add_function("path_open", path_open_type, None);

    // path_filestat_get: Get file metadata
    // i32 path_filestat_get(fd: i32, flags: i32, path: *const u8, path_len: i32, filestat: *mut filestat) -> errno
    let path_filestat_get_type = i32_type.fn_type(
        &[
            i32_type.into(), // fd
            i32_type.into(), // flags
            ptr_type.into(), // path
            i32_type.into(), // path_len
            ptr_type.into(), // filestat (out param)
        ],
        false,
    );
    module.add_function("path_filestat_get", path_filestat_get_type, None);

    // path_remove_directory: Remove a directory
    // i32 path_remove_directory(fd: i32, path: *const u8, path_len: i32) -> errno
    let path_remove_directory_type = i32_type.fn_type(
        &[
            i32_type.into(), // fd
            ptr_type.into(), // path
            i32_type.into(), // path_len
        ],
        false,
    );
    module.add_function("path_remove_directory", path_remove_directory_type, None);

    // path_unlink_file: Unlink a file
    // i32 path_unlink_file(fd: i32, path: *const u8, path_len: i32) -> errno
    let path_unlink_file_type = i32_type.fn_type(
        &[
            i32_type.into(), // fd
            ptr_type.into(), // path
            i32_type.into(), // path_len
        ],
        false,
    );
    module.add_function("path_unlink_file", path_unlink_file_type, None);

    Ok(())
}

#[cfg(not(feature = "llvm"))]
pub fn declare_wasi_imports(_module: &()) -> Result<(), CompileError> {
    let ctx = ErrorContext::new()
        .with_code(codes::UNSUPPORTED_FEATURE)
        .with_help("Enable LLVM support by building with --features llvm");
    Err(CompileError::semantic_with_context(
        "LLVM feature not enabled for WASI imports".to_string(),
        ctx,
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_clock_id_constants() {
        assert_eq!(clock_id::REALTIME, 0);
        assert_eq!(clock_id::MONOTONIC, 1);
        assert_eq!(clock_id::PROCESS_CPUTIME, 2);
        assert_eq!(clock_id::THREAD_CPUTIME, 3);
    }

    #[test]
    fn test_fd_constants() {
        assert_eq!(fd::STDIN, 0);
        assert_eq!(fd::STDOUT, 1);
        assert_eq!(fd::STDERR, 2);
    }

    #[test]
    fn test_wasi_module_name() {
        assert_eq!(WASI_MODULE_NAME, "wasi_snapshot_preview1");
    }

    #[test]
    #[cfg(feature = "llvm")]
    fn test_declare_wasi_imports() {
        use inkwell::context::Context;

        let context = Context::create();
        let module = context.create_module("test_wasi");

        // Declare WASI imports
        declare_wasi_imports(&module).unwrap();

        // Verify some key functions were declared
        assert!(module.get_function("fd_write").is_some());
        assert!(module.get_function("fd_read").is_some());
        assert!(module.get_function("fd_close").is_some());
        assert!(module.get_function("environ_get").is_some());
        assert!(module.get_function("args_get").is_some());
        assert!(module.get_function("proc_exit").is_some());
        assert!(module.get_function("clock_time_get").is_some());
        assert!(module.get_function("random_get").is_some());
        assert!(module.get_function("path_open").is_some());
    }
}
