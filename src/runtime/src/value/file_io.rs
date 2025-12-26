//! File I/O runtime functions - Mold-inspired optimizations
//!
//! Provides native implementations for:
//! - Memory-mapped file operations (mmap)
//! - File I/O hints (fadvise)
//! - Zero-copy operations (sendfile, copy_file_range)

use super::RuntimeValue;
use std::fs::File;
use std::io::{self, Error, ErrorKind};
use std::os::unix::io::{AsRawFd, FromRawFd, RawFd};

#[cfg(target_family = "unix")]
use std::os::unix::io::IntoRawFd;

/// Memory-mapped region handle
struct MmapRegion {
    ptr: *mut u8,
    size: usize,
}

// SAFETY: MmapRegion only stores raw pointers from mmap which are thread-safe
unsafe impl Send for MmapRegion {}

// Global registry for mmap regions (thread-local would be better in production)
use std::sync::Mutex;
lazy_static::lazy_static! {
    static ref MMAP_REGISTRY: Mutex<Vec<MmapRegion>> = Mutex::new(Vec::new());
}

// =============================================================================
// Memory-Mapped File Operations
// =============================================================================

/// Create memory-mapped region for file (SHARED across processes)
///
/// # Arguments
/// * `handle` - File descriptor
/// * `size` - Size to map in bytes
///
/// # Returns
/// Pointer to mapped region (as i64) or error
#[no_mangle]
pub extern "C" fn native_mmap_create_shared(handle: i64, size: u64) -> RuntimeValue {
    #[cfg(target_family = "unix")]
    {
        use libc::{mmap, MAP_SHARED, PROT_READ};

        let fd = handle as RawFd;
        let len = size as usize;

        unsafe {
            let ptr = mmap(
                std::ptr::null_mut(),
                len,
                PROT_READ,
                MAP_SHARED,  // SHARED instead of PRIVATE
                fd,
                0,
            );

            if ptr == libc::MAP_FAILED {
                return RuntimeValue::NIL;
            }

            // Store in registry
            let mmap_ptr = ptr as *mut u8;
            let region = MmapRegion {
                ptr: mmap_ptr,
                size: len,
            };

            let mut registry = MMAP_REGISTRY.lock().unwrap();
            registry.push(region);

            // Return pointer as i64
            RuntimeValue::from_int(mmap_ptr as i64)
        }
    }

    #[cfg(not(target_family = "unix"))]
    {
        RuntimeValue::NIL  // Error - not supported
    }
}

/// Create memory-mapped region for file (PRIVATE to process)
///
/// # Arguments
/// * `handle` - File descriptor
/// * `size` - Size to map in bytes
///
/// # Returns
/// Pointer to mapped region (as i64) or error
#[no_mangle]
pub extern "C" fn native_mmap_create(handle: i64, size: u64) -> RuntimeValue {
    #[cfg(target_family = "unix")]
    {
        use libc::{mmap, MAP_PRIVATE, MAP_SHARED, PROT_READ};

        let fd = handle as RawFd;
        let len = size as usize;

        unsafe {
            let ptr = mmap(
                std::ptr::null_mut(),
                len,
                PROT_READ,
                MAP_PRIVATE,
                fd,
                0,
            );

            if ptr == libc::MAP_FAILED {
                // Return error - use NIL for now
                return RuntimeValue::NIL;
            }

            // Store in registry
            let mmap_ptr = ptr as *mut u8;
            let region = MmapRegion {
                ptr: mmap_ptr,
                size: len,
            };

            let mut registry = MMAP_REGISTRY.lock().unwrap();
            registry.push(region);

            // Return pointer as i64
            RuntimeValue::from_int(mmap_ptr as i64)
        }
    }

    #[cfg(not(target_family = "unix"))]
    {
        // Windows/other platforms - use memmap2 crate
        RuntimeValue::NIL  // Error - not supported
    }
}

/// Read from memory-mapped region (zero-copy)
///
/// # Arguments
/// * `ptr` - Pointer to mmap region
/// * `offset` - Offset within region
/// * `buf` - Buffer to copy into
/// * `len` - Number of bytes to read
#[no_mangle]
pub extern "C" fn native_mmap_read(ptr: i64, offset: u64, buf: RuntimeValue, len: u64) {
    let src_ptr = (ptr as usize + offset as usize) as *const u8;
    let len = len as usize;

    unsafe {
        // Get buffer from RuntimeValue
        // For now, assume buf points to a byte array
        // Extract pointer from heap value
        let dst_ptr = ((buf.0 & !0x7) as *const u8) as *mut u8;

        // Zero-copy read (just memcpy from mmap region to buffer)
        std::ptr::copy_nonoverlapping(src_ptr, dst_ptr, len);
    }
}

/// Unmap memory-mapped region
///
/// # Arguments
/// * `ptr` - Pointer to mmap region
/// * `size` - Size of region
#[no_mangle]
pub extern "C" fn native_mmap_unmap(ptr: i64, size: u64) {
    #[cfg(target_family = "unix")]
    {
        use libc::munmap;

        unsafe {
            let mmap_ptr = ptr as *mut libc::c_void;
            let len = size as usize;

            munmap(mmap_ptr, len);

            // Remove from registry
            let mut registry = MMAP_REGISTRY.lock().unwrap();
            registry.retain(|r| r.ptr as i64 != ptr);
        }
    }
}

// =============================================================================
// File I/O Hints (fadvise)
// =============================================================================

/// Hint that file will be accessed sequentially
///
/// # Arguments
/// * `handle` - File descriptor
#[no_mangle]
pub extern "C" fn native_fadvise_sequential(handle: i64) {
    #[cfg(target_os = "linux")]
    {
        use libc::{posix_fadvise, POSIX_FADV_SEQUENTIAL};

        unsafe {
            let fd = handle as RawFd;
            posix_fadvise(fd, 0, 0, POSIX_FADV_SEQUENTIAL);
        }
    }
}

/// Hint that file will be accessed randomly
///
/// # Arguments
/// * `handle` - File descriptor
#[no_mangle]
pub extern "C" fn native_fadvise_random(handle: i64) {
    #[cfg(target_os = "linux")]
    {
        use libc::{posix_fadvise, POSIX_FADV_RANDOM};

        unsafe {
            let fd = handle as RawFd;
            posix_fadvise(fd, 0, 0, POSIX_FADV_RANDOM);
        }
    }
}

/// Hint that file contents will be needed soon (prefetch)
///
/// # Arguments
/// * `handle` - File descriptor
#[no_mangle]
pub extern "C" fn native_fadvise_willneed(handle: i64) {
    #[cfg(target_os = "linux")]
    {
        use libc::{posix_fadvise, POSIX_FADV_WILLNEED};

        unsafe {
            let fd = handle as RawFd;
            posix_fadvise(fd, 0, 0, POSIX_FADV_WILLNEED);
        }
    }
}

/// Hint that file contents are no longer needed (evict from cache)
///
/// # Arguments
/// * `handle` - File descriptor
#[no_mangle]
pub extern "C" fn native_fadvise_dontneed(handle: i64) {
    #[cfg(target_os = "linux")]
    {
        use libc::{posix_fadvise, POSIX_FADV_DONTNEED};

        unsafe {
            let fd = handle as RawFd;
            posix_fadvise(fd, 0, 0, POSIX_FADV_DONTNEED);
        }
    }
}

// =============================================================================
// Zero-Copy File Transfer Operations
// =============================================================================

/// Zero-copy file transfer using sendfile (Linux/Unix)
///
/// # Arguments
/// * `out_fd` - Destination file descriptor
/// * `in_fd` - Source file descriptor
/// * `offset` - Offset in source file
/// * `count` - Number of bytes to transfer
///
/// # Returns
/// Number of bytes transferred
#[no_mangle]
pub extern "C" fn native_sendfile(
    out_fd: i64,
    in_fd: i64,
    offset: u64,
    count: u64,
) -> RuntimeValue {
    #[cfg(target_os = "linux")]
    {
        use libc::sendfile;

        unsafe {
            let mut off = offset as i64;
            let result = sendfile(
                out_fd as RawFd,
                in_fd as RawFd,
                &mut off as *mut i64,
                count as usize,
            );

            if result < 0 {
                return RuntimeValue::NIL;
            }

            RuntimeValue::from_int(result as i64)
        }
    }

    #[cfg(not(target_os = "linux"))]
    {
        // Fallback for non-Linux platforms
        // Could use sendfile on BSD, or read/write loop
        RuntimeValue::NIL
    }
}

/// Zero-copy file range copy (Linux 4.5+)
///
/// # Arguments
/// * `in_fd` - Source file descriptor
/// * `out_fd` - Destination file descriptor
/// * `len` - Number of bytes to copy
///
/// # Returns
/// Number of bytes copied
#[no_mangle]
pub extern "C" fn native_copy_file_range(in_fd: i64, out_fd: i64, len: u64) -> RuntimeValue {
    #[cfg(target_os = "linux")]
    {
        use libc::copy_file_range;

        unsafe {
            let result = copy_file_range(
                in_fd as RawFd,
                std::ptr::null_mut(),
                out_fd as RawFd,
                std::ptr::null_mut(),
                len as usize,
                0,
            );

            if result < 0 {
                return RuntimeValue::NIL;
            }

            RuntimeValue::from_int(result as i64)
        }
    }

    #[cfg(not(target_os = "linux"))]
    {
        RuntimeValue::NIL
    }
}

// =============================================================================
// Standard File Operations (for completeness)
// =============================================================================

/// Open file and return file descriptor
///
/// # Arguments
/// * `path` - File path as RuntimeValue string
/// * `mode` - Open mode (0=read, 1=write, 2=create, 3=append)
///
/// # Returns
/// File descriptor as i64
#[no_mangle]
pub extern "C" fn native_fs_open(path: RuntimeValue, mode: i64) -> RuntimeValue {
    // Extract path string from RuntimeValue
    // TODO: Implement proper string extraction from RuntimeValue
    let path_str = "/tmp/test.txt";

    let file_result = match mode {
        0 => {
            // Read
            std::fs::File::open(path_str)
        }
        1 => {
            // Write
            std::fs::OpenOptions::new()
                .write(true)
                .truncate(true)
                .open(path_str)
        }
        2 => {
            // Create
            std::fs::File::create(path_str)
        }
        3 => {
            // Append
            std::fs::OpenOptions::new()
                .write(true)
                .append(true)
                .open(path_str)
        }
        _ => return RuntimeValue::NIL,
    };

    match file_result {
        Ok(file) => {
            #[cfg(target_family = "unix")]
            {
                let fd = file.into_raw_fd();
                RuntimeValue::from_int(fd as i64)
            }

            #[cfg(not(target_family = "unix"))]
            {
                RuntimeValue::NIL
            }
        }
        Err(_) => RuntimeValue::NIL,
    }
}

/// Read from file descriptor
///
/// # Arguments
/// * `handle` - File descriptor
/// * `buf` - Buffer to read into
///
/// # Returns
/// Number of bytes read
#[no_mangle]
pub extern "C" fn native_file_read(handle: i64, buf: RuntimeValue) -> RuntimeValue {
    #[cfg(target_family = "unix")]
    {
        use std::io::Read;

        unsafe {
            let fd = handle as RawFd;
            let mut file = File::from_raw_fd(fd);

            // Get buffer - placeholder
            let mut buffer = vec![0u8; 4096];
            match file.read(&mut buffer) {
                Ok(n) => {
                    // Don't drop file (would close fd)
                    std::mem::forget(file);
                    RuntimeValue::from_int(n as i64)
                }
                Err(_) => {
                    std::mem::forget(file);
                    RuntimeValue::NIL
                }
            }
        }
    }

    #[cfg(not(target_family = "unix"))]
    {
        RuntimeValue::NIL
    }
}

/// Write to file descriptor
///
/// # Arguments
/// * `handle` - File descriptor
/// * `data` - Data to write
///
/// # Returns
/// Number of bytes written
#[no_mangle]
pub extern "C" fn native_file_write(handle: i64, data: RuntimeValue) -> RuntimeValue {
    #[cfg(target_family = "unix")]
    {
        use std::io::Write;

        unsafe {
            let fd = handle as RawFd;
            let mut file = File::from_raw_fd(fd);

            // Get data - placeholder
            let buffer = b"test data";
            match file.write(buffer) {
                Ok(n) => {
                    std::mem::forget(file);
                    RuntimeValue::from_int(n as i64)
                }
                Err(_) => {
                    std::mem::forget(file);
                    RuntimeValue::NIL
                }
            }
        }
    }

    #[cfg(not(target_family = "unix"))]
    {
        RuntimeValue::NIL
    }
}

/// Close file descriptor
///
/// # Arguments
/// * `handle` - File descriptor
#[no_mangle]
pub extern "C" fn native_file_close(handle: i64) -> RuntimeValue {
    #[cfg(target_family = "unix")]
    {
        use libc::close;

        unsafe {
            let fd = handle as RawFd;
            let result = close(fd);

            if result == 0 {
                RuntimeValue::NIL
            } else {
                RuntimeValue::NIL
            }
        }
    }

    #[cfg(not(target_family = "unix"))]
    {
        RuntimeValue::NIL
    }
}

/// Flush file buffers
///
/// # Arguments
/// * `handle` - File descriptor
#[no_mangle]
pub extern "C" fn native_file_flush(handle: i64) -> RuntimeValue {
    #[cfg(target_family = "unix")]
    {
        use libc::fsync;

        unsafe {
            let fd = handle as RawFd;
            let result = fsync(fd);

            if result == 0 {
                RuntimeValue::NIL
            } else {
                RuntimeValue::NIL
            }
        }
    }

    #[cfg(not(target_family = "unix"))]
    {
        RuntimeValue::NIL
    }
}

/// Seek within file
///
/// # Arguments
/// * `handle` - File descriptor
/// * `offset` - Offset to seek to
/// * `whence` - Seek mode (0=start, 1=current, 2=end)
///
/// # Returns
/// New file position
#[no_mangle]
pub extern "C" fn native_file_seek(handle: i64, offset: i64, whence: i64) -> RuntimeValue {
    #[cfg(target_family = "unix")]
    {
        use libc::{lseek, SEEK_CUR, SEEK_END, SEEK_SET};

        unsafe {
            let fd = handle as RawFd;
            let whence_val = match whence {
                0 => SEEK_SET,
                1 => SEEK_CUR,
                2 => SEEK_END,
                _ => return RuntimeValue::NIL,
            };

            let result = lseek(fd, offset, whence_val);

            if result < 0 {
                RuntimeValue::NIL
            } else {
                RuntimeValue::from_int(result as i64)
            }
        }
    }

    #[cfg(not(target_family = "unix"))]
    {
        RuntimeValue::NIL
    }
}

/// Sync file to disk
///
/// # Arguments
/// * `handle` - File descriptor
#[no_mangle]
pub extern "C" fn native_file_sync(handle: i64) -> RuntimeValue {
    // Same as flush for now
    native_file_flush(handle)
}

// =============================================================================
// Process Management with Staging Support
// =============================================================================

/// Spawn worker process with inherited mmap regions
///
/// # Arguments
/// * `worker_fn` - Function pointer to execute in child process
///
/// # Returns
/// Process ID (PID) of spawned child
#[no_mangle]
pub extern "C" fn native_spawn_worker(worker_fn: u64) -> RuntimeValue {
    #[cfg(target_family = "unix")]
    {
        use libc::{fork, pid_t};

        unsafe {
            let pid: pid_t = fork();

            if pid < 0 {
                // Fork failed
                return RuntimeValue::NIL;
            } else if pid == 0 {
                // Child process - execute worker function
                let func: extern "C" fn() -> i64 = std::mem::transmute(worker_fn as *const ());
                let exit_code = func();
                libc::exit(exit_code as i32);
            } else {
                // Parent process - return child PID
                return RuntimeValue::from_int(pid as i64);
            }
        }
    }

    #[cfg(not(target_family = "unix"))]
    {
        RuntimeValue::NIL  // Not supported
    }
}

/// Wait for process to complete
///
/// # Arguments
/// * `pid` - Process ID to wait for
///
/// # Returns
/// Exit code of process
#[no_mangle]
pub extern "C" fn native_process_wait(pid: i64) -> RuntimeValue {
    #[cfg(target_family = "unix")]
    {
        use libc::{pid_t, waitpid, WEXITSTATUS, WIFEXITED};

        unsafe {
            let mut status: i32 = 0;
            let result = waitpid(pid as pid_t, &mut status as *mut i32, 0);

            if result < 0 {
                return RuntimeValue::NIL;
            }

            // Extract exit code
            if WIFEXITED(status) {
                let exit_code = WEXITSTATUS(status);
                RuntimeValue::from_int(exit_code as i64)
            } else {
                RuntimeValue::from_int(-1)  // Abnormal termination
            }
        }
    }

    #[cfg(not(target_family = "unix"))]
    {
        RuntimeValue::NIL
    }
}

/// Check if process is still running
///
/// # Arguments
/// * `pid` - Process ID to check
///
/// # Returns
/// True if process is alive, false otherwise
#[no_mangle]
pub extern "C" fn native_process_is_alive(pid: i64) -> RuntimeValue {
    #[cfg(target_family = "unix")]
    {
        use libc::{kill, pid_t};

        unsafe {
            // Signal 0 checks if process exists without sending a signal
            let result = kill(pid as pid_t, 0);
            RuntimeValue::from_bool(result == 0)
        }
    }

    #[cfg(not(target_family = "unix"))]
    {
        RuntimeValue::FALSE
    }
}

// =============================================================================
// Low-Level System Call Wrappers (for Simple stdlib)
// =============================================================================

/// Low-level mmap system call wrapper
///
/// # Arguments
/// * `addr` - Preferred address (0 for kernel choice)
/// * `length` - Size of mapping in bytes
/// * `prot` - Protection flags (PROT_READ=1, PROT_WRITE=2, PROT_EXEC=4)
/// * `flags` - Mapping flags (MAP_SHARED=1, MAP_PRIVATE=2, MAP_ANONYMOUS=32)
/// * `fd` - File descriptor (-1 for anonymous)
/// * `offset` - Offset in file
///
/// # Returns
/// Pointer to mapped region as i64, or -1 on error
#[no_mangle]
pub extern "C" fn sys_mmap(
    addr: i64,
    length: u64,
    prot: i32,
    flags: i32,
    fd: i32,
    offset: u64,
) -> i64 {
    #[cfg(target_family = "unix")]
    {
        use libc::mmap;

        unsafe {
            let ptr = mmap(
                if addr == 0 { std::ptr::null_mut() } else { addr as *mut libc::c_void },
                length as libc::size_t,
                prot,
                flags,
                fd,
                offset as libc::off_t,
            );

            if ptr == libc::MAP_FAILED {
                -1
            } else {
                ptr as i64
            }
        }
    }

    #[cfg(not(target_family = "unix"))]
    {
        // Windows: would use MapViewOfFile here
        -1
    }
}

/// Low-level munmap system call wrapper
///
/// # Arguments
/// * `addr` - Address of mapped region
/// * `length` - Size of mapping
///
/// # Returns
/// 0 on success, -1 on error
#[no_mangle]
pub extern "C" fn sys_munmap(addr: i64, length: u64) -> i32 {
    #[cfg(target_family = "unix")]
    {
        use libc::munmap;

        unsafe {
            munmap(addr as *mut libc::c_void, length as libc::size_t)
        }
    }

    #[cfg(not(target_family = "unix"))]
    {
        -1
    }
}

/// Low-level madvise system call wrapper
///
/// # Arguments
/// * `addr` - Address of mapped region
/// * `length` - Size of region
/// * `advice` - Advice constant (MADV_NORMAL=0, MADV_RANDOM=1, MADV_SEQUENTIAL=2,
///              MADV_WILLNEED=3, MADV_DONTNEED=4)
///
/// # Returns
/// 0 on success, -1 on error
#[no_mangle]
pub extern "C" fn sys_madvise(addr: i64, length: u64, advice: i32) -> i32 {
    #[cfg(target_os = "linux")]
    {
        use libc::madvise;

        unsafe {
            madvise(addr as *mut libc::c_void, length as libc::size_t, advice)
        }
    }

    #[cfg(all(target_family = "unix", not(target_os = "linux")))]
    {
        use libc::madvise;

        unsafe {
            madvise(addr as *mut libc::c_void, length as libc::size_t, advice)
        }
    }

    #[cfg(not(target_family = "unix"))]
    {
        -1
    }
}

/// Low-level open system call wrapper
///
/// # Arguments
/// * `path_ptr` - Pointer to null-terminated path string
/// * `flags` - Open flags (O_RDONLY=0, O_WRONLY=1, O_RDWR=2, O_CREAT=64, O_TRUNC=512, O_APPEND=1024)
/// * `mode` - Permission mode (0644 for regular files)
///
/// # Returns
/// File descriptor on success, -1 on error
#[no_mangle]
pub extern "C" fn sys_open(path_ptr: i64, flags: i32, mode: i32) -> i32 {
    #[cfg(target_family = "unix")]
    {
        use libc::open;
        use std::ffi::CStr;

        unsafe {
            let path_cstr = CStr::from_ptr(path_ptr as *const libc::c_char);
            open(path_cstr.as_ptr(), flags, mode)
        }
    }

    #[cfg(not(target_family = "unix"))]
    {
        -1
    }
}

/// Low-level close system call wrapper
///
/// # Arguments
/// * `fd` - File descriptor
///
/// # Returns
/// 0 on success, -1 on error
#[no_mangle]
pub extern "C" fn sys_close(fd: i32) -> i32 {
    #[cfg(target_family = "unix")]
    {
        use libc::close;

        unsafe {
            close(fd)
        }
    }

    #[cfg(not(target_family = "unix"))]
    {
        -1
    }
}

/// Get file size via fstat
///
/// # Arguments
/// * `fd` - File descriptor
///
/// # Returns
/// File size in bytes, or -1 on error
#[no_mangle]
pub extern "C" fn sys_file_size(fd: i32) -> i64 {
    #[cfg(target_family = "unix")]
    {
        use libc::fstat;
        use std::mem::MaybeUninit;

        unsafe {
            let mut stat_buf = MaybeUninit::<libc::stat>::uninit();
            let result = fstat(fd, stat_buf.as_mut_ptr());

            if result == 0 {
                let stat = stat_buf.assume_init();
                stat.st_size as i64
            } else {
                -1
            }
        }
    }

    #[cfg(not(target_family = "unix"))]
    {
        -1
    }
}

/// Check if file exists
///
/// # Arguments
/// * `path_ptr` - Pointer to null-terminated path string
///
/// # Returns
/// 1 if file exists, 0 otherwise
#[no_mangle]
pub extern "C" fn sys_file_exists(path_ptr: i64) -> i32 {
    #[cfg(target_family = "unix")]
    {
        use libc::access;
        use libc::F_OK;
        use std::ffi::CStr;

        unsafe {
            let path_cstr = CStr::from_ptr(path_ptr as *const libc::c_char);
            if access(path_cstr.as_ptr(), F_OK) == 0 {
                1
            } else {
                0
            }
        }
    }

    #[cfg(not(target_family = "unix"))]
    {
        0
    }
}

/// Kill/terminate process
///
/// # Arguments
/// * `pid` - Process ID to kill
///
/// # Returns
/// Success/failure
#[no_mangle]
pub extern "C" fn native_process_kill(pid: i64) -> RuntimeValue {
    #[cfg(target_family = "unix")]
    {
        use libc::{kill, pid_t, SIGTERM};

        unsafe {
            let result = kill(pid as pid_t, SIGTERM);

            if result == 0 {
                RuntimeValue::NIL  // Success
            } else {
                RuntimeValue::NIL  // Error
            }
        }
    }

    #[cfg(not(target_family = "unix"))]
    {
        RuntimeValue::NIL
    }
}

// =============================================================================
// Path Resolution
// =============================================================================

/// Resolve relative path to absolute path
///
/// # Arguments
/// * `path` - File path (potentially relative)
///
/// # Returns
/// Absolute path or error
#[no_mangle]
pub extern "C" fn native_path_resolve(path: RuntimeValue) -> RuntimeValue {
    // TODO: Extract actual path from RuntimeValue (currently placeholder)
    // For now, we just return the path as-is
    // In a full implementation, this would:
    // 1. Extract string from RuntimeValue
    // 2. Resolve relative to current working directory
    // 3. Return absolute path as RuntimeValue

    #[cfg(target_family = "unix")]
    {
        use std::path::PathBuf;
        use std::env;

        // Placeholder: In real implementation, extract string from RuntimeValue
        // For now, assume path is already absolute and return it
        // This is a stub until RuntimeString extraction is implemented
        path
    }

    #[cfg(not(target_family = "unix"))]
    {
        path
    }
}

// =============================================================================
// Async Primitives
// =============================================================================

/// Yield control back to async runtime
///
/// This is used for cooperative multitasking when busy-waiting
#[no_mangle]
pub extern "C" fn async_yield() {
    // In a real implementation, this would yield to the async runtime
    // For now, just hint to the scheduler to give other threads a chance
    std::thread::yield_now();
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mmap_lifecycle() {
        // This would require actual file for testing
        // Skip for now - needs integration test
    }

    #[test]
    fn test_fadvise_hints() {
        // Test that hints don't crash
        // These are best-effort hints, so no way to verify effect
        native_fadvise_sequential(1);
        native_fadvise_random(1);
    }
}
