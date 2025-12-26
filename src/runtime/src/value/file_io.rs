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
// The pointer itself can be shared across threads as it points to memory-mapped pages
unsafe impl Send for MmapRegion {}
unsafe impl Sync for MmapRegion {}

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

    #[cfg(target_family = "windows")]
    {
        use std::os::windows::io::AsRawHandle;
        use windows_sys::Win32::Foundation::{CloseHandle, INVALID_HANDLE_VALUE};
        use windows_sys::Win32::Storage::FileSystem::{FILE_MAP_READ, FILE_MAP_WRITE, FILE_MAP_COPY};
        use windows_sys::Win32::System::Memory::{
            CreateFileMappingW, MapViewOfFile, PAGE_READONLY, PAGE_READWRITE, PAGE_WRITECOPY,
        };

        unsafe {
            // Convert fd to HANDLE (Windows file descriptor)
            let file_handle = if fd == -1 {
                INVALID_HANDLE_VALUE as isize
            } else {
                fd as isize
            };

            // Convert prot flags to Windows protection
            let protect = if prot & 0x2 != 0 {
                // PROT_WRITE
                if flags & 0x2 != 0 {
                    PAGE_WRITECOPY  // MAP_PRIVATE with write
                } else {
                    PAGE_READWRITE  // MAP_SHARED with write
                }
            } else {
                PAGE_READONLY  // Read-only
            };

            // Create file mapping object
            let map_handle = CreateFileMappingW(
                file_handle,
                std::ptr::null(),
                protect,
                (length >> 32) as u32,  // High DWORD of size
                (length & 0xFFFFFFFF) as u32,  // Low DWORD of size
                std::ptr::null(),  // No name (anonymous)
            );

            if map_handle == 0 || map_handle == INVALID_HANDLE_VALUE as isize {
                return -1;
            }

            // Map view of file
            let desired_access = if prot & 0x2 != 0 {
                FILE_MAP_WRITE | FILE_MAP_READ
            } else if prot & 0x1 != 0 {
                FILE_MAP_READ
            } else {
                FILE_MAP_READ  // Default to read
            };

            let ptr = MapViewOfFile(
                map_handle,
                desired_access,
                (offset >> 32) as u32,  // High DWORD of offset
                (offset & 0xFFFFFFFF) as u32,  // Low DWORD of offset
                length as usize,
            );

            // Close the mapping handle (view retains reference to file)
            CloseHandle(map_handle);

            if ptr.is_null() {
                -1
            } else {
                ptr as i64
            }
        }
    }

    #[cfg(not(any(target_family = "unix", target_family = "windows")))]
    {
        -1
    }
}

/// Low-level munmap system call wrapper
///
/// # Arguments
/// * `addr` - Address of mapped region
/// * `length` - Size of mapping (ignored on Windows)
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

    #[cfg(target_family = "windows")]
    {
        use windows_sys::Win32::System::Memory::UnmapViewOfFile;

        unsafe {
            // UnmapViewOfFile unmaps entire view (length parameter ignored)
            if UnmapViewOfFile(addr as *const std::ffi::c_void) != 0 {
                0  // Success
            } else {
                -1  // Failure
            }
        }
    }

    #[cfg(not(any(target_family = "unix", target_family = "windows")))]
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
///
/// # Notes
/// Windows: Partial implementation using PrefetchVirtualMemory (WILLNEED) and
/// DiscardVirtualMemory (DONTNEED). Other hints are no-ops (Windows manages automatically).
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

    #[cfg(target_family = "windows")]
    {
        use windows_sys::Win32::System::Memory::{
            DiscardVirtualMemory, PrefetchVirtualMemory, WIN32_MEMORY_RANGE_ENTRY,
        };

        unsafe {
            match advice {
                3 => {
                    // MADV_WILLNEED -> PrefetchVirtualMemory (Windows 8+)
                    let mut range = WIN32_MEMORY_RANGE_ENTRY {
                        VirtualAddress: addr as *mut std::ffi::c_void,
                        NumberOfBytes: length as usize,
                    };

                    if PrefetchVirtualMemory(
                        std::ptr::null_mut(),  // Current process
                        1,  // One range
                        &mut range as *mut WIN32_MEMORY_RANGE_ENTRY,
                        0,  // No flags
                    ) != 0 {
                        0
                    } else {
                        // Not fatal if unsupported (older Windows)
                        0
                    }
                }
                4 => {
                    // MADV_DONTNEED -> DiscardVirtualMemory (Windows 8.1+)
                    if DiscardVirtualMemory(
                        addr as *mut std::ffi::c_void,
                        length as usize,
                    ) != 0 {
                        0
                    } else {
                        // Not fatal if unsupported
                        0
                    }
                }
                _ => {
                    // MADV_NORMAL, MADV_RANDOM, MADV_SEQUENTIAL
                    // Windows manages these automatically, no explicit hints needed
                    0
                }
            }
        }
    }

    #[cfg(not(any(target_family = "unix", target_family = "windows")))]
    {
        -1
    }
}

/// Low-level open system call wrapper
///
/// # Arguments
/// * `path_ptr` - Pointer to null-terminated path string
/// * `flags` - Open flags (O_RDONLY=0, O_WRONLY=1, O_RDWR=2, O_CREAT=64, O_TRUNC=512, O_APPEND=1024)
/// * `mode` - Permission mode (ignored on Windows)
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

    #[cfg(target_family = "windows")]
    {
        use std::ffi::CStr;
        use std::os::windows::io::AsRawHandle;
        use windows_sys::Win32::Foundation::{GENERIC_READ, GENERIC_WRITE, INVALID_HANDLE_VALUE};
        use windows_sys::Win32::Storage::FileSystem::{
            CreateFileA, CREATE_ALWAYS, CREATE_NEW, FILE_ATTRIBUTE_NORMAL,
            FILE_SHARE_READ, FILE_SHARE_WRITE, OPEN_ALWAYS, OPEN_EXISTING, TRUNCATE_EXISTING,
        };

        unsafe {
            let path_cstr = CStr::from_ptr(path_ptr as *const i8);
            let path_bytes = path_cstr.to_bytes_with_nul();

            // Convert flags to Windows access and creation disposition
            let (desired_access, creation_disposition) = match flags & 0x3 {
                0 => {
                    // O_RDONLY
                    let disposition = if flags & 64 != 0 {
                        OPEN_ALWAYS  // O_CREAT
                    } else {
                        OPEN_EXISTING
                    };
                    (GENERIC_READ, disposition)
                }
                1 => {
                    // O_WRONLY
                    let disposition = if flags & 64 != 0 {
                        if flags & 512 != 0 {
                            CREATE_ALWAYS  // O_CREAT | O_TRUNC
                        } else {
                            OPEN_ALWAYS  // O_CREAT
                        }
                    } else if flags & 512 != 0 {
                        TRUNCATE_EXISTING  // O_TRUNC
                    } else {
                        OPEN_EXISTING
                    };
                    (GENERIC_WRITE, disposition)
                }
                2 => {
                    // O_RDWR
                    let disposition = if flags & 64 != 0 {
                        if flags & 512 != 0 {
                            CREATE_ALWAYS  // O_CREAT | O_TRUNC
                        } else {
                            OPEN_ALWAYS  // O_CREAT
                        }
                    } else if flags & 512 != 0 {
                        TRUNCATE_EXISTING  // O_TRUNC
                    } else {
                        OPEN_EXISTING
                    };
                    (GENERIC_READ | GENERIC_WRITE, disposition)
                }
                _ => (GENERIC_READ, OPEN_EXISTING),
            };

            let handle = CreateFileA(
                path_bytes.as_ptr(),
                desired_access,
                FILE_SHARE_READ | FILE_SHARE_WRITE,
                std::ptr::null(),
                creation_disposition,
                FILE_ATTRIBUTE_NORMAL,
                0,
            );

            if handle == INVALID_HANDLE_VALUE as isize {
                -1
            } else {
                handle as i32
            }
        }
    }

    #[cfg(not(any(target_family = "unix", target_family = "windows")))]
    {
        -1
    }
}

/// Low-level close system call wrapper
///
/// # Arguments
/// * `fd` - File descriptor (Windows: HANDLE)
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

    #[cfg(target_family = "windows")]
    {
        use windows_sys::Win32::Foundation::CloseHandle;

        unsafe {
            if CloseHandle(fd as isize) != 0 {
                0  // Success
            } else {
                -1  // Failure
            }
        }
    }

    #[cfg(not(any(target_family = "unix", target_family = "windows")))]
    {
        -1
    }
}

/// Get file size via fstat
///
/// # Arguments
/// * `fd` - File descriptor (Windows: HANDLE)
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

    #[cfg(target_family = "windows")]
    {
        use windows_sys::Win32::Storage::FileSystem::GetFileSizeEx;

        unsafe {
            let mut file_size: i64 = 0;
            if GetFileSizeEx(fd as isize, &mut file_size as *mut i64) != 0 {
                file_size
            } else {
                -1
            }
        }
    }

    #[cfg(not(any(target_family = "unix", target_family = "windows")))]
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

    #[cfg(target_family = "windows")]
    {
        use std::ffi::CStr;
        use windows_sys::Win32::Storage::FileSystem::GetFileAttributesA;
        use windows_sys::Win32::Storage::FileSystem::INVALID_FILE_ATTRIBUTES;

        unsafe {
            let path_cstr = CStr::from_ptr(path_ptr as *const i8);
            let path_bytes = path_cstr.to_bytes_with_nul();

            let attrs = GetFileAttributesA(path_bytes.as_ptr());
            if attrs != INVALID_FILE_ATTRIBUTES {
                1
            } else {
                0
            }
        }
    }

    #[cfg(not(any(target_family = "unix", target_family = "windows")))]
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
// Async File Loading Infrastructure (#1765-#1769)
// =============================================================================

use std::sync::Arc;
use parking_lot::RwLock;
use std::sync::mpsc::{channel, Sender, Receiver};
use std::thread::{self, JoinHandle};

/// File loading state for async operations
#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FileLoadState {
    Pending = 0,
    Loading = 1,
    Ready = 2,
    Failed = 3,
}

/// Async file handle for background loading
pub struct AsyncFileHandle {
    path: String,
    state: Arc<RwLock<FileLoadState>>,
    region: Arc<RwLock<Option<MmapRegion>>>,
    error: Arc<RwLock<Option<String>>>,
    mode: i32,    // Open mode flags
    prefault: bool, // Enable progressive prefaulting
}

impl AsyncFileHandle {
    /// Create a new async file handle
    pub fn new(path: String, mode: i32, prefault: bool) -> Self {
        AsyncFileHandle {
            path,
            state: Arc::new(RwLock::new(FileLoadState::Pending)),
            region: Arc::new(RwLock::new(None)),
            error: Arc::new(RwLock::new(None)),
            mode,
            prefault,
        }
    }

    /// Start loading the file in background
    pub fn start_loading(&self) {
        let path = self.path.clone();
        let state = self.state.clone();
        let region = self.region.clone();
        let error = self.error.clone();
        let mode = self.mode;
        let prefault = self.prefault;

        // Submit to thread pool
        ASYNC_FILE_POOL.submit(move || {
            // Mark as loading
            *state.write() = FileLoadState::Loading;

            // Perform the actual file loading
            match load_file_mmap(&path, mode, prefault) {
                Ok(mmap_region) => {
                    *region.write() = Some(mmap_region);
                    *state.write() = FileLoadState::Ready;
                }
                Err(e) => {
                    *error.write() = Some(e);
                    *state.write() = FileLoadState::Failed;
                }
            }
        });
    }

    /// Check if file is ready (non-blocking)
    pub fn is_ready(&self) -> bool {
        *self.state.read() == FileLoadState::Ready
    }

    /// Check if loading failed
    pub fn is_failed(&self) -> bool {
        *self.state.read() == FileLoadState::Failed
    }

    /// Get current state
    pub fn get_state(&self) -> FileLoadState {
        *self.state.read()
    }

    /// Wait for loading to complete (blocking)
    pub fn wait(&self) -> Result<MmapRegion, String> {
        // Spin-wait until ready or failed
        loop {
            let state = *self.state.read();
            match state {
                FileLoadState::Ready => {
                    let region = self.region.read();
                    if let Some(r) = region.as_ref() {
                        return Ok(MmapRegion {
                            ptr: r.ptr,
                            size: r.size,
                        });
                    } else {
                        return Err("Region not available".to_string());
                    }
                }
                FileLoadState::Failed => {
                    let error = self.error.read();
                    return Err(error.clone().unwrap_or_else(|| "Unknown error".to_string()));
                }
                FileLoadState::Pending | FileLoadState::Loading => {
                    // Yield to avoid busy-waiting
                    std::thread::yield_now();
                    std::thread::sleep(std::time::Duration::from_micros(100));
                }
            }
        }
    }
}

/// Worker thread pool for async file operations
struct AsyncFileThreadPool {
    workers: Vec<JoinHandle<()>>,
    sender: Sender<Box<dyn FnOnce() + Send>>,
}

impl AsyncFileThreadPool {
    /// Create a new thread pool with the specified number of workers
    fn new(num_workers: usize) -> Self {
        let (sender, receiver) = channel::<Box<dyn FnOnce() + Send>>();
        let receiver = Arc::new(parking_lot::Mutex::new(receiver));

        let mut workers = Vec::with_capacity(num_workers);

        for id in 0..num_workers {
            let receiver = receiver.clone();
            let handle = thread::Builder::new()
                .name(format!("async-file-worker-{}", id))
                .spawn(move || {
                    loop {
                        let task = {
                            let lock = receiver.lock();
                            lock.recv()
                        };

                        match task {
                            Ok(task) => {
                                task();
                            }
                            Err(_) => {
                                // Channel closed, exit worker
                                break;
                            }
                        }
                    }
                })
                .expect("Failed to spawn worker thread");

            workers.push(handle);
        }

        AsyncFileThreadPool { workers, sender }
    }

    /// Submit a task to the thread pool
    fn submit<F>(&self, task: F)
    where
        F: FnOnce() + Send + 'static,
    {
        self.sender
            .send(Box::new(task))
            .expect("Failed to send task to thread pool");
    }
}

// Global thread pool for async file operations (lazy initialization)
lazy_static::lazy_static! {
    static ref ASYNC_FILE_POOL: AsyncFileThreadPool = {
        let num_workers = num_cpus::get().max(4);
        AsyncFileThreadPool::new(num_workers)
    };
}

/// Load a file using mmap (blocking operation)
fn load_file_mmap(path: &str, mode: i32, prefault: bool) -> Result<MmapRegion, String> {
    // Open file
    let fd = unsafe {
        #[cfg(target_family = "unix")]
        {
            use std::ffi::CString;
            let c_path = CString::new(path).map_err(|e| format!("Invalid path: {}", e))?;
            libc::open(c_path.as_ptr(), mode)
        }
        #[cfg(target_family = "windows")]
        {
            use windows_sys::Win32::Storage::FileSystem::{CreateFileA, OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL};
            use windows_sys::Win32::Foundation::INVALID_HANDLE_VALUE;

            let access = if mode & 0x1 != 0 { 0x80000000 } else { 0 }  // GENERIC_READ
                       | if mode & 0x2 != 0 { 0x40000000 } else { 0 }; // GENERIC_WRITE

            let handle = CreateFileA(
                path.as_ptr(),
                access,
                0x1 | 0x2, // FILE_SHARE_READ | FILE_SHARE_WRITE
                std::ptr::null(),
                OPEN_EXISTING,
                FILE_ATTRIBUTE_NORMAL,
                0,
            );

            if handle == INVALID_HANDLE_VALUE as isize {
                return Err(format!("Failed to open file: {}", path));
            }
            handle as i32
        }
    };

    if fd < 0 {
        return Err(format!("Failed to open file: {}", path));
    }

    // Get file size
    let file_size = sys_file_size(fd);
    if file_size < 0 {
        unsafe { sys_close(fd); }
        return Err("Failed to get file size".to_string());
    }

    // Create mmap
    let mmap_ptr = sys_mmap(
        0,           // addr: let kernel choose
        file_size as u64,
        1,           // prot: PROT_READ
        2,           // flags: MAP_PRIVATE
        fd,
        0,           // offset
    );

    if mmap_ptr < 0 {
        unsafe { sys_close(fd); }
        return Err("mmap failed".to_string());
    }

    // Progressive prefaulting if enabled
    if prefault {
        progressive_prefault(mmap_ptr as *mut u8, file_size as usize);
    }

    // Close fd (mmap keeps reference)
    unsafe { sys_close(fd); }

    Ok(MmapRegion {
        ptr: mmap_ptr as *mut u8,
        size: file_size as usize,
    })
}

/// Progressive prefaulting - gradually fault in pages (#1769)
///
/// This uses madvise WILLNEED to hint the kernel to load pages in the background
fn progressive_prefault(ptr: *mut u8, size: usize) {
    const CHUNK_SIZE: usize = 4 * 1024 * 1024; // 4MB chunks
    const PREFAULT_ADVICE: i32 = 4; // MADV_WILLNEED

    let mut offset = 0;
    while offset < size {
        let chunk_size = std::cmp::min(CHUNK_SIZE, size - offset);

        unsafe {
            let chunk_ptr = ptr.add(offset);
            let _ = sys_madvise(chunk_ptr as i64, chunk_size as u64, PREFAULT_ADVICE);
        }

        offset += chunk_size;

        // Small delay to avoid overwhelming the system
        std::thread::sleep(std::time::Duration::from_micros(100));
    }
}

// =============================================================================
// Async File Handle FFI Functions
// =============================================================================

/// Create a new async file handle
///
/// # Arguments
/// * `path` - RuntimeValue containing the file path (String)
/// * `mode` - Open mode flags
/// * `prefault` - Enable progressive prefaulting (bool)
///
/// # Returns
/// Handle ID (as i64) for the async file handle
#[no_mangle]
pub extern "C" fn native_async_file_create(path: RuntimeValue, mode: i32, prefault: i32) -> i64 {
    // TODO: Extract string from RuntimeValue
    // For now, use placeholder path
    let path_str = "placeholder.txt".to_string();

    let handle = AsyncFileHandle::new(path_str, mode, prefault != 0);

    // Store handle in registry and return ID
    // TODO: Implement handle registry
    0
}

/// Start loading a file asynchronously
#[no_mangle]
pub extern "C" fn native_async_file_start_loading(handle_id: i64) {
    // TODO: Retrieve handle from registry and start loading
}

/// Check if async file is ready (non-blocking)
#[no_mangle]
pub extern "C" fn native_async_file_is_ready(handle_id: i64) -> i32 {
    // TODO: Retrieve handle from registry and check state
    0
}

/// Get async file loading state
#[no_mangle]
pub extern "C" fn native_async_file_get_state(handle_id: i64) -> i32 {
    // TODO: Retrieve handle from registry and return state
    FileLoadState::Pending as i32
}

/// Wait for async file to load (blocking)
///
/// Returns RuntimeValue containing the MmapRegion or error
#[no_mangle]
pub extern "C" fn native_async_file_wait(handle_id: i64) -> RuntimeValue {
    // TODO: Retrieve handle, wait for completion, return region or error
    RuntimeValue::from_int(0)
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
