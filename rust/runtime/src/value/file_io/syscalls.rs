//! Low-level system call wrappers for file I/O operations
//!
//! Provides direct bindings to platform-specific syscalls for:
//! - Memory mapping (mmap, munmap, madvise)
//! - File operations (open, close)
//! - File metadata (file size, existence check)
//!
//! These wrappers are used by the Simple stdlib for low-level file operations
//! and support both Unix (Linux, macOS, BSD) and Windows platforms.

// =============================================================================
// Low-Level Memory Mapping Syscalls
// =============================================================================

/// Low-level mmap system call wrapper
///
/// Maps a file or anonymous memory region into the process address space.
/// Supports both Unix (POSIX mmap) and Windows (CreateFileMapping + MapViewOfFile).
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
///
/// # Platform-Specific Notes
/// - **Unix**: Direct mmap syscall with all standard flags
/// - **Windows**: Uses CreateFileMappingW + MapViewOfFile, with automatic flag conversion:
///   - MAP_PRIVATE with PROT_WRITE → PAGE_WRITECOPY
///   - MAP_SHARED with PROT_WRITE → PAGE_READWRITE
///   - Read-only → PAGE_READONLY
#[no_mangle]
pub extern "C" fn sys_mmap(addr: i64, length: u64, prot: i32, flags: i32, fd: i32, offset: u64) -> i64 {
    #[cfg(target_family = "unix")]
    {
        use libc::mmap;

        unsafe {
            let ptr = mmap(
                if addr == 0 {
                    std::ptr::null_mut()
                } else {
                    addr as *mut libc::c_void
                },
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
        use windows_sys::Win32::Storage::FileSystem::{FILE_MAP_COPY, FILE_MAP_READ, FILE_MAP_WRITE};
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
                    PAGE_WRITECOPY // MAP_PRIVATE with write
                } else {
                    PAGE_READWRITE // MAP_SHARED with write
                }
            } else {
                PAGE_READONLY // Read-only
            };

            // Create file mapping object
            let map_handle = CreateFileMappingW(
                file_handle,
                std::ptr::null(),
                protect,
                (length >> 32) as u32,        // High DWORD of size
                (length & 0xFFFFFFFF) as u32, // Low DWORD of size
                std::ptr::null(),             // No name (anonymous)
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
                FILE_MAP_READ // Default to read
            };

            let ptr = MapViewOfFile(
                map_handle,
                desired_access,
                (offset >> 32) as u32,        // High DWORD of offset
                (offset & 0xFFFFFFFF) as u32, // Low DWORD of offset
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
/// Unmaps a previously mapped memory region and returns it to the system.
/// Supports both Unix (POSIX munmap) and Windows (UnmapViewOfFile).
///
/// # Arguments
/// * `addr` - Address of mapped region
/// * `length` - Size of mapping (ignored on Windows)
///
/// # Returns
/// 0 on success, -1 on error
///
/// # Platform-Specific Notes
/// - **Unix**: length parameter must match the original mmap length
/// - **Windows**: Unmaps the entire view regardless of length (parameter ignored)
#[no_mangle]
pub extern "C" fn sys_munmap(addr: i64, length: u64) -> i32 {
    #[cfg(target_family = "unix")]
    {
        use libc::munmap;

        unsafe { munmap(addr as *mut libc::c_void, length as libc::size_t) }
    }

    #[cfg(target_family = "windows")]
    {
        use windows_sys::Win32::System::Memory::UnmapViewOfFile;

        unsafe {
            // UnmapViewOfFile unmaps entire view (length parameter ignored)
            if UnmapViewOfFile(addr as *const std::ffi::c_void) != 0 {
                0 // Success
            } else {
                -1 // Failure
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
/// Provides hints to the kernel about expected memory access patterns.
/// Supports both Unix (POSIX madvise) and Windows (PrefetchVirtualMemory, DiscardVirtualMemory).
///
/// # Arguments
/// * `addr` - Address of mapped region
/// * `length` - Size of region
/// * `advice` - Advice constant:
///   - 0: MADV_NORMAL - No special advice
///   - 1: MADV_RANDOM - Random access pattern
///   - 2: MADV_SEQUENTIAL - Sequential access expected
///   - 3: MADV_WILLNEED - Expect to need (preload) pages
///   - 4: MADV_DONTNEED - Don't need pages (can free)
///
/// # Returns
/// 0 on success, -1 on error
///
/// # Platform-Specific Notes
/// - **Unix**: Full support for all POSIX madvise hints (Linux and other Unix variants)
/// - **Windows**: Partial implementation
///   - MADV_WILLNEED (3) → PrefetchVirtualMemory (Windows 8+)
///   - MADV_DONTNEED (4) → DiscardVirtualMemory (Windows 8.1+)
///   - Other hints are no-ops (Windows manages automatically)
///   - Returns 0 even if Windows API unavailable (graceful degradation)
#[no_mangle]
pub extern "C" fn sys_madvise(addr: i64, length: u64, advice: i32) -> i32 {
    #[cfg(target_os = "linux")]
    {
        use libc::madvise;

        unsafe { madvise(addr as *mut libc::c_void, length as libc::size_t, advice) }
    }

    #[cfg(all(target_family = "unix", not(target_os = "linux")))]
    {
        use libc::madvise;

        unsafe { madvise(addr as *mut libc::c_void, length as libc::size_t, advice) }
    }

    #[cfg(target_family = "windows")]
    {
        use windows_sys::Win32::System::Memory::{DiscardVirtualMemory, PrefetchVirtualMemory, WIN32_MEMORY_RANGE_ENTRY};

        unsafe {
            match advice {
                3 => {
                    // MADV_WILLNEED -> PrefetchVirtualMemory (Windows 8+)
                    let mut range = WIN32_MEMORY_RANGE_ENTRY {
                        VirtualAddress: addr as *mut std::ffi::c_void,
                        NumberOfBytes: length as usize,
                    };

                    if PrefetchVirtualMemory(
                        std::ptr::null_mut(), // Current process
                        1,                    // One range
                        &mut range as *mut WIN32_MEMORY_RANGE_ENTRY,
                        0, // No flags
                    ) != 0
                    {
                        0
                    } else {
                        // Not fatal if unsupported (older Windows)
                        0
                    }
                }
                4 => {
                    // MADV_DONTNEED -> DiscardVirtualMemory (Windows 8.1+)
                    if DiscardVirtualMemory(addr as *mut std::ffi::c_void, length as usize) != 0 {
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

// =============================================================================
// Low-Level File Operation Syscalls
// =============================================================================

/// Low-level open system call wrapper
///
/// Opens a file and returns a file descriptor.
/// Supports both Unix (POSIX open) and Windows (CreateFileA).
///
/// # Arguments
/// * `path_ptr` - Pointer to null-terminated path string
/// * `flags` - Open flags:
///   - 0: O_RDONLY - Read-only
///   - 1: O_WRONLY - Write-only
///   - 2: O_RDWR - Read-write
///   - 64: O_CREAT - Create if doesn't exist
///   - 512: O_TRUNC - Truncate if exists
///   - 1024: O_APPEND - Append mode
/// * `mode` - Permission mode (Unix only, ignored on Windows)
///
/// # Returns
/// File descriptor on success, -1 on error
///
/// # Platform-Specific Notes
/// - **Unix**: Direct open() syscall with all flag combinations supported
/// - **Windows**: Uses CreateFileA with automatic flag conversion:
///   - O_RDONLY → GENERIC_READ
///   - O_WRONLY → GENERIC_WRITE
///   - O_RDWR → GENERIC_READ | GENERIC_WRITE
///   - O_CREAT + O_TRUNC → CREATE_ALWAYS
///   - O_CREAT → OPEN_ALWAYS
///   - O_TRUNC → TRUNCATE_EXISTING
///   - Default → OPEN_EXISTING
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
            CreateFileA, CREATE_ALWAYS, CREATE_NEW, FILE_ATTRIBUTE_NORMAL, FILE_SHARE_READ, FILE_SHARE_WRITE,
            OPEN_ALWAYS, OPEN_EXISTING, TRUNCATE_EXISTING,
        };

        unsafe {
            let path_cstr = CStr::from_ptr(path_ptr as *const i8);
            let path_bytes = path_cstr.to_bytes_with_nul();

            // Convert flags to Windows access and creation disposition
            let (desired_access, creation_disposition) = match flags & 0x3 {
                0 => {
                    // O_RDONLY
                    let disposition = if flags & 64 != 0 {
                        OPEN_ALWAYS // O_CREAT
                    } else {
                        OPEN_EXISTING
                    };
                    (GENERIC_READ, disposition)
                }
                1 => {
                    // O_WRONLY
                    let disposition = if flags & 64 != 0 {
                        if flags & 512 != 0 {
                            CREATE_ALWAYS // O_CREAT | O_TRUNC
                        } else {
                            OPEN_ALWAYS // O_CREAT
                        }
                    } else if flags & 512 != 0 {
                        TRUNCATE_EXISTING // O_TRUNC
                    } else {
                        OPEN_EXISTING
                    };
                    (GENERIC_WRITE, disposition)
                }
                2 => {
                    // O_RDWR
                    let disposition = if flags & 64 != 0 {
                        if flags & 512 != 0 {
                            CREATE_ALWAYS // O_CREAT | O_TRUNC
                        } else {
                            OPEN_ALWAYS // O_CREAT
                        }
                    } else if flags & 512 != 0 {
                        TRUNCATE_EXISTING // O_TRUNC
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
/// Closes a file descriptor and releases associated resources.
/// Supports both Unix (POSIX close) and Windows (CloseHandle).
///
/// # Arguments
/// * `fd` - File descriptor (Windows: HANDLE as i32)
///
/// # Returns
/// 0 on success, -1 on error
///
/// # Platform-Specific Notes
/// - **Unix**: Direct close() syscall
/// - **Windows**: Uses CloseHandle() with cast from i32 to HANDLE
#[no_mangle]
pub extern "C" fn sys_close(fd: i32) -> i32 {
    #[cfg(target_family = "unix")]
    {
        use libc::close;

        unsafe { close(fd) }
    }

    #[cfg(target_family = "windows")]
    {
        use windows_sys::Win32::Foundation::CloseHandle;

        unsafe {
            if CloseHandle(fd as isize) != 0 {
                0 // Success
            } else {
                -1 // Failure
            }
        }
    }

    #[cfg(not(any(target_family = "unix", target_family = "windows")))]
    {
        -1
    }
}

// =============================================================================
// Low-Level File Metadata Syscalls
// =============================================================================

/// Get file size via fstat
///
/// Retrieves file size through the fstat syscall.
/// Supports both Unix (fstat) and Windows (GetFileSizeEx).
///
/// # Arguments
/// * `fd` - File descriptor (Windows: HANDLE as i32)
///
/// # Returns
/// File size in bytes, or -1 on error
///
/// # Platform-Specific Notes
/// - **Unix**: Uses fstat() to get st_size field
/// - **Windows**: Uses GetFileSizeEx() API
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
/// Checks for file existence without opening it.
/// Supports both Unix (access with F_OK) and Windows (GetFileAttributesA).
///
/// # Arguments
/// * `path_ptr` - Pointer to null-terminated path string
///
/// # Returns
/// 1 if file exists, 0 otherwise
///
/// # Platform-Specific Notes
/// - **Unix**: Uses access(path, F_OK) to check existence
/// - **Windows**: Uses GetFileAttributesA() to check attributes
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
