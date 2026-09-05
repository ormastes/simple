//! Memory-Mapped I/O Operations
//!
//! This module provides memory-mapped file I/O operations including:
//! - mmap: Map file into memory
//! - munmap: Unmap memory region
//! - madvise: Advise kernel on memory access pattern
//! - msync: Synchronize memory-mapped file with storage
//!
//! These operations are Unix-specific and provide high-performance
//! file I/O for large files and shared memory scenarios.

/// Memory map a file
/// Returns null pointer on error
///
/// # Arguments
/// - addr: Hint for mapping address (usually null)
/// - length: Length of mapping
/// - prot: Protection flags (PROT_READ, PROT_WRITE, etc.)
/// - flags: Mapping flags (MAP_SHARED, MAP_PRIVATE, etc.)
/// - fd: File descriptor to map
/// - offset: Offset in file
#[no_mangle]
pub unsafe extern "C" fn rt_file_mmap(
    addr: *mut u8,
    length: u64,
    prot: i32,
    flags: i32,
    fd: i32,
    offset: u64,
) -> *mut u8 {
    let Ok(length) = usize::try_from(length) else {
        return std::ptr::null_mut();
    };
    let Ok(offset) = i64::try_from(offset) else {
        return std::ptr::null_mut();
    };
    if length == 0 || fd < 0 {
        return std::ptr::null_mut();
    }
    #[cfg(unix)]
    {
        use libc::mmap;

        unsafe {
            let addr = mmap(addr.cast(), length, prot, flags, fd, offset);

            if addr == libc::MAP_FAILED {
                std::ptr::null_mut()
            } else {
                addr as *mut u8
            }
        }
    }

    #[cfg(not(unix))]
    {
        // Non-Unix platforms not supported for mmap
        std::ptr::null_mut()
    }
}

/// Unmap memory region
/// Returns 0 on success, -1 on error
#[no_mangle]
pub unsafe extern "C" fn rt_file_munmap(addr: *mut u8, length: u64) -> i32 {
    let Ok(length) = usize::try_from(length) else {
        return -1;
    };
    if addr.is_null() || length == 0 {
        return -1;
    }
    #[cfg(unix)]
    {
        use libc::munmap;

        unsafe { munmap(addr as *mut libc::c_void, length) }
    }

    #[cfg(not(unix))]
    {
        -1
    }
}

/// Advise kernel on memory access pattern
/// Returns 0 on success, -1 on error
///
/// # Advice values (Unix)
/// - MADV_NORMAL: No special treatment
/// - MADV_RANDOM: Random access pattern
/// - MADV_SEQUENTIAL: Sequential access pattern
/// - MADV_WILLNEED: Will need these pages soon
/// - MADV_DONTNEED: Don't need these pages
#[no_mangle]
pub unsafe extern "C" fn rt_file_madvise(addr: *mut u8, length: u64, advice: i32) -> i32 {
    let Ok(length) = usize::try_from(length) else {
        return -1;
    };
    if addr.is_null() || length == 0 {
        return -1;
    }
    #[cfg(unix)]
    {
        use libc::madvise;

        unsafe { madvise(addr as *mut libc::c_void, length, advice) }
    }

    #[cfg(not(unix))]
    {
        -1
    }
}

/// Synchronize memory-mapped file with storage
/// Returns 0 on success, -1 on error
///
/// # Flags (Unix)
/// - MS_ASYNC: Asynchronous sync
/// - MS_SYNC: Synchronous sync
/// - MS_INVALIDATE: Invalidate other mappings
#[no_mangle]
pub unsafe extern "C" fn rt_file_msync(addr: *mut u8, length: u64, flags: i32) -> i32 {
    let Ok(length) = usize::try_from(length) else {
        return -1;
    };
    if addr.is_null() || length == 0 {
        return -1;
    }
    #[cfg(unix)]
    {
        use libc::msync;

        unsafe { msync(addr as *mut libc::c_void, length, flags) }
    }

    #[cfg(not(unix))]
    {
        -1
    }
}

/// Wrapper for native_msync - stdlib compatibility
/// Returns 0 on success, -1 on error
#[no_mangle]
pub unsafe extern "C" fn native_msync(addr: *mut u8, length: u64, flags: i32) -> i32 {
    unsafe { rt_file_msync(addr, length, flags) }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(unix)]
    use std::fs;
    #[cfg(unix)]
    use std::os::unix::io::AsRawFd;
    #[cfg(unix)]
    use tempfile::TempDir;

    #[test]
    #[cfg(unix)]
    fn test_mmap_munmap() {
        use libc::{MAP_SHARED, PROT_READ};

        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.txt");
        let content = b"Hello, mmap!";
        fs::write(&file_path, content).unwrap();

        let file = fs::File::open(&file_path).unwrap();
        let fd = file.as_raw_fd();
        let size = content.len() as u64;

        unsafe {
            // Map the file into memory
            let addr = rt_file_mmap(std::ptr::null_mut(), size, PROT_READ, MAP_SHARED, fd, 0);
            assert!(!addr.is_null(), "mmap failed");

            // Read the mapped content
            let mapped_slice = std::slice::from_raw_parts(addr, size as usize);
            assert_eq!(mapped_slice, content);

            // Unmap the memory
            let result = rt_file_munmap(addr, size);
            assert_eq!(result, 0, "munmap failed");
        }

        // File is closed when dropped
        drop(file);
    }

    #[test]
    #[cfg(unix)]
    fn test_madvise() {
        use libc::{MADV_SEQUENTIAL, MAP_PRIVATE, PROT_READ};

        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.txt");
        fs::write(&file_path, b"test content").unwrap();

        let file = fs::File::open(&file_path).unwrap();
        let fd = file.as_raw_fd();
        let size = 12u64;

        unsafe {
            let addr = rt_file_mmap(std::ptr::null_mut(), size, PROT_READ, MAP_PRIVATE, fd, 0);
            assert!(!addr.is_null());

            // Advise sequential access
            let result = rt_file_madvise(addr, size, MADV_SEQUENTIAL);
            assert_eq!(result, 0, "madvise failed");

            rt_file_munmap(addr, size);
        }

        drop(file);
    }

    #[test]
    #[cfg(unix)]
    fn test_msync() {
        use libc::{MAP_SHARED, MS_SYNC, PROT_READ, PROT_WRITE};

        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.txt");
        fs::write(&file_path, b"original").unwrap();

        let file = fs::OpenOptions::new().read(true).write(true).open(&file_path).unwrap();
        let fd = file.as_raw_fd();
        let size = 8u64;

        unsafe {
            let addr = rt_file_mmap(std::ptr::null_mut(), size, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
            assert!(!addr.is_null());

            // Sync the mapping
            let result = rt_file_msync(addr, size, MS_SYNC);
            assert_eq!(result, 0, "msync failed");

            rt_file_munmap(addr, size);
        }

        drop(file);
    }

    #[test]
    fn raw_mapping_lifecycle_rejects_invalid_pointer_and_size() {
        unsafe {
            assert!(rt_file_mmap(std::ptr::null_mut(), 0, 0, 0, -1, 0).is_null());
            assert_eq!(rt_file_munmap(std::ptr::null_mut(), 1), -1);
            assert_eq!(rt_file_munmap(std::ptr::dangling_mut(), 0), -1);
            assert_eq!(rt_file_madvise(std::ptr::null_mut(), 1, 0), -1);
            assert_eq!(rt_file_msync(std::ptr::null_mut(), 1, 0), -1);
        }
    }
}
