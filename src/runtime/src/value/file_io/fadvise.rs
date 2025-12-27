//! File I/O hints (fadvise) - Mold-inspired optimizations
//!
//! Provides native implementations for file access hint operations that help
//! the kernel optimize I/O scheduling and caching strategies.
//!
//! These operations are useful for:
//! - Prefetching data (willneed)
//! - Evicting unused data (dontneed)
//! - Optimizing access patterns (sequential/random)

use std::os::unix::io::RawFd;

/// Hint that file will be accessed sequentially
///
/// Tells the kernel to optimize for sequential access patterns, enabling
/// read-ahead caching and prefetch optimizations.
///
/// # Arguments
/// * `handle` - File descriptor
///
/// # Platform Support
/// Currently implemented for Linux via `posix_fadvise(POSIX_FADV_SEQUENTIAL)`.
/// No-op on other platforms.
///
/// # Example
/// ```c
/// // Hint OS to prefetch data for sequential reading
/// native_fadvise_sequential(fd);
/// ```
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
/// Tells the kernel to optimize for random access patterns, disabling
/// sequential prefetching and allowing more flexible caching strategies.
///
/// # Arguments
/// * `handle` - File descriptor
///
/// # Platform Support
/// Currently implemented for Linux via `posix_fadvise(POSIX_FADV_RANDOM)`.
/// No-op on other platforms.
///
/// # Example
/// ```c
/// // Hint OS to disable sequential prefetching
/// native_fadvise_random(fd);
/// ```
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
/// Tells the kernel to prefetch the file's contents into the page cache,
/// reducing latency for subsequent reads. Useful before bulk read operations.
///
/// # Arguments
/// * `handle` - File descriptor
///
/// # Platform Support
/// Currently implemented for Linux via `posix_fadvise(POSIX_FADV_WILLNEED)`.
/// No-op on other platforms.
///
/// # Example
/// ```c
/// // Prefetch entire file into cache before processing
/// native_fadvise_willneed(fd);
/// ```
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
/// Tells the kernel to evict the file's contents from the page cache,
/// freeing memory for other purposes. Useful after processing large files.
///
/// # Arguments
/// * `handle` - File descriptor
///
/// # Platform Support
/// Currently implemented for Linux via `posix_fadvise(POSIX_FADV_DONTNEED)`.
/// No-op on other platforms.
///
/// # Example
/// ```c
/// // Free cache space after streaming file processing
/// native_fadvise_dontneed(fd);
/// ```
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
