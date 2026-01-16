//! Zero-copy file transfer operations
//!
//! Provides native implementations for:
//! - sendfile (Linux/Unix) - Zero-copy file transfer
//! - copy_file_range (Linux 4.5+) - In-kernel file copying

use crate::value::RuntimeValue;
use std::os::unix::io::RawFd;

// =============================================================================
// Zero-Copy File Transfer Operations
// =============================================================================

/// Zero-copy file transfer using sendfile (Linux/Unix)
///
/// Transfers data directly from one file descriptor to another without copying
/// data into userspace, leveraging kernel-level optimizations like DMA.
///
/// # Arguments
/// * `out_fd` - Destination file descriptor
/// * `in_fd` - Source file descriptor
/// * `offset` - Offset in source file
/// * `count` - Number of bytes to transfer
///
/// # Returns
/// Number of bytes transferred as RuntimeValue, or NIL on error
///
/// # Platforms
/// - Linux: Full support via libc::sendfile
/// - Other Unix: Returns NIL (not implemented)
///
/// # Notes
/// - The offset is updated after the transfer
/// - Efficient for large file transfers (network sockets, etc)
/// - Avoids kernel buffer copies
#[no_mangle]
pub extern "C" fn native_sendfile(out_fd: i64, in_fd: i64, offset: u64, count: u64) -> RuntimeValue {
    #[cfg(target_os = "linux")]
    {
        use libc::sendfile;

        unsafe {
            let mut off = offset as i64;
            let result = sendfile(out_fd as RawFd, in_fd as RawFd, &mut off as *mut i64, count as usize);

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
/// Copies data from one file to another using kernel-level copy-on-write
/// semantics or reflink when available. More efficient than sendfile for
/// local file-to-file transfers.
///
/// # Arguments
/// * `in_fd` - Source file descriptor
/// * `out_fd` - Destination file descriptor
/// * `len` - Number of bytes to copy
///
/// # Returns
/// Number of bytes copied as RuntimeValue, or NIL on error
///
/// # Platforms
/// - Linux 4.5+: Full support via libc::copy_file_range
/// - Other platforms: Returns NIL (not implemented)
///
/// # Notes
/// - Both file positions are updated
/// - Uses reflink/CoW when available (BTRFS, XFS)
/// - Falls back to in-kernel copy on other filesystems
/// - More efficient than userspace read/write for large files
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
