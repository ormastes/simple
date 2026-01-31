//! Memory-mapped file operations - Mold-inspired optimizations
//!
//! Provides native implementations for mmap (memory-mapped) file operations:
//! - SHARED and PRIVATE memory mapping
//! - Zero-copy read operations
//! - Memory region unmapping with registry cleanup

use super::{MmapRegion, MMAP_REGISTRY};
use crate::value::RuntimeValue;

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

        let fd = handle as std::os::unix::io::RawFd;
        let len = size as usize;

        unsafe {
            let ptr = mmap(
                std::ptr::null_mut(),
                len,
                PROT_READ,
                MAP_SHARED, // SHARED instead of PRIVATE
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
        RuntimeValue::NIL // Error - not supported
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
        use libc::{mmap, MAP_PRIVATE, PROT_READ};

        let fd = handle as std::os::unix::io::RawFd;
        let len = size as usize;

        unsafe {
            let ptr = mmap(std::ptr::null_mut(), len, PROT_READ, MAP_PRIVATE, fd, 0);

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
        RuntimeValue::NIL // Error - not supported
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

#[cfg(test)]
mod tests {
    #[test]
    fn test_mmap_lifecycle() {
        // This would require actual file for testing
        // Skip for now - needs integration test
    }
}
