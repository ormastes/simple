use super::ExecutableMemory;

/// Default implementation of `free` that simply drops the memory.
/// The actual deallocation happens in the platform-specific `Drop` impl.
pub fn default_free(mem: ExecutableMemory) -> std::io::Result<()> {
    drop(mem);
    Ok(())
}

/// Helper to check syscall result (non-zero = error for Unix)
#[cfg(unix)]
pub fn check_unix_result(result: i32) -> std::io::Result<()> {
    if result != 0 {
        return Err(std::io::Error::last_os_error());
    }
    Ok(())
}

/// Helper to check syscall result (zero = error for Windows)
#[cfg(windows)]
pub fn check_windows_result(result: i32) -> std::io::Result<()> {
    if result == 0 {
        return Err(std::io::Error::last_os_error());
    }
    Ok(())
}

/// Align size up to the given alignment
pub fn align_size(size: usize, alignment: usize) -> usize {
    (size + alignment - 1) & !(alignment - 1)
}

/// Get system page size with fallback
#[cfg(unix)]
pub fn get_page_size() -> usize {
    let page_size = unsafe { libc::sysconf(libc::_SC_PAGESIZE) as usize };
    if page_size == 0 { 4096 } else { page_size }
}

/// Macro to implement common allocator methods
#[macro_export]
macro_rules! impl_allocator_new {
    ($type:ty) => {
        impl $type {
            pub fn new() -> Self {
                Self
            }
        }

        impl Default for $type {
            fn default() -> Self {
                Self::new()
            }
        }
    };
}
