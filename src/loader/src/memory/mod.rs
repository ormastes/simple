#[cfg(unix)]
mod linux;
#[cfg(windows)]
mod windows;

#[cfg(unix)]
pub use linux::*;
#[cfg(windows)]
pub use windows::*;

/// Memory protection flags
#[derive(Debug, Clone, Copy)]
pub struct Protection {
    pub read: bool,
    pub write: bool,
    pub execute: bool,
}

impl Protection {
    pub const READ_ONLY: Self = Self {
        read: true,
        write: false,
        execute: false,
    };
    pub const READ_WRITE: Self = Self {
        read: true,
        write: true,
        execute: false,
    };
    pub const READ_EXECUTE: Self = Self {
        read: true,
        write: false,
        execute: true,
    };
    pub const READ_WRITE_EXECUTE: Self = Self {
        read: true,
        write: true,
        execute: true,
    };
}

/// Executable memory region
pub struct ExecutableMemory {
    pub(crate) ptr: *mut u8,
    pub(crate) size: usize,
}

impl ExecutableMemory {
    pub fn as_ptr(&self) -> *const u8 {
        self.ptr
    }

    pub fn as_mut_ptr(&self) -> *mut u8 {
        self.ptr
    }

    pub fn size(&self) -> usize {
        self.size
    }

    /// Get function pointer at offset
    pub unsafe fn get_fn<F>(&self, offset: usize) -> F {
        std::mem::transmute_copy(&(self.ptr.add(offset) as usize))
    }
}

/// Memory allocator trait
pub trait MemoryAllocator {
    /// Allocate memory with given size and alignment
    fn allocate(&self, size: usize, alignment: usize) -> std::io::Result<ExecutableMemory>;

    /// Set protection on memory region
    fn protect(&self, mem: &ExecutableMemory, prot: Protection) -> std::io::Result<()>;

    /// Free memory
    fn free(&self, mem: ExecutableMemory) -> std::io::Result<()>;
}
