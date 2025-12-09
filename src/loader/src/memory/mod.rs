mod common;

#[cfg(unix)]
mod posix;
#[cfg(windows)]
mod windows;

#[cfg(unix)]
pub use posix::PosixAllocator;
#[cfg(windows)]
pub use windows::WindowsAllocator;

/// Platform-specific allocator type alias
#[cfg(unix)]
pub type PlatformAllocator = PosixAllocator;
#[cfg(windows)]
pub type PlatformAllocator = WindowsAllocator;

/// Memory protection level - enumerated for formal verification.
///
/// This enum replaces the previous struct with 3 booleans, making
/// invalid states unrepresentable (e.g., execute-only without read).
///
/// Lean equivalent:
/// ```lean
/// inductive Protection
///   | readOnly       -- R--
///   | readWrite      -- RW-
///   | readExecute    -- R-X
///   | readWriteExecute -- RWX
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Protection {
    /// Read-only access (R--)
    ReadOnly,
    /// Read-write access (RW-)
    ReadWrite,
    /// Read-execute access (R-X)
    ReadExecute,
    /// Read-write-execute access (RWX)
    ReadWriteExecute,
}

impl Protection {
    // Legacy constants for backwards compatibility
    pub const READ_ONLY: Self = Self::ReadOnly;
    pub const READ_WRITE: Self = Self::ReadWrite;
    pub const READ_EXECUTE: Self = Self::ReadExecute;
    pub const READ_WRITE_EXECUTE: Self = Self::ReadWriteExecute;

    /// Check if readable
    pub fn is_readable(&self) -> bool {
        true // All valid protections include read
    }

    /// Check if writable
    pub fn is_writable(&self) -> bool {
        matches!(self, Protection::ReadWrite | Protection::ReadWriteExecute)
    }

    /// Check if executable
    pub fn is_executable(&self) -> bool {
        matches!(self, Protection::ReadExecute | Protection::ReadWriteExecute)
    }
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
