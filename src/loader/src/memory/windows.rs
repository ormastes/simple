use super::common::{check_windows_result, default_free};
use super::{ExecutableMemory, MemoryAllocator, Protection};
use windows_sys::Win32::System::Memory::*;

/// Windows memory allocator using VirtualAlloc/VirtualProtect/VirtualFree
pub struct WindowsAllocator;

crate::impl_allocator_new!(WindowsAllocator);

impl WindowsAllocator {
    fn protection_to_flags(prot: Protection) -> u32 {
        match prot {
            Protection::ReadOnly => PAGE_READONLY,
            Protection::ReadWrite => PAGE_READWRITE,
            Protection::ReadExecute => PAGE_EXECUTE_READ,
            Protection::ReadWriteExecute => PAGE_EXECUTE_READWRITE,
        }
    }
}

impl MemoryAllocator for WindowsAllocator {
    fn allocate(&self, size: usize, _alignment: usize) -> std::io::Result<ExecutableMemory> {
        let ptr = unsafe {
            VirtualAlloc(
                std::ptr::null_mut(),
                size,
                MEM_COMMIT | MEM_RESERVE,
                PAGE_READWRITE,
            )
        };

        if ptr.is_null() {
            return Err(std::io::Error::last_os_error());
        }

        Ok(ExecutableMemory {
            ptr: ptr as *mut u8,
            size,
        })
    }

    fn protect(&self, mem: &ExecutableMemory, prot: Protection) -> std::io::Result<()> {
        let flags = Self::protection_to_flags(prot);
        let mut old_flags = 0u32;
        let result = unsafe { VirtualProtect(mem.ptr as *mut _, mem.size, flags, &mut old_flags) };
        check_windows_result(result)
    }

    fn free(&self, mem: ExecutableMemory) -> std::io::Result<()> {
        default_free(mem)
    }
}

impl Drop for ExecutableMemory {
    fn drop(&mut self) {
        unsafe {
            VirtualFree(self.ptr as *mut _, 0, MEM_RELEASE);
        }
    }
}
