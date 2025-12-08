use super::{ExecutableMemory, MemoryAllocator, Protection};
use windows_sys::Win32::System::Memory::*;

pub struct WindowsAllocator;

impl WindowsAllocator {
    pub fn new() -> Self {
        Self
    }

    fn protection_to_flags(prot: Protection) -> u32 {
        match (prot.read, prot.write, prot.execute) {
            (true, true, true) => PAGE_EXECUTE_READWRITE,
            (true, true, false) => PAGE_READWRITE,
            (true, false, true) => PAGE_EXECUTE_READ,
            (true, false, false) => PAGE_READONLY,
            (false, false, true) => PAGE_EXECUTE,
            _ => PAGE_NOACCESS,
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

        if result == 0 {
            return Err(std::io::Error::last_os_error());
        }

        Ok(())
    }

    fn free(&self, mem: ExecutableMemory) -> std::io::Result<()> {
        drop(mem);
        Ok(())
    }
}

#[cfg(windows)]
impl Drop for ExecutableMemory {
    fn drop(&mut self) {
        unsafe {
            VirtualFree(self.ptr as *mut _, 0, MEM_RELEASE);
        }
    }
}
