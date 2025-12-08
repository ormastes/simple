use super::{ExecutableMemory, MemoryAllocator, Protection};
use libc::{mmap, mprotect, munmap, MAP_ANON, MAP_PRIVATE, PROT_EXEC, PROT_NONE, PROT_READ, PROT_WRITE};
use std::ptr;

pub struct LinuxAllocator;

impl LinuxAllocator {
    pub fn new() -> Self {
        Self
    }

    fn protection_to_flags(prot: Protection) -> i32 {
        let mut flags = 0;
        if prot.read {
            flags |= PROT_READ;
        }
        if prot.write {
            flags |= PROT_WRITE;
        }
        if prot.execute {
            flags |= PROT_EXEC;
        }
        if flags == 0 {
            flags = PROT_NONE;
        }
        flags
    }
}

impl MemoryAllocator for LinuxAllocator {
    fn allocate(&self, size: usize, alignment: usize) -> std::io::Result<ExecutableMemory> {
        // Round up to alignment and page size
        let page_size = unsafe { libc::sysconf(libc::_SC_PAGESIZE) as usize };
        let page_size = if page_size == 0 { 4096 } else { page_size };
        let align = alignment.max(page_size);
        let aligned_size = (size + align - 1) & !(align - 1);

        let ptr = unsafe {
            mmap(
                ptr::null_mut(),
                aligned_size,
                PROT_READ | PROT_WRITE,
                MAP_PRIVATE | MAP_ANON,
                -1,
                0,
            )
        };

        if ptr == libc::MAP_FAILED {
            return Err(std::io::Error::last_os_error());
        }

        Ok(ExecutableMemory {
            ptr: ptr as *mut u8,
            size: aligned_size,
        })
    }

    fn protect(&self, mem: &ExecutableMemory, prot: Protection) -> std::io::Result<()> {
        let flags = Self::protection_to_flags(prot);

        let result = unsafe { mprotect(mem.ptr as *mut _, mem.size, flags) };

        if result != 0 {
            return Err(std::io::Error::last_os_error());
        }

        Ok(())
    }

    fn free(&self, mem: ExecutableMemory) -> std::io::Result<()> {
        drop(mem);
        Ok(())
    }
}

#[cfg(unix)]
impl Drop for ExecutableMemory {
    fn drop(&mut self) {
        unsafe {
            munmap(self.ptr as *mut _, self.size);
        }
    }
}
