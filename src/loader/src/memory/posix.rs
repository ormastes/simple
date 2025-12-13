use super::common::{align_size, check_unix_result, default_free, get_page_size};
use super::{ExecutableMemory, MemoryAllocator, Protection};
use libc::{
    mmap, mprotect, munmap, MAP_ANON, MAP_FAILED, MAP_PRIVATE, PROT_EXEC, PROT_READ, PROT_WRITE,
};
use std::ptr;

/// POSIX-compliant memory allocator for Unix systems (Linux, macOS, BSD)
pub struct PosixAllocator;

crate::impl_allocator_new!(PosixAllocator);

impl PosixAllocator {
    fn protection_to_flags(prot: Protection) -> i32 {
        match prot {
            Protection::ReadOnly => PROT_READ,
            Protection::ReadWrite => PROT_READ | PROT_WRITE,
            Protection::ReadExecute => PROT_READ | PROT_EXEC,
            Protection::ReadWriteExecute => PROT_READ | PROT_WRITE | PROT_EXEC,
        }
    }
}

impl MemoryAllocator for PosixAllocator {
    fn allocate(&self, size: usize, alignment: usize) -> std::io::Result<ExecutableMemory> {
        let page_size = get_page_size();
        let align = alignment.max(page_size);
        let aligned_size = align_size(size, align);

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

        if ptr == MAP_FAILED {
            return Err(std::io::Error::last_os_error());
        }

        Ok(ExecutableMemory {
            ptr: ptr as *mut u8,
            size: aligned_size,
            dealloc: |ptr, size| {
                unsafe {
                    munmap(ptr as *mut _, size);
                }
            },
        })
    }

    fn protect(&self, mem: &ExecutableMemory, prot: Protection) -> std::io::Result<()> {
        let flags = Self::protection_to_flags(prot);
        let result = unsafe { mprotect(mem.ptr as *mut _, mem.size, flags) };
        check_unix_result(result)
    }

    fn free(&self, mem: ExecutableMemory) -> std::io::Result<()> {
        default_free(mem)
    }
}
