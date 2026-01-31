use super::*;
#[cfg(test)]
mod tests {
    use super::*;

    // Mock allocator for testing
    struct MockAllocator;

    impl MemoryAllocator for MockAllocator {
        fn allocate(&self, size: usize, _alignment: usize) -> std::io::Result<ExecutableMemory> {
            let layout = std::alloc::Layout::from_size_align(size, 4096).unwrap();
            let ptr = unsafe { std::alloc::alloc(layout) };
            if ptr.is_null() {
                Err(std::io::Error::new(
                    std::io::ErrorKind::OutOfMemory,
                    "Allocation failed",
                ))
            } else {
                Ok(ExecutableMemory {
                    ptr,
                    size,
                    dealloc: |ptr, size| unsafe {
                        let layout = std::alloc::Layout::from_size_align(size, 4096).unwrap();
                        std::alloc::dealloc(ptr, layout);
                    },
                })
            }
        }

        fn protect(&self, _mem: &ExecutableMemory, _prot: Protection) -> std::io::Result<()> {
            Ok(())
        }

        fn free(&self, mem: ExecutableMemory) -> std::io::Result<()> {
            drop(mem);
            Ok(())
        }
    }

    #[test]
    fn test_settlement_creation() {
        let allocator = Arc::new(MockAllocator);
        let config = SettlementConfig {
            code_region_size: 1024 * 1024, // 1MB
            data_region_size: 512 * 1024,  // 512KB
            reloadable: true,
            executable: false,
        };

        let settlement = Settlement::new(config, allocator).unwrap();
        assert_eq!(settlement.module_count(), 0);
        assert!(settlement.is_reloadable());
        assert!(!settlement.is_executable());
    }

    #[test]
    fn test_module_handle() {
        let h = ModuleHandle(5);
        assert!(h.is_valid());
        assert_eq!(h.as_usize(), 5);
        assert!(!ModuleHandle::INVALID.is_valid());
    }

    #[test]
    fn test_settlement_header() {
        let allocator = Arc::new(MockAllocator);
        let config = SettlementConfig {
            code_region_size: 1024 * 1024,
            data_region_size: 512 * 1024,
            reloadable: true,
            executable: true,
        };

        let settlement = Settlement::new(config, allocator).unwrap();
        let header = settlement.to_header();

        assert!(header.is_valid());
        assert!(header.is_executable());
        assert!(header.is_reloadable());
    }
}
