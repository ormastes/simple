//! Memory Layout and Management
//!
//! Defines memory regions and provides memory layout abstractions for embedded targets.

/// Memory region type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MemoryType {
    /// Flash memory (read-only, execute).
    Flash,
    /// RAM (read-write).
    Ram,
    /// Peripheral memory (read-write, no cache).
    Peripheral,
    /// External memory.
    External,
}

/// Memory region definition.
#[derive(Debug, Clone, Copy)]
pub struct MemoryRegion {
    /// Region name.
    pub name: &'static str,
    /// Start address.
    pub start: usize,
    /// Size in bytes.
    pub size: usize,
    /// Memory type.
    pub mem_type: MemoryType,
}

impl MemoryRegion {
    /// Create a new memory region.
    pub const fn new(name: &'static str, start: usize, size: usize, mem_type: MemoryType) -> Self {
        Self {
            name,
            start,
            size,
            mem_type,
        }
    }

    /// Get the end address (exclusive).
    pub const fn end(&self) -> usize {
        self.start + self.size
    }

    /// Check if an address is within this region.
    pub const fn contains(&self, addr: usize) -> bool {
        addr >= self.start && addr < self.end()
    }

    /// Check if a range is within this region.
    pub const fn contains_range(&self, start: usize, size: usize) -> bool {
        start >= self.start && start + size <= self.end()
    }
}

/// Memory layout for a target.
#[derive(Debug, Clone)]
pub struct MemoryLayout {
    /// Flash region.
    pub flash: MemoryRegion,
    /// RAM region.
    pub ram: MemoryRegion,
    /// Additional regions.
    pub extra: &'static [MemoryRegion],
    /// Stack size.
    pub stack_size: usize,
    /// Heap size (0 if no heap).
    pub heap_size: usize,
}

impl MemoryLayout {
    /// Create a simple memory layout with flash and RAM.
    pub const fn simple(
        flash_start: usize,
        flash_size: usize,
        ram_start: usize,
        ram_size: usize,
    ) -> Self {
        Self {
            flash: MemoryRegion::new("FLASH", flash_start, flash_size, MemoryType::Flash),
            ram: MemoryRegion::new("RAM", ram_start, ram_size, MemoryType::Ram),
            extra: &[],
            stack_size: 4096,
            heap_size: 0,
        }
    }

    /// Set stack size.
    pub const fn with_stack_size(mut self, size: usize) -> Self {
        self.stack_size = size;
        self
    }

    /// Set heap size.
    pub const fn with_heap_size(mut self, size: usize) -> Self {
        self.heap_size = size;
        self
    }

    /// Calculate the total RAM needed for stack and heap.
    pub const fn reserved_ram(&self) -> usize {
        self.stack_size + self.heap_size
    }

    /// Get available RAM for data and BSS.
    pub const fn available_ram(&self) -> usize {
        self.ram.size - self.reserved_ram()
    }
}

// Common memory layouts for popular chips

/// STM32F103 (Blue Pill) - 64KB flash, 20KB RAM.
pub const STM32F103: MemoryLayout = MemoryLayout::simple(
    0x0800_0000,
    64 * 1024, // 64KB Flash
    0x2000_0000,
    20 * 1024, // 20KB RAM
)
.with_stack_size(2048);

/// STM32F4xx - 512KB flash, 128KB RAM.
pub const STM32F4: MemoryLayout = MemoryLayout::simple(
    0x0800_0000,
    512 * 1024, // 512KB Flash
    0x2000_0000,
    128 * 1024, // 128KB RAM
)
.with_stack_size(8192)
.with_heap_size(32 * 1024);

/// nRF52832 - 512KB flash, 64KB RAM.
pub const NRF52832: MemoryLayout = MemoryLayout::simple(
    0x0000_0000,
    512 * 1024, // 512KB Flash
    0x2000_0000,
    64 * 1024, // 64KB RAM
)
.with_stack_size(4096)
.with_heap_size(16 * 1024);

/// ESP32-C3 (RISC-V) - 4MB flash, 400KB RAM.
pub const ESP32_C3: MemoryLayout = MemoryLayout::simple(
    0x4200_0000,
    4 * 1024 * 1024, // 4MB Flash
    0x3FC8_0000,
    400 * 1024, // 400KB RAM
)
.with_stack_size(8192)
.with_heap_size(64 * 1024);

/// Generic RISC-V (QEMU virt) - 128MB RAM.
pub const RISCV_QEMU: MemoryLayout = MemoryLayout::simple(
    0x8000_0000,
    128 * 1024 * 1024, // 128MB (RAM as flash)
    0x8800_0000,
    128 * 1024 * 1024, // 128MB RAM
)
.with_stack_size(65536)
.with_heap_size(1024 * 1024);

// Note: Linker script generation requires std and is only used at build time on the host.
// Use the pre-written linker scripts in linker/cortex-m.ld or linker/riscv.ld,
// or generate custom scripts using the build.rs pattern.

/// Get the recommended linker script path for ARM Cortex-M.
pub const fn cortex_m_linker_script() -> &'static str {
    "linker/cortex-m.ld"
}

/// Get the recommended linker script path for RISC-V.
pub const fn riscv_linker_script() -> &'static str {
    "linker/riscv.ld"
}
