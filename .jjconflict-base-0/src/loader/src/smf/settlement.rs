//! Settlement SMF format definitions.
//!
//! Extended SMF format that carries additional information for settlement operations,
//! native library embedding, and executable packaging.

use std::io::{Read, Write};

/// Settlement SMF magic number: "SSMF"
pub const SSMF_MAGIC: [u8; 4] = *b"SSMF";

/// Settlement SMF format version
pub const SSMF_VERSION: u16 = 1;

// Settlement flags
pub const SSMF_FLAG_EXECUTABLE: u16 = 0x0001; // Has executable stub
pub const SSMF_FLAG_RELOADABLE: u16 = 0x0002; // Supports hot reload
pub const SSMF_FLAG_HAS_NATIVES: u16 = 0x0004; // Contains native libraries
pub const SSMF_FLAG_COMPRESSED: u16 = 0x0008; // Resources are compressed
pub const SSMF_FLAG_DEBUG: u16 = 0x0010; // Contains debug info

// Native library types
pub const NATIVE_LIB_STATIC: u8 = 0x01; // Embedded in settlement
pub const NATIVE_LIB_SHARED: u8 = 0x02; // Load from path at runtime
pub const NATIVE_LIB_SYSTEM: u8 = 0x03; // System library (libc, etc.)

/// Settlement SMF header.
///
/// Layout is designed for executable compatibility:
/// - Executable stub (optional) comes before this header
/// - Critical sections (code, data) are uncompressed and at front
/// - Resources and debug info are at the end (can be zipped)
#[repr(C)]
#[derive(Debug, Clone, Copy, Default)]
pub struct SettlementHeader {
    /// Magic number: "SSMF"
    pub magic: [u8; 4],
    /// Format version
    pub version: u16,
    /// Flags (EXECUTABLE, RELOADABLE, HAS_NATIVES, COMPRESSED, DEBUG)
    pub flags: u16,
    /// Target architecture (matches SMF Arch enum)
    pub arch: u8,
    /// Reserved for future use
    pub reserved: [u8; 5],

    // Section offsets (from start of settlement, after any executable stub)
    /// Offset to code section
    pub code_offset: u64,
    /// Size of code section
    pub code_size: u64,
    /// Offset to data section
    pub data_offset: u64,
    /// Size of data section
    pub data_size: u64,

    // Indirection tables
    /// Offset to function table
    pub func_table_offset: u64,
    /// Size of function table
    pub func_table_size: u64,
    /// Offset to global table
    pub global_table_offset: u64,
    /// Size of global table
    pub global_table_size: u64,
    /// Offset to type table
    pub type_table_offset: u64,
    /// Size of type table
    pub type_table_size: u64,

    // Module and native lib tables
    /// Offset to module table
    pub module_table_offset: u64,
    /// Size of module table
    pub module_table_size: u64,
    /// Offset to native libraries table
    pub native_libs_offset: u64,
    /// Size of native libraries table
    pub native_libs_size: u64,

    // String table
    /// Offset to string table
    pub string_table_offset: u64,
    /// Size of string table
    pub string_table_size: u64,

    // Dependency table
    /// Offset to dependency table
    pub dep_table_offset: u64,
    /// Size of dependency table
    pub dep_table_size: u64,

    // Debug and resources (optional, at end)
    /// Offset to debug info (0 if none)
    pub debug_offset: u64,
    /// Size of debug info
    pub debug_size: u64,
    /// Offset to resources section
    pub resource_offset: u64,
    /// Size of resources section
    pub resource_size: u64,

    // Counts
    /// Number of modules in settlement
    pub module_count: u32,
    /// Number of native libraries
    pub native_lib_count: u32,
    /// Index of entry module (has main())
    pub entry_module_idx: u32,
    /// Function table index for entry point
    pub entry_func_idx: u32,

    // Legacy count fields (for backward compat)
    /// Number of entries in function table
    pub func_table_count: u32,
    /// Number of entries in global table
    pub global_table_count: u32,
    /// Number of entries in type table
    pub type_table_count: u32,
    /// Reserved
    pub _reserved2: u32,

    // Checksums for integrity
    /// CRC32 of code section
    pub code_checksum: u32,
    /// CRC32 of entire file
    pub full_checksum: u32,
}

impl SettlementHeader {
    pub const SIZE: usize = std::mem::size_of::<Self>();

    /// Create a new settlement header with magic and version set.
    pub fn new() -> Self {
        Self {
            magic: SSMF_MAGIC,
            version: SSMF_VERSION,
            ..Default::default()
        }
    }

    /// Check if magic number is valid.
    pub fn is_valid(&self) -> bool {
        self.magic == SSMF_MAGIC
    }

    /// Check if this is an executable settlement.
    pub fn is_executable(&self) -> bool {
        self.flags & SSMF_FLAG_EXECUTABLE != 0
    }

    /// Check if this settlement supports hot reload.
    pub fn is_reloadable(&self) -> bool {
        self.flags & SSMF_FLAG_RELOADABLE != 0
    }

    /// Check if this settlement has native libraries.
    pub fn has_natives(&self) -> bool {
        self.flags & SSMF_FLAG_HAS_NATIVES != 0
    }

    /// Check if resources are compressed.
    pub fn is_compressed(&self) -> bool {
        self.flags & SSMF_FLAG_COMPRESSED != 0
    }

    /// Check if debug info is included.
    pub fn has_debug(&self) -> bool {
        self.flags & SSMF_FLAG_DEBUG != 0
    }

    /// Read header from bytes.
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        if bytes.len() < Self::SIZE {
            return None;
        }

        // Safety: SettlementHeader is repr(C) and contains only primitive types
        let header = unsafe { std::ptr::read_unaligned(bytes.as_ptr() as *const SettlementHeader) };

        if header.is_valid() {
            Some(header)
        } else {
            None
        }
    }

    /// Write header to bytes.
    pub fn to_bytes(&self) -> [u8; Self::SIZE] {
        let mut bytes = [0u8; Self::SIZE];
        // Safety: SettlementHeader is repr(C) and contains only primitive types
        unsafe {
            std::ptr::write_unaligned(bytes.as_mut_ptr() as *mut SettlementHeader, *self);
        }
        bytes
    }

    /// Read header from reader.
    pub fn read_from<R: Read>(reader: &mut R) -> std::io::Result<Self> {
        let mut bytes = [0u8; Self::SIZE];
        reader.read_exact(&mut bytes)?;
        Self::from_bytes(&bytes).ok_or_else(|| {
            std::io::Error::new(std::io::ErrorKind::InvalidData, "Invalid settlement header")
        })
    }

    /// Write header to writer.
    pub fn write_to<W: Write>(&self, writer: &mut W) -> std::io::Result<()> {
        writer.write_all(&self.to_bytes())
    }
}

// Alias for backward compatibility
pub const SSMF_FLAG_HAS_NATIVE_LIBS: u16 = SSMF_FLAG_HAS_NATIVES;

/// Native library entry in settlement.
#[repr(C)]
#[derive(Debug, Clone, Copy, Default)]
pub struct NativeLibEntry {
    /// Offset to library name string (in string table)
    pub name_offset: u32,
    /// Library type (STATIC, SHARED, SYSTEM)
    pub lib_type: u8,
    /// Flags (reserved)
    pub flags: u8,
    /// Reserved for alignment
    pub reserved: [u8; 2],
    /// For STATIC: offset to embedded library data
    /// For SHARED: unused
    pub data_offset: u64,
    /// For STATIC: size of embedded library
    /// For SHARED: unused
    pub data_size: u64,
    /// For SHARED: offset to path string in string table
    pub path_offset: u32,
    /// Number of exported symbols
    pub symbol_count: u32,
    /// Offset to exported symbols list
    pub symbols_offset: u32,
    /// Reserved
    pub _reserved: u32,
}

impl NativeLibEntry {
    pub const SIZE: usize = std::mem::size_of::<Self>();

    /// Check if this is a statically linked library.
    pub fn is_static(&self) -> bool {
        self.lib_type == NATIVE_LIB_STATIC
    }

    /// Check if this is a shared library.
    pub fn is_shared(&self) -> bool {
        self.lib_type == NATIVE_LIB_SHARED
    }

    /// Check if this is a system library.
    pub fn is_system(&self) -> bool {
        self.lib_type == NATIVE_LIB_SYSTEM
    }
}

/// Module entry in settlement registry.
#[repr(C)]
#[derive(Debug, Clone, Copy, Default)]
pub struct ModuleTableEntry {
    /// Offset to module name string
    pub name_offset: u32,
    /// Module version (for compatibility checking)
    pub version: u32,
    /// Module flags
    pub flags: u16,
    /// Reserved
    pub _reserved: u16,
    /// Start slot in code region
    pub code_start: u32,
    /// End slot in code region
    pub code_end: u32,
    /// Start slot in data region
    pub data_start: u32,
    /// End slot in data region
    pub data_end: u32,
    /// First function table index for this module
    pub func_start: u32,
    /// Number of functions from this module
    pub func_count: u32,
    /// First global table index for this module
    pub global_start: u32,
    /// Number of globals from this module
    pub global_count: u32,
    /// First type table index for this module
    pub type_start: u32,
    /// Number of types from this module
    pub type_count: u32,
    /// Offset into dependency table for this module's dependencies
    pub dep_start: u32,
    /// Number of dependencies
    pub dep_count: u32,
}

impl ModuleTableEntry {
    pub const SIZE: usize = std::mem::size_of::<Self>();
}

/// Alias for backward compatibility
pub type ModuleRegistryEntry = ModuleTableEntry;

/// Function table entry for indirection.
#[repr(C)]
#[derive(Debug, Clone, Copy, Default)]
pub struct FuncTableEntry {
    /// Pointer to function code (updated atomically for hot reload)
    pub code_ptr: u64,
    /// Module ID this function belongs to
    pub module_id: u16,
    /// Function version (for compatibility)
    pub version: u16,
    /// Flags (VALID, TOMBSTONE, TRAMPOLINE)
    pub flags: u32,
}

pub const FUNC_FLAG_VALID: u32 = 0x0001;
pub const FUNC_FLAG_TOMBSTONE: u32 = 0x0002;
pub const FUNC_FLAG_TRAMPOLINE: u32 = 0x0004;

impl FuncTableEntry {
    pub const SIZE: usize = std::mem::size_of::<Self>();

    pub fn is_valid(&self) -> bool {
        self.flags & FUNC_FLAG_VALID != 0 && self.flags & FUNC_FLAG_TOMBSTONE == 0
    }
}

/// Global table entry for indirection.
#[repr(C)]
#[derive(Debug, Clone, Copy, Default)]
pub struct GlobalTableEntry {
    /// Pointer to global data
    pub data_ptr: u64,
    /// Size of global data
    pub size: u32,
    /// Module ID this global belongs to
    pub module_id: u16,
    /// Flags
    pub flags: u16,
}

impl GlobalTableEntry {
    pub const SIZE: usize = std::mem::size_of::<Self>();
}

/// Type table entry for type info.
#[repr(C)]
#[derive(Debug, Clone, Copy, Default)]
pub struct TypeTableEntry {
    /// Pointer to type info structure
    pub type_ptr: u64,
    /// Hash of type layout (for compatibility checking)
    pub layout_hash: u32,
    /// Module ID this type belongs to
    pub module_id: u16,
    /// Flags
    pub flags: u16,
}

impl TypeTableEntry {
    pub const SIZE: usize = std::mem::size_of::<Self>();
}

/// Dependency entry in module registry.
#[repr(C)]
#[derive(Debug, Clone, Copy, Default)]
pub struct DependencyEntry {
    /// Index of dependent module in registry
    pub module_idx: u32,
    /// Required version (0 = any)
    pub required_version: u32,
}

impl DependencyEntry {
    pub const SIZE: usize = std::mem::size_of::<Self>();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_header_size() {
        // Ensure header size is stable for binary compatibility
        assert!(SettlementHeader::SIZE >= 128);
    }

    #[test]
    fn test_header_roundtrip() {
        let mut header = SettlementHeader::new();
        header.flags = SSMF_FLAG_EXECUTABLE | SSMF_FLAG_HAS_NATIVES;
        header.module_count = 5;
        header.code_size = 0x10000;

        let bytes = header.to_bytes();
        let restored = SettlementHeader::from_bytes(&bytes).unwrap();

        assert_eq!(restored.magic, SSMF_MAGIC);
        assert_eq!(restored.flags, header.flags);
        assert_eq!(restored.module_count, 5);
        assert_eq!(restored.code_size, 0x10000);
    }

    #[test]
    fn test_header_flags() {
        let mut header = SettlementHeader::new();
        assert!(!header.is_executable());
        assert!(!header.has_natives());

        header.flags = SSMF_FLAG_EXECUTABLE | SSMF_FLAG_HAS_NATIVES | SSMF_FLAG_DEBUG;
        assert!(header.is_executable());
        assert!(header.has_natives());
        assert!(header.has_debug());
        assert!(!header.is_compressed());
    }

    #[test]
    fn test_native_lib_entry() {
        let entry = NativeLibEntry {
            lib_type: NATIVE_LIB_STATIC,
            ..Default::default()
        };
        assert!(entry.is_static());
        assert!(!entry.is_shared());
    }
}
