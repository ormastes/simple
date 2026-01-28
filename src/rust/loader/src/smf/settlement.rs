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

    // Template table (for generic constructs)
    /// Offset to template table
    pub template_table_offset: u64,
    /// Size of template table
    pub template_table_size: u64,

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
    /// Number of entries in template table
    pub template_table_count: u32,

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
        Self::from_bytes(&bytes)
            .ok_or_else(|| std::io::Error::new(std::io::ErrorKind::InvalidData, "Invalid settlement header"))
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

/// Template table for generic constructs.
/// Stores serialized MIR/AST for generic functions, structs, enums, and traits.
#[derive(Debug, Clone, Default)]
pub struct TemplateTable {
    /// Template entries for all generic constructs
    pub entries: Vec<TemplateEntry>,
}

impl TemplateTable {
    pub fn new() -> Self {
        Self {
            entries: Vec::new(),
        }
    }

    /// Add a template entry
    pub fn add_entry(&mut self, entry: TemplateEntry) {
        self.entries.push(entry);
    }

    /// Get template entry name from string table with bounds checking
    pub fn entry_name<'a>(&self, entry: &TemplateEntry, string_table: &'a [u8]) -> &'a str {
        let name_offset = entry.name_offset as usize;

        // Bounds check on start offset
        if name_offset >= string_table.len() {
            return "";
        }

        // Find null terminator
        let end = string_table
            .get(name_offset..)
            .and_then(|rest| rest.iter().position(|&b| b == 0).map(|i| name_offset + i))
            .unwrap_or(string_table.len());

        // Validate range before slicing
        if end > string_table.len() {
            return "";
        }

        // Convert to string
        std::str::from_utf8(&string_table[name_offset..end]).unwrap_or("")
    }

    /// Find a template by name
    /// Requires the string table to resolve name offsets
    pub fn find_by_name(&self, name: &str, string_table: &[u8]) -> Option<&TemplateEntry> {
        self.entries.iter().find(|e| {
            self.entry_name(e, string_table) == name
        })
    }
}

/// Template entry for a single generic construct.
#[repr(C)]
#[derive(Debug, Clone, Copy, Default)]
pub struct TemplateEntry {
    /// Offset to template name in string table
    pub name_offset: u32,
    /// Generic kind: 0=Function, 1=Struct, 2=Enum, 3=Trait
    pub kind: u8,
    /// Number of generic type parameters
    pub generic_param_count: u8,
    /// Reserved for alignment
    pub reserved: [u8; 2],
    /// Offset to serialized MIR/AST in TemplateCode section
    pub mir_offset: u64,
    /// Size of serialized MIR/AST
    pub mir_size: u32,
    /// Offset to specializations list in TemplateMeta section
    pub specializations_offset: u64,
    /// Number of specializations
    pub specializations_count: u32,
    /// Reserved for future use
    pub _reserved: u32,
}

impl TemplateEntry {
    pub const SIZE: usize = std::mem::size_of::<Self>();

    /// Template kind constants
    pub const KIND_FUNCTION: u8 = 0;
    pub const KIND_STRUCT: u8 = 1;
    pub const KIND_ENUM: u8 = 2;
    pub const KIND_TRAIT: u8 = 3;

    /// Check if this is a function template
    pub fn is_function(&self) -> bool {
        self.kind == Self::KIND_FUNCTION
    }

    /// Check if this is a struct template
    pub fn is_struct(&self) -> bool {
        self.kind == Self::KIND_STRUCT
    }

    /// Check if this is an enum template
    pub fn is_enum(&self) -> bool {
        self.kind == Self::KIND_ENUM
    }

    /// Check if this is a trait template
    pub fn is_trait(&self) -> bool {
        self.kind == Self::KIND_TRAIT
    }
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

    #[test]
    fn test_template_table_string_lookup() {
        // Create a string table with null-terminated strings
        let mut string_table = Vec::new();
        let offset1 = string_table.len() as u32;
        string_table.extend_from_slice(b"my_function\0");
        let offset2 = string_table.len() as u32;
        string_table.extend_from_slice(b"MyStruct\0");
        let offset3 = string_table.len() as u32;
        string_table.extend_from_slice(b"MyEnum\0");

        // Create template entries
        let entry1 = TemplateEntry {
            name_offset: offset1,
            kind: TemplateEntry::KIND_FUNCTION,
            generic_param_count: 2,
            ..Default::default()
        };
        let entry2 = TemplateEntry {
            name_offset: offset2,
            kind: TemplateEntry::KIND_STRUCT,
            generic_param_count: 1,
            ..Default::default()
        };
        let entry3 = TemplateEntry {
            name_offset: offset3,
            kind: TemplateEntry::KIND_ENUM,
            generic_param_count: 0,
            ..Default::default()
        };

        // Create template table
        let mut table = TemplateTable::new();
        table.add_entry(entry1);
        table.add_entry(entry2);
        table.add_entry(entry3);

        // Test entry_name
        assert_eq!(table.entry_name(&entry1, &string_table), "my_function");
        assert_eq!(table.entry_name(&entry2, &string_table), "MyStruct");
        assert_eq!(table.entry_name(&entry3, &string_table), "MyEnum");

        // Test find_by_name
        let found1 = table.find_by_name("my_function", &string_table);
        assert!(found1.is_some());
        assert_eq!(found1.unwrap().kind, TemplateEntry::KIND_FUNCTION);
        assert_eq!(found1.unwrap().generic_param_count, 2);

        let found2 = table.find_by_name("MyStruct", &string_table);
        assert!(found2.is_some());
        assert_eq!(found2.unwrap().kind, TemplateEntry::KIND_STRUCT);
        assert_eq!(found2.unwrap().generic_param_count, 1);

        let found3 = table.find_by_name("MyEnum", &string_table);
        assert!(found3.is_some());
        assert_eq!(found3.unwrap().kind, TemplateEntry::KIND_ENUM);

        // Test not found
        let not_found = table.find_by_name("NonExistent", &string_table);
        assert!(not_found.is_none());
    }

    #[test]
    fn test_template_entry_kind_checks() {
        let func_entry = TemplateEntry {
            kind: TemplateEntry::KIND_FUNCTION,
            ..Default::default()
        };
        assert!(func_entry.is_function());
        assert!(!func_entry.is_struct());

        let struct_entry = TemplateEntry {
            kind: TemplateEntry::KIND_STRUCT,
            ..Default::default()
        };
        assert!(struct_entry.is_struct());
        assert!(!struct_entry.is_function());

        let enum_entry = TemplateEntry {
            kind: TemplateEntry::KIND_ENUM,
            ..Default::default()
        };
        assert!(enum_entry.is_enum());
        assert!(!enum_entry.is_trait());

        let trait_entry = TemplateEntry {
            kind: TemplateEntry::KIND_TRAIT,
            ..Default::default()
        };
        assert!(trait_entry.is_trait());
        assert!(!trait_entry.is_enum());
    }
}
