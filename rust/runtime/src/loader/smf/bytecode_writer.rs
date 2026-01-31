//! SMF bytecode writer.
//!
//! Writes compiled bytecode functions into SMF files with proper section
//! layout, constant pools, and function metadata.
//!
//! **SMF Bytecode File Layout:**
//! ```text
//! ┌────────────────────────────────────────┐
//! │ SMF Header (128 bytes)                 │
//! ├────────────────────────────────────────┤
//! │ Section Table (SmfSection entries)     │
//! ├────────────────────────────────────────┤
//! │ Code Section (bytecode functions)      │
//! │   ┌──────────────────────────────────┐ │
//! │   │ "BCOD" magic (4 bytes)           │ │
//! │   │ Version: u16                     │ │
//! │   │ Function count: u32              │ │
//! │   │ ┌────────────────────────────┐   │ │
//! │   │ │ Function metadata table    │   │ │
//! │   │ │ (offset, len, params, etc) │   │ │
//! │   │ └────────────────────────────┘   │ │
//! │   │ ┌────────────────────────────┐   │ │
//! │   │ │ Bytecode instructions      │   │ │
//! │   │ └────────────────────────────┘   │ │
//! │   └──────────────────────────────────┘ │
//! ├────────────────────────────────────────┤
//! │ Data Section (constant pool)           │
//! │   [RuntimeValue constants]             │
//! ├────────────────────────────────────────┤
//! │ StrTab Section (string constants)      │
//! │   [null-terminated strings]            │
//! ├────────────────────────────────────────┤
//! │ SymTab Section (symbol table)          │
//! │   [SmfSymbol entries]                  │
//! └────────────────────────────────────────┘
//! ```

use std::io::{self, Write};

use super::header::{SmfHeader, SMF_MAGIC};
use super::section::{
    SectionType, SmfSection, SECTION_FLAG_EXEC, SECTION_FLAG_READ,
};

/// Bytecode section magic marker.
pub const BYTECODE_MAGIC: &[u8; 4] = b"BCOD";

/// Bytecode section version.
pub const BYTECODE_VERSION: u16 = 1;

/// Metadata for a single bytecode function within the Code section.
#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct BytecodeFuncEntry {
    /// Offset of bytecode within the code section (after header).
    pub code_offset: u32,
    /// Length of bytecode in bytes.
    pub code_length: u32,
    /// Number of parameters.
    pub param_count: u16,
    /// Number of local variables (including parameters).
    pub local_count: u16,
    /// Offset of function name in string table.
    pub name_offset: u32,
}

/// A compiled bytecode function ready for writing.
pub struct BytecodeFunction {
    /// Function name.
    pub name: String,
    /// Compiled bytecode.
    pub code: Vec<u8>,
    /// Number of parameters.
    pub param_count: u16,
    /// Number of local variables.
    pub local_count: u16,
}

/// Constant pool entry types.
#[repr(u8)]
#[derive(Debug, Clone, Copy)]
pub enum ConstantType {
    /// 64-bit signed integer.
    Int64 = 0,
    /// 64-bit float.
    Float64 = 1,
    /// Boolean (true/false).
    Bool = 2,
    /// Nil value.
    Nil = 3,
    /// String constant (offset into string table).
    String = 4,
}

/// A constant in the data section.
#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct ConstantEntry {
    /// Type of constant.
    pub const_type: ConstantType,
    /// Padding for alignment.
    pub _pad: [u8; 7],
    /// Raw value (i64 for int, f64 bits for float, 0/1 for bool, string offset for string).
    pub value: u64,
}

/// SMF bytecode file writer.
///
/// Builds and writes an SMF file containing bytecode functions.
pub struct SmfBytecodeWriter {
    /// Functions to write.
    functions: Vec<BytecodeFunction>,
    /// String constants (string table).
    strings: Vec<String>,
}

impl SmfBytecodeWriter {
    /// Create a new writer.
    pub fn new() -> Self {
        Self {
            functions: Vec::new(),
            strings: Vec::new(),
        }
    }

    /// Add a compiled function.
    pub fn add_function(&mut self, func: BytecodeFunction) {
        self.functions.push(func);
    }

    /// Add a string constant, returning its offset in the string table.
    pub fn add_string(&mut self, s: String) -> u32 {
        let offset = self.strings.iter().map(|s| s.len() + 1).sum::<usize>() as u32;
        self.strings.push(s);
        offset
    }

    /// Build the string table (null-terminated strings).
    fn build_string_table(&self) -> Vec<u8> {
        let mut table = Vec::new();
        for s in &self.strings {
            table.extend_from_slice(s.as_bytes());
            table.push(0); // null terminator
        }
        // Add function names
        for func in &self.functions {
            table.extend_from_slice(func.name.as_bytes());
            table.push(0);
        }
        table
    }

    /// Build the code section (bytecode functions with metadata).
    fn build_code_section(&self) -> Vec<u8> {
        let mut section = Vec::new();

        // Write bytecode magic
        section.extend_from_slice(BYTECODE_MAGIC);

        // Write version
        section.extend_from_slice(&BYTECODE_VERSION.to_le_bytes());

        // Write function count
        section.extend_from_slice(&(self.functions.len() as u32).to_le_bytes());

        // Calculate function metadata table size
        let entry_size = std::mem::size_of::<BytecodeFuncEntry>();
        let metadata_table_size = entry_size * self.functions.len();

        // Calculate code offsets relative to after metadata table
        let code_start = 4 + 2 + 4 + metadata_table_size; // magic + version + count + table
        let mut current_offset = code_start;
        let mut func_entries: Vec<BytecodeFuncEntry> = Vec::new();
        let mut name_offset = 0u32; // Offset in string table for function names

        // Calculate name offsets (after any user strings)
        let user_string_size: u32 = self.strings.iter().map(|s| (s.len() + 1) as u32).sum();

        for func in &self.functions {
            func_entries.push(BytecodeFuncEntry {
                code_offset: current_offset as u32,
                code_length: func.code.len() as u32,
                param_count: func.param_count,
                local_count: func.local_count,
                name_offset: user_string_size + name_offset,
            });
            current_offset += func.code.len();
            name_offset += (func.name.len() + 1) as u32;
        }

        // Write function metadata table
        for entry in &func_entries {
            let bytes = unsafe {
                std::slice::from_raw_parts(
                    entry as *const BytecodeFuncEntry as *const u8,
                    entry_size,
                )
            };
            section.extend_from_slice(bytes);
        }

        // Write function bytecode
        for func in &self.functions {
            section.extend_from_slice(&func.code);
        }

        section
    }

    /// Write the complete SMF file.
    pub fn write<W: Write>(&self, writer: &mut W) -> io::Result<()> {
        // Build sections
        let code_section_data = self.build_code_section();
        let string_table = self.build_string_table();

        // Calculate offsets
        let header_size = std::mem::size_of::<SmfHeader>();
        let section_table_start = header_size;
        let section_count = 2u32; // Code + StrTab
        let section_entry_size = std::mem::size_of::<SmfSection>();
        let section_table_size = section_entry_size * section_count as usize;

        let code_offset = section_table_start + section_table_size;
        let strtab_offset = code_offset + code_section_data.len();

        // Build header
        let header = SmfHeader {
            magic: *SMF_MAGIC,
            version_major: 1,
            version_minor: 1,
            platform: 0, // Any
            arch: 0,     // x86_64
            flags: 0x0001, // SMF_FLAG_EXECUTABLE
            compression: 0,
            compression_level: 0,
            reserved_compression: [0; 2],
            section_count,
            section_table_offset: section_table_start as u64,
            symbol_table_offset: 0,
            symbol_count: self.functions.len() as u32,
            exported_count: self.functions.len() as u32,
            entry_point: 0,
            stub_size: 0,
            smf_data_offset: 0,
            module_hash: 0,
            source_hash: 0,
            app_type: 0,
            window_width: 0,
            window_height: 0,
            prefetch_hint: 0,
            prefetch_file_count: 0,
            reserved: [0; 5],
        };

        // Build section table entries
        let code_section = SmfSection {
            section_type: SectionType::Code,
            flags: SECTION_FLAG_READ | SECTION_FLAG_EXEC,
            offset: code_offset as u64,
            size: code_section_data.len() as u64,
            virtual_size: code_section_data.len() as u64,
            alignment: 8,
            name: section_name(b".code"),
        };

        let strtab_section = SmfSection {
            section_type: SectionType::StrTab,
            flags: SECTION_FLAG_READ,
            offset: strtab_offset as u64,
            size: string_table.len() as u64,
            virtual_size: string_table.len() as u64,
            alignment: 1,
            name: section_name(b".strtab"),
        };

        // Write everything
        write_struct(writer, &header)?;
        write_struct(writer, &code_section)?;
        write_struct(writer, &strtab_section)?;
        writer.write_all(&code_section_data)?;
        writer.write_all(&string_table)?;

        Ok(())
    }

    /// Write the SMF file to a byte vector.
    pub fn write_to_vec(&self) -> io::Result<Vec<u8>> {
        let mut buf = Vec::new();
        self.write(&mut buf)?;
        Ok(buf)
    }
}

impl Default for SmfBytecodeWriter {
    fn default() -> Self {
        Self::new()
    }
}

/// Create a section name from a byte slice (padded to 16 bytes).
fn section_name(name: &[u8]) -> [u8; 16] {
    let mut buf = [0u8; 16];
    let len = name.len().min(15);
    buf[..len].copy_from_slice(&name[..len]);
    buf
}

/// Write a struct as raw bytes.
fn write_struct<W: Write, T>(writer: &mut W, value: &T) -> io::Result<()> {
    let bytes = unsafe {
        std::slice::from_raw_parts(value as *const T as *const u8, std::mem::size_of::<T>())
    };
    writer.write_all(bytes)
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_write_empty_smf() {
        let writer = SmfBytecodeWriter::new();
        let data = writer.write_to_vec().expect("Write failed");

        // Should have at least a header
        assert!(data.len() >= std::mem::size_of::<SmfHeader>());

        // Check magic
        assert_eq!(&data[0..4], SMF_MAGIC);
    }

    #[test]
    fn test_write_single_function() {
        let mut writer = SmfBytecodeWriter::new();

        // Simple function that returns 42
        writer.add_function(BytecodeFunction {
            name: "main".to_string(),
            code: vec![
                0x01, 0x00, // CONST_I64
                0x00, 0x00, // dest = 0
                42, 0, 0, 0, 0, 0, 0, 0, // value = 42
                0x44, 0x00, // RET
                0x00, 0x00, // value = slot 0
            ],
            param_count: 0,
            local_count: 1,
        });

        let data = writer.write_to_vec().expect("Write failed");

        // Check magic
        assert_eq!(&data[0..4], SMF_MAGIC);

        // Check that the code section contains BCOD magic
        let header_size = std::mem::size_of::<SmfHeader>();
        let section_size = std::mem::size_of::<SmfSection>();
        let code_start = header_size + section_size * 2; // 2 sections

        assert_eq!(&data[code_start..code_start + 4], BYTECODE_MAGIC);
    }

    #[test]
    fn test_write_multiple_functions() {
        let mut writer = SmfBytecodeWriter::new();

        writer.add_function(BytecodeFunction {
            name: "add".to_string(),
            code: vec![0x20, 0x00], // ADD_I64
            param_count: 2,
            local_count: 3,
        });

        writer.add_function(BytecodeFunction {
            name: "sub".to_string(),
            code: vec![0x21, 0x00], // SUB_I64
            param_count: 2,
            local_count: 3,
        });

        let data = writer.write_to_vec().expect("Write failed");

        // Check that the code section has function count = 2
        let header_size = std::mem::size_of::<SmfHeader>();
        let section_size = std::mem::size_of::<SmfSection>();
        let code_start = header_size + section_size * 2;

        // After BCOD magic (4 bytes) + version (2 bytes), the function count is a u32
        let func_count_offset = code_start + 4 + 2;
        let func_count = u32::from_le_bytes([
            data[func_count_offset],
            data[func_count_offset + 1],
            data[func_count_offset + 2],
            data[func_count_offset + 3],
        ]);
        assert_eq!(func_count, 2);
    }

    #[test]
    fn test_string_table() {
        let mut writer = SmfBytecodeWriter::new();
        let offset = writer.add_string("hello".to_string());
        assert_eq!(offset, 0);

        let offset2 = writer.add_string("world".to_string());
        assert_eq!(offset2, 6); // "hello\0" = 6 bytes

        writer.add_function(BytecodeFunction {
            name: "test".to_string(),
            code: vec![0x45, 0x00], // RET_VOID
            param_count: 0,
            local_count: 0,
        });

        let data = writer.write_to_vec().expect("Write failed");
        assert!(!data.is_empty());
    }
}
