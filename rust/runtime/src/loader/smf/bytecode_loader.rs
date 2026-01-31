//! SMF bytecode loader.
//!
//! Reads bytecode functions from SMF files and prepares them for execution
//! by the bytecode VM.

use std::io::{self, Read, Seek, SeekFrom};

use super::bytecode_writer::{BytecodeFuncEntry, BYTECODE_MAGIC, BYTECODE_VERSION};
use super::header::SmfHeader;
use super::section::{SectionType, SmfSection};

/// A loaded bytecode module ready for VM execution.
#[derive(Debug)]
pub struct LoadedBytecodeModule {
    /// All bytecode from the code section (raw bytes).
    pub code: Vec<u8>,
    /// Function metadata entries.
    pub functions: Vec<LoadedFunction>,
    /// String table.
    pub string_table: Vec<u8>,
}

/// A loaded function entry.
#[derive(Debug, Clone)]
pub struct LoadedFunction {
    /// Function name.
    pub name: String,
    /// Offset of bytecode within the code buffer.
    pub code_offset: usize,
    /// Length of bytecode.
    pub code_length: usize,
    /// Number of parameters.
    pub param_count: u16,
    /// Number of local variables.
    pub local_count: u16,
}

/// Load error types.
#[derive(Debug)]
pub enum LoadError {
    /// I/O error.
    Io(io::Error),
    /// Invalid SMF magic.
    InvalidMagic,
    /// Invalid bytecode magic (expected "BCOD").
    InvalidBytecodeMagic,
    /// Unsupported bytecode version.
    UnsupportedVersion(u16),
    /// Code section not found.
    NoCodeSection,
    /// Section data truncated.
    TruncatedSection,
}

impl std::fmt::Display for LoadError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LoadError::Io(e) => write!(f, "I/O error: {}", e),
            LoadError::InvalidMagic => write!(f, "Invalid SMF magic number"),
            LoadError::InvalidBytecodeMagic => write!(f, "Invalid bytecode magic (expected BCOD)"),
            LoadError::UnsupportedVersion(v) => write!(f, "Unsupported bytecode version: {}", v),
            LoadError::NoCodeSection => write!(f, "No code section found in SMF file"),
            LoadError::TruncatedSection => write!(f, "Section data is truncated"),
        }
    }
}

impl std::error::Error for LoadError {}

impl From<io::Error> for LoadError {
    fn from(e: io::Error) -> Self {
        LoadError::Io(e)
    }
}

/// Load a bytecode module from an SMF file.
pub fn load_bytecode_module<R: Read + Seek>(reader: &mut R) -> Result<LoadedBytecodeModule, LoadError> {
    // Read SMF header
    let header = read_header(reader)?;

    // Read section table
    reader.seek(SeekFrom::Start(header.section_table_offset))?;
    let sections = read_section_table(reader, header.section_count)?;

    // Find Code section
    let code_section = sections
        .iter()
        .find(|s| s.section_type == SectionType::Code)
        .ok_or(LoadError::NoCodeSection)?;

    // Read code section data
    reader.seek(SeekFrom::Start(code_section.offset))?;
    let mut code_data = vec![0u8; code_section.size as usize];
    reader.read_exact(&mut code_data)?;

    // Parse bytecode header within code section
    if code_data.len() < 10 {
        return Err(LoadError::TruncatedSection);
    }

    // Check BCOD magic
    if &code_data[0..4] != BYTECODE_MAGIC {
        return Err(LoadError::InvalidBytecodeMagic);
    }

    // Check version
    let version = u16::from_le_bytes([code_data[4], code_data[5]]);
    if version != BYTECODE_VERSION {
        return Err(LoadError::UnsupportedVersion(version));
    }

    // Read function count
    let func_count = u32::from_le_bytes([code_data[6], code_data[7], code_data[8], code_data[9]]);

    // Read function entries
    let entry_size = std::mem::size_of::<BytecodeFuncEntry>();
    let entries_start = 10; // After magic + version + count
    let mut functions = Vec::with_capacity(func_count as usize);

    // Read string table (if present)
    let strtab_section = sections.iter().find(|s| s.section_type == SectionType::StrTab);
    let string_table = if let Some(strtab) = strtab_section {
        reader.seek(SeekFrom::Start(strtab.offset))?;
        let mut data = vec![0u8; strtab.size as usize];
        reader.read_exact(&mut data)?;
        data
    } else {
        Vec::new()
    };

    for i in 0..func_count as usize {
        let offset = entries_start + i * entry_size;
        if offset + entry_size > code_data.len() {
            return Err(LoadError::TruncatedSection);
        }

        let entry: BytecodeFuncEntry = unsafe {
            std::ptr::read(code_data[offset..].as_ptr() as *const BytecodeFuncEntry)
        };

        // Read function name from string table
        let name = read_string_at(&string_table, entry.name_offset as usize);

        functions.push(LoadedFunction {
            name,
            code_offset: entry.code_offset as usize,
            code_length: entry.code_length as usize,
            param_count: entry.param_count,
            local_count: entry.local_count,
        });
    }

    // Extract raw bytecode (everything in code_data is the bytecode)
    Ok(LoadedBytecodeModule {
        code: code_data,
        functions,
        string_table,
    })
}

/// Read the SMF header from a reader.
fn read_header<R: Read>(reader: &mut R) -> Result<SmfHeader, LoadError> {
    let mut buf = [0u8; std::mem::size_of::<SmfHeader>()];
    reader.read_exact(&mut buf)?;

    if &buf[0..4] != super::header::SMF_MAGIC {
        return Err(LoadError::InvalidMagic);
    }

    let header: SmfHeader = unsafe { std::ptr::read(buf.as_ptr() as *const SmfHeader) };
    Ok(header)
}

/// Read the section table.
fn read_section_table<R: Read>(reader: &mut R, count: u32) -> Result<Vec<SmfSection>, LoadError> {
    let entry_size = std::mem::size_of::<SmfSection>();
    let mut sections = Vec::with_capacity(count as usize);

    for _ in 0..count {
        let mut buf = vec![0u8; entry_size];
        reader.read_exact(&mut buf)?;
        let section: SmfSection = unsafe { std::ptr::read(buf.as_ptr() as *const SmfSection) };
        sections.push(section);
    }

    Ok(sections)
}

/// Read a null-terminated string from a byte buffer.
fn read_string_at(data: &[u8], offset: usize) -> String {
    if offset >= data.len() {
        return String::new();
    }
    let end = data[offset..]
        .iter()
        .position(|&b| b == 0)
        .map(|pos| offset + pos)
        .unwrap_or(data.len());
    String::from_utf8_lossy(&data[offset..end]).to_string()
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::super::smf::bytecode_writer::{BytecodeFunction, SmfBytecodeWriter};
    use std::io::Cursor;

    #[test]
    fn test_roundtrip_single_function() {
        // Write
        let mut writer = SmfBytecodeWriter::new();
        writer.add_function(BytecodeFunction {
            name: "main".to_string(),
            code: vec![0x01, 0x00, 0x00, 0x00, 42, 0, 0, 0, 0, 0, 0, 0, 0x45, 0x00],
            param_count: 0,
            local_count: 1,
        });
        let data = writer.write_to_vec().expect("Write failed");

        // Read
        let mut cursor = Cursor::new(&data);
        let module = load_bytecode_module(&mut cursor).expect("Load failed");

        assert_eq!(module.functions.len(), 1);
        assert_eq!(module.functions[0].name, "main");
        assert_eq!(module.functions[0].param_count, 0);
        assert_eq!(module.functions[0].local_count, 1);
    }

    #[test]
    fn test_roundtrip_multiple_functions() {
        let mut writer = SmfBytecodeWriter::new();
        writer.add_function(BytecodeFunction {
            name: "add".to_string(),
            code: vec![0x20, 0x00],
            param_count: 2,
            local_count: 3,
        });
        writer.add_function(BytecodeFunction {
            name: "sub".to_string(),
            code: vec![0x21, 0x00],
            param_count: 2,
            local_count: 3,
        });
        let data = writer.write_to_vec().expect("Write failed");

        let mut cursor = Cursor::new(&data);
        let module = load_bytecode_module(&mut cursor).expect("Load failed");

        assert_eq!(module.functions.len(), 2);
        assert_eq!(module.functions[0].name, "add");
        assert_eq!(module.functions[1].name, "sub");
    }

    #[test]
    fn test_invalid_magic() {
        let data = vec![0x00; 256]; // All zeros
        let mut cursor = Cursor::new(&data);
        let result = load_bytecode_module(&mut cursor);
        assert!(result.is_err());
    }
}
