use std::collections::HashMap;
use std::io::{self, Write};
use thiserror::Error;

use crate::mir::MirModule;

/// SMF file constants
pub const SMF_MAGIC: &[u8; 4] = b"SMF\0";
pub const SMF_VERSION_MAJOR: u8 = 0;
pub const SMF_VERSION_MINOR: u8 = 1;

/// SMF section types
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SmfSectionType {
    Code = 1,
    Data = 2,
    Rodata = 3,
    Bss = 4,
    Reloc = 5,
    Symtab = 6,
    Strtab = 7,
    Debug = 8,
}

/// SMF symbol binding
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SymbolBinding {
    Local = 0,
    Global = 1,
    Weak = 2,
}

/// SMF symbol type
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SymbolType {
    None = 0,
    Function = 1,
    Data = 2,
}

/// SMF relocation type
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RelocationType {
    Abs64 = 1,
    Rel32 = 2,
    Plt32 = 3,
}

#[derive(Error, Debug)]
pub enum SmfWriteError {
    #[error("IO error: {0}")]
    Io(#[from] io::Error),

    #[error("Invalid data: {0}")]
    InvalidData(String),
}

pub type SmfWriteResult<T> = Result<T, SmfWriteError>;

/// Symbol entry for SMF
#[derive(Debug, Clone)]
pub struct SmfSymbol {
    pub name: String,
    pub binding: SymbolBinding,
    pub sym_type: SymbolType,
    pub section_index: u16,
    pub value: u64,
    pub size: u64,
}

/// Relocation entry for SMF
#[derive(Debug, Clone)]
pub struct SmfRelocation {
    pub offset: u64,
    pub symbol_index: u32,
    pub reloc_type: RelocationType,
    pub addend: i64,
}

/// SMF section
#[derive(Debug, Clone)]
pub struct SmfSection {
    pub name: String,
    pub section_type: SmfSectionType,
    pub flags: u32,
    pub data: Vec<u8>,
    pub alignment: u32,
}

/// SMF writer for creating SMF files from compiled code
pub struct SmfWriter {
    sections: Vec<SmfSection>,
    symbols: Vec<SmfSymbol>,
    relocations: Vec<SmfRelocation>,
    string_table: Vec<u8>,
    string_offsets: HashMap<String, u32>,
}

impl SmfWriter {
    pub fn new() -> Self {
        let mut writer = Self {
            sections: Vec::new(),
            symbols: Vec::new(),
            relocations: Vec::new(),
            string_table: Vec::new(),
            string_offsets: HashMap::new(),
        };

        // Add empty string at offset 0
        writer.string_table.push(0);

        writer
    }

    /// Add a string to the string table, returning its offset
    pub fn add_string(&mut self, s: &str) -> u32 {
        if let Some(&offset) = self.string_offsets.get(s) {
            return offset;
        }

        let offset = self.string_table.len() as u32;
        self.string_table.extend_from_slice(s.as_bytes());
        self.string_table.push(0);
        self.string_offsets.insert(s.to_string(), offset);
        offset
    }

    /// Add a code section
    pub fn add_code_section(&mut self, name: &str, code: Vec<u8>) -> usize {
        let section = SmfSection {
            name: name.to_string(),
            section_type: SmfSectionType::Code,
            flags: 0x5, // Read + Execute
            data: code,
            alignment: 16,
        };
        let index = self.sections.len();
        self.sections.push(section);
        index
    }

    /// Add a data section
    pub fn add_data_section(&mut self, name: &str, data: Vec<u8>, readonly: bool) -> usize {
        let section = SmfSection {
            name: name.to_string(),
            section_type: if readonly { SmfSectionType::Rodata } else { SmfSectionType::Data },
            flags: if readonly { 0x1 } else { 0x3 }, // Read or Read+Write
            data,
            alignment: 8,
        };
        let index = self.sections.len();
        self.sections.push(section);
        index
    }

    /// Add a symbol
    pub fn add_symbol(&mut self, symbol: SmfSymbol) -> u32 {
        let index = self.symbols.len() as u32;
        self.symbols.push(symbol);
        index
    }

    /// Add a relocation
    pub fn add_relocation(&mut self, reloc: SmfRelocation) {
        self.relocations.push(reloc);
    }

    /// Write SMF file to a writer
    pub fn write<W: Write>(&mut self, writer: &mut W) -> SmfWriteResult<()> {
        // Build string table section
        let strtab_section = SmfSection {
            name: ".strtab".to_string(),
            section_type: SmfSectionType::Strtab,
            flags: 0,
            data: self.string_table.clone(),
            alignment: 1,
        };
        self.sections.push(strtab_section);

        // Calculate offsets
        let header_size = 64;
        let section_header_size = 48;
        let section_table_offset = header_size;
        let section_table_size = self.sections.len() * section_header_size;

        let mut data_offset = section_table_offset + section_table_size;
        let mut section_offsets = Vec::new();

        for section in &self.sections {
            // Align
            let align = section.alignment as usize;
            if align > 0 {
                data_offset = (data_offset + align - 1) & !(align - 1);
            }
            section_offsets.push(data_offset);
            data_offset += section.data.len();
        }

        // Write header
        writer.write_all(SMF_MAGIC)?;
        writer.write_all(&[SMF_VERSION_MAJOR, SMF_VERSION_MINOR])?;
        writer.write_all(&[0u8; 2])?; // Platform, Arch
        writer.write_all(&0u32.to_le_bytes())?; // Flags
        writer.write_all(&(self.sections.len() as u32).to_le_bytes())?;
        writer.write_all(&(section_table_offset as u64).to_le_bytes())?;
        writer.write_all(&(self.symbols.len() as u32).to_le_bytes())?;
        writer.write_all(&0u32.to_le_bytes())?; // Entry point symbol index
        writer.write_all(&[0u8; 32])?; // Reserved

        // Pre-compute name offsets (add all names to string table first)
        let name_offsets: Vec<u32> = self.sections.iter()
            .map(|s| s.name.clone())
            .collect::<Vec<_>>()
            .into_iter()
            .map(|name| self.add_string(&name))
            .collect();

        // Write section headers
        for (i, section) in self.sections.iter().enumerate() {
            writer.write_all(&name_offsets[i].to_le_bytes())?;
            writer.write_all(&[section.section_type as u8])?;
            writer.write_all(&[0u8; 3])?; // Padding
            writer.write_all(&section.flags.to_le_bytes())?;
            writer.write_all(&(section_offsets[i] as u64).to_le_bytes())?;
            writer.write_all(&(section.data.len() as u64).to_le_bytes())?;
            writer.write_all(&(section.data.len() as u64).to_le_bytes())?; // Virtual size
            writer.write_all(&section.alignment.to_le_bytes())?;
            writer.write_all(&[0u8; 12])?; // Reserved
        }

        // Write section data with padding
        let mut current_offset = section_table_offset + section_table_size;
        for (i, section) in self.sections.iter().enumerate() {
            let target_offset = section_offsets[i];
            while current_offset < target_offset {
                writer.write_all(&[0])?;
                current_offset += 1;
            }
            writer.write_all(&section.data)?;
            current_offset += section.data.len();
        }

        Ok(())
    }

    /// Create SMF from object code and MIR module
    pub fn from_object_code(object_code: &[u8], mir: &MirModule) -> SmfWriteResult<Self> {
        let mut writer = Self::new();

        // Add code section with object code
        // Note: In a real implementation, we'd parse the object file and extract sections
        writer.add_code_section(".text", object_code.to_vec());

        // Add symbols for each function
        for (i, func) in mir.functions.iter().enumerate() {
            let symbol = SmfSymbol {
                name: func.name.clone(),
                binding: if func.is_public { SymbolBinding::Global } else { SymbolBinding::Local },
                sym_type: SymbolType::Function,
                section_index: 0, // .text section
                value: 0, // Would need to get from object file
                size: 0,
            };
            writer.add_symbol(symbol);
        }

        Ok(writer)
    }
}

impl Default for SmfWriter {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_string_table() {
        let mut writer = SmfWriter::new();

        let off1 = writer.add_string("hello");
        let off2 = writer.add_string("world");
        let off3 = writer.add_string("hello"); // Duplicate

        assert_eq!(off1, 1); // After initial null
        assert_eq!(off2, 7); // After "hello\0"
        assert_eq!(off3, off1); // Same as first "hello"
    }

    #[test]
    fn test_add_code_section() {
        let mut writer = SmfWriter::new();

        let code = vec![0xC3]; // ret
        let idx = writer.add_code_section(".text", code);

        assert_eq!(idx, 0);
        assert_eq!(writer.sections.len(), 1);
        assert_eq!(writer.sections[0].section_type, SmfSectionType::Code);
    }

    #[test]
    fn test_add_symbol() {
        let mut writer = SmfWriter::new();

        let sym = SmfSymbol {
            name: "main".to_string(),
            binding: SymbolBinding::Global,
            sym_type: SymbolType::Function,
            section_index: 0,
            value: 0,
            size: 10,
        };

        let idx = writer.add_symbol(sym);
        assert_eq!(idx, 0);
        assert_eq!(writer.symbols.len(), 1);
    }

    #[test]
    fn test_write_smf() {
        let mut writer = SmfWriter::new();

        writer.add_code_section(".text", vec![0xC3]);
        writer.add_symbol(SmfSymbol {
            name: "entry".to_string(),
            binding: SymbolBinding::Global,
            sym_type: SymbolType::Function,
            section_index: 0,
            value: 0,
            size: 1,
        });

        let mut output = Vec::new();
        writer.write(&mut output).unwrap();

        // Check magic
        assert_eq!(&output[0..4], SMF_MAGIC);
        assert!(!output.is_empty());
    }

    #[test]
    fn test_smf_header_format() {
        let mut writer = SmfWriter::new();
        writer.add_code_section(".text", vec![0x90, 0xC3]); // nop, ret

        let mut output = Vec::new();
        writer.write(&mut output).unwrap();

        // Magic
        assert_eq!(&output[0..4], b"SMF\0");
        // Version
        assert_eq!(output[4], SMF_VERSION_MAJOR);
        assert_eq!(output[5], SMF_VERSION_MINOR);
    }
}
