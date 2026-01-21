use std::collections::HashMap;
use std::io::{self, Write};
use thiserror::Error;

use crate::mir::MirModule;

// Re-export SMF types from loader (single source of truth)
pub use simple_loader::smf::{
    RelocationType, SectionType, SymbolBinding, SymbolType, SECTION_FLAG_EXEC, SECTION_FLAG_READ, SECTION_FLAG_WRITE,
    SMF_FLAG_EXECUTABLE, SMF_MAGIC,
};

/// SMF version constants
pub const SMF_VERSION_MAJOR: u8 = 0;
pub const SMF_VERSION_MINOR: u8 = 1;

/// Data section kind - for formal verification.
/// Replaces boolean `readonly` parameter with explicit enum.
///
/// Lean equivalent:
/// ```lean
/// inductive DataSectionKind
///   | mutable   -- read-write data (.data)
///   | readonly  -- read-only data (.rodata)
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum DataSectionKind {
    /// Mutable data section (.data) - read-write
    #[default]
    Mutable,
    /// Read-only data section (.rodata)
    ReadOnly,
}

impl DataSectionKind {
    /// Check if this is read-only
    pub fn is_readonly(&self) -> bool {
        matches!(self, DataSectionKind::ReadOnly)
    }

    /// Convert to SMF section type
    pub fn to_section_type(&self) -> SectionType {
        match self {
            DataSectionKind::Mutable => SectionType::Data,
            DataSectionKind::ReadOnly => SectionType::RoData,
        }
    }

    /// Get section flags (read-only = 0x1, read-write = 0x3)
    pub fn to_flags(&self) -> u32 {
        match self {
            DataSectionKind::ReadOnly => SECTION_FLAG_READ,
            DataSectionKind::Mutable => SECTION_FLAG_READ | SECTION_FLAG_WRITE,
        }
    }
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
    /// Layout phase for code locality optimization (startup, first_frame, steady, cold)
    pub layout_phase: u8,
    /// Whether this symbol is an event loop anchor point
    pub is_event_loop_anchor: bool,
    /// Whether this symbol's layout is pinned (should not be moved)
    pub layout_pinned: bool,
}

/// Relocation entry for SMF
#[derive(Debug, Clone)]
pub struct SmfRelocation {
    pub offset: u64,
    pub symbol_index: u32,
    pub reloc_type: RelocationType,
    pub addend: i64,
}

/// SMF section for writing
#[derive(Debug, Clone)]
pub struct SmfSection {
    pub name: String,
    pub section_type: SectionType,
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
            section_type: SectionType::Code,
            flags: SECTION_FLAG_READ | SECTION_FLAG_EXEC,
            data: code,
            alignment: 16,
        };
        let index = self.sections.len();
        self.sections.push(section);
        index
    }

    /// Add a data section with the specified kind (mutable or read-only)
    pub fn add_data_section(&mut self, name: &str, data: Vec<u8>, kind: DataSectionKind) -> usize {
        let section = SmfSection {
            name: name.to_string(),
            section_type: kind.to_section_type(),
            flags: kind.to_flags(),
            data,
            alignment: 8,
        };
        let index = self.sections.len();
        self.sections.push(section);
        index
    }

    /// Add a read-only data section (convenience method)
    pub fn add_rodata_section(&mut self, name: &str, data: Vec<u8>) -> usize {
        self.add_data_section(name, data, DataSectionKind::ReadOnly)
    }

    /// Add a mutable data section (convenience method)
    pub fn add_mutable_data_section(&mut self, name: &str, data: Vec<u8>) -> usize {
        self.add_data_section(name, data, DataSectionKind::Mutable)
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
        // Build symbol table section if we have symbols
        if !self.symbols.is_empty() {
            // First, collect all symbol names and add to string table
            let name_offsets: Vec<u32> = self
                .symbols
                .iter()
                .map(|s| s.name.clone())
                .collect::<Vec<_>>()
                .into_iter()
                .map(|name| self.add_string(&name))
                .collect();

            let mut symtab_data = Vec::new();
            for (i, symbol) in self.symbols.iter().enumerate() {
                let name_offset = name_offsets[i];
                symtab_data.extend_from_slice(&name_offset.to_le_bytes());
                symtab_data.push(symbol.binding as u8);
                symtab_data.push(symbol.sym_type as u8);
                symtab_data.extend_from_slice(&[0u8; 2]); // Padding
                symtab_data.extend_from_slice(&symbol.section_index.to_le_bytes());
                symtab_data.extend_from_slice(&[0u8; 2]); // Padding
                symtab_data.extend_from_slice(&symbol.value.to_le_bytes());
                symtab_data.extend_from_slice(&symbol.size.to_le_bytes());
                symtab_data.push(symbol.layout_phase);
                symtab_data.push(if symbol.is_event_loop_anchor { 1 } else { 0 });
                symtab_data.push(if symbol.layout_pinned { 1 } else { 0 });
                symtab_data.extend_from_slice(&[0u8; 5]); // Padding to 32 bytes
            }

            let symtab_section = SmfSection {
                name: ".symtab".to_string(),
                section_type: SectionType::SymTab,
                flags: 0,
                data: symtab_data,
                alignment: 8,
            };
            self.sections.push(symtab_section);
        }

        // Build relocation sections if we have relocations
        if !self.relocations.is_empty() {
            let mut rela_data = Vec::new();
            for reloc in &self.relocations {
                rela_data.extend_from_slice(&reloc.offset.to_le_bytes());
                rela_data.extend_from_slice(&reloc.symbol_index.to_le_bytes());
                rela_data.push(reloc.reloc_type as u8);
                rela_data.extend_from_slice(&[0u8; 3]); // Padding
                rela_data.extend_from_slice(&reloc.addend.to_le_bytes());
            }

            let rela_section = SmfSection {
                name: ".rela".to_string(),
                section_type: SectionType::Reloc,
                flags: 0,
                data: rela_data,
                alignment: 8,
            };
            self.sections.push(rela_section);
        }

        // Build string table section
        let strtab_section = SmfSection {
            name: ".strtab".to_string(),
            section_type: SectionType::StrTab,
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
        let name_offsets: Vec<u32> = self
            .sections
            .iter()
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
        use crate::linker::object_parser::ParsedObject;
        use std::collections::HashMap;

        let mut writer = Self::new();

        // Parse object file to extract sections, symbols, and relocations
        let parsed = ParsedObject::parse(object_code)
            .map_err(|e| SmfWriteError::InvalidData(format!("Failed to parse object file: {}", e)))?;

        // Build mapping from MIR function names to layout info
        let mut mir_func_info: HashMap<String, _> = HashMap::new();
        for func in &mir.functions {
            mir_func_info.insert(
                func.name.clone(),
                (func.layout_phase.priority(), func.is_event_loop_anchor),
            );
        }

        // Track section index mapping (object section idx -> SMF section idx)
        let mut section_mapping: HashMap<usize, usize> = HashMap::new();

        // Add all sections from parsed object
        for (obj_idx, section) in parsed.sections.iter().enumerate() {
            let smf_idx = writer.sections.len();
            section_mapping.insert(obj_idx, smf_idx);
            writer.sections.push(section.clone());
        }

        // Add all symbols with layout information from MIR
        for mut symbol in parsed.symbols.into_iter() {
            // Update section index to SMF numbering
            if let Some(&smf_idx) = section_mapping.get(&(symbol.section_index as usize)) {
                symbol.section_index = smf_idx as u16;
            }

            // Merge layout info from MIR if available
            if let Some(&(layout_phase, is_anchor)) = mir_func_info.get(&symbol.name) {
                symbol.layout_phase = layout_phase;
                symbol.is_event_loop_anchor = is_anchor;
            }

            writer.symbols.push(symbol);
        }

        // Add all relocations
        for reloc in parsed.relocations {
            writer.relocations.push(reloc);
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
        assert_eq!(writer.sections[0].section_type, SectionType::Code);
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
            layout_phase: 2, // Steady
            is_event_loop_anchor: false,
            layout_pinned: false,
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
            layout_phase: 0, // Startup
            is_event_loop_anchor: false,
            layout_pinned: false,
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
