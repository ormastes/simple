use std::collections::HashMap;
use std::io::{self, Write};
use thiserror::Error;

use crate::mir::MirModule;

// Re-export SMF types from common (single source of truth)
pub use simple_common::smf::{
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
        use simple_common::smf::{
            hash_name, symbol_flags, Arch, Platform, SmfHeader as LoaderHeader, SmfRelocation as LoaderRelocation,
            SmfSection as LoaderSection, SmfSymbol as LoaderSymbol,
        };

        let symbol_names: Vec<String> = self.symbols.iter().map(|symbol| symbol.name.clone()).collect();
        let name_offsets: Vec<u32> = symbol_names.iter().map(|name| self.add_string(name)).collect();

        let mut loader_sections: Vec<LoaderSection> =
            Vec::with_capacity(self.sections.len() + usize::from(!self.relocations.is_empty()));
        let mut section_payloads: Vec<Vec<u8>> = self.sections.iter().map(|section| section.data.clone()).collect();

        for section in &self.sections {
            let mut name = [0u8; 16];
            let bytes = section.name.as_bytes();
            let copy_len = bytes.len().min(name.len());
            name[..copy_len].copy_from_slice(&bytes[..copy_len]);
            loader_sections.push(LoaderSection {
                section_type: section.section_type,
                flags: section.flags,
                offset: 0,
                size: section.data.len() as u64,
                virtual_size: section.data.len() as u64,
                alignment: section.alignment as u64,
                name,
            });
        }

        if !self.relocations.is_empty() {
            let mut rela_data = Vec::with_capacity(self.relocations.len() * std::mem::size_of::<LoaderRelocation>());
            for reloc in &self.relocations {
                let loader_reloc = LoaderRelocation {
                    offset: reloc.offset,
                    symbol_index: reloc.symbol_index,
                    reloc_type: reloc.reloc_type,
                    addend: reloc.addend,
                };
                let bytes = unsafe {
                    std::slice::from_raw_parts(
                        &loader_reloc as *const LoaderRelocation as *const u8,
                        std::mem::size_of::<LoaderRelocation>(),
                    )
                };
                rela_data.extend_from_slice(bytes);
            }
            let mut name = [0u8; 16];
            name[..5].copy_from_slice(b".rela");
            loader_sections.push(LoaderSection {
                section_type: SectionType::Reloc,
                flags: 0,
                offset: 0,
                size: rela_data.len() as u64,
                virtual_size: rela_data.len() as u64,
                alignment: 8,
                name,
            });
            section_payloads.push(rela_data);
        }

        let section_table_offset = LoaderHeader::SIZE as u64;
        let section_table_size = (loader_sections.len() * std::mem::size_of::<LoaderSection>()) as u64;
        let mut current_offset = section_table_offset + section_table_size;

        for (section, payload) in loader_sections.iter_mut().zip(section_payloads.iter()) {
            let align = section.alignment.max(1);
            current_offset = (current_offset + align - 1) & !(align - 1);
            section.offset = current_offset;
            section.size = payload.len() as u64;
            section.virtual_size = payload.len() as u64;
            current_offset += payload.len() as u64;
        }

        let symbol_table_offset = current_offset;
        let string_table_offset =
            symbol_table_offset + (self.symbols.len() as u64 * std::mem::size_of::<LoaderSymbol>() as u64);

        let entry_point = self
            .symbols
            .iter()
            .find(|symbol| symbol.name == "spl_main")
            .or_else(|| self.symbols.iter().find(|symbol| symbol.name == "main"))
            .map(|symbol| symbol.value)
            .unwrap_or(0);
        let exported_count = self
            .symbols
            .iter()
            .filter(|symbol| symbol.binding != SymbolBinding::Local)
            .count() as u32;

        let target = simple_common::target::Target::host();
        let header = LoaderHeader {
            magic: *SMF_MAGIC,
            version_major: SMF_VERSION_MAJOR,
            version_minor: SMF_VERSION_MINOR,
            platform: Platform::from_target_os(target.os) as u8,
            arch: Arch::from_target_arch(target.arch) as u8,
            flags: SMF_FLAG_EXECUTABLE,
            compression: 0,
            compression_level: 0,
            reserved_compression: [0; 2],
            section_count: loader_sections.len() as u32,
            section_table_offset,
            symbol_table_offset,
            symbol_count: self.symbols.len() as u32,
            exported_count,
            entry_point,
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

        let header_bytes = unsafe {
            std::slice::from_raw_parts(
                &header as *const LoaderHeader as *const u8,
                std::mem::size_of::<LoaderHeader>(),
            )
        };
        writer.write_all(header_bytes)?;

        for section in &loader_sections {
            let section_bytes = unsafe {
                std::slice::from_raw_parts(
                    section as *const LoaderSection as *const u8,
                    std::mem::size_of::<LoaderSection>(),
                )
            };
            writer.write_all(section_bytes)?;
        }

        let mut written_offset = section_table_offset + section_table_size;
        for (section, payload) in loader_sections.iter().zip(section_payloads.iter()) {
            while written_offset < section.offset {
                writer.write_all(&[0])?;
                written_offset += 1;
            }
            writer.write_all(payload)?;
            written_offset += payload.len() as u64;
        }

        while written_offset < symbol_table_offset {
            writer.write_all(&[0])?;
            written_offset += 1;
        }

        for (symbol, name_offset) in self.symbols.iter().zip(name_offsets.iter()) {
            let mut flags = symbol.layout_phase & symbol_flags::LAYOUT_PHASE_MASK;
            if symbol.is_event_loop_anchor {
                flags |= symbol_flags::EVENT_LOOP_ANCHOR;
            }
            if symbol.layout_pinned {
                flags |= symbol_flags::LAYOUT_PINNED;
            }
            let loader_symbol = LoaderSymbol {
                name_offset: *name_offset,
                name_hash: hash_name(&symbol.name),
                sym_type: symbol.sym_type,
                binding: symbol.binding,
                visibility: 0,
                flags,
                value: symbol.value,
                size: symbol.size,
                type_id: 0,
                version: 0,
                template_param_count: 0,
                reserved: [0; 3],
                template_offset: 0,
            };
            let symbol_bytes = unsafe {
                std::slice::from_raw_parts(
                    &loader_symbol as *const LoaderSymbol as *const u8,
                    std::mem::size_of::<LoaderSymbol>(),
                )
            };
            writer.write_all(symbol_bytes)?;
        }

        writer.write_all(&self.string_table)?;
        debug_assert_eq!(
            string_table_offset + self.string_table.len() as u64,
            symbol_table_offset
                + (self.symbols.len() as u64 * std::mem::size_of::<LoaderSymbol>() as u64)
                + self.string_table.len() as u64
        );
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
