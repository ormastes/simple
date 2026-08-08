//! Object file parsing for SMF generation
//!
//! Parses ELF, Mach-O, and COFF object files produced by Cranelift
//! and extracts sections, symbols, and relocations for SMF generation.

use object::{Object, ObjectSection, ObjectSymbol, RelocationTarget, SectionKind, SymbolKind};
use std::collections::HashMap;
use thiserror::Error;

use super::smf_writer::{
    DataSectionKind, RelocationType, SectionType, SmfRelocation, SmfSection, SmfSymbol, SymbolBinding, SymbolType,
    SECTION_FLAG_EXEC, SECTION_FLAG_READ, SECTION_FLAG_WRITE,
};

#[derive(Error, Debug)]
pub enum ObjectParseError {
    #[error("Failed to parse object file: {0}")]
    ParseError(#[from] object::Error),

    #[error("Unsupported relocation type: {0}")]
    UnsupportedRelocation(u32),

    #[error("Invalid section: {0}")]
    InvalidSection(String),

    #[error("Symbol not found: {0}")]
    SymbolNotFound(String),
}

pub type ParseResult<T> = Result<T, ObjectParseError>;

/// Parsed object file data
#[derive(Debug, Clone)]
pub struct ParsedObject {
    pub sections: Vec<SmfSection>,
    pub symbols: Vec<SmfSymbol>,
    pub relocations: Vec<SmfRelocation>,
    pub section_name_to_index: HashMap<String, usize>,
    pub symbol_name_to_index: HashMap<String, usize>,
}

impl ParsedObject {
    /// Create empty parsed object
    pub fn new() -> Self {
        Self {
            sections: Vec::new(),
            symbols: Vec::new(),
            relocations: Vec::new(),
            section_name_to_index: HashMap::new(),
            symbol_name_to_index: HashMap::new(),
        }
    }

    /// Parse an object file into SMF-compatible structures
    pub fn parse(data: &[u8]) -> ParseResult<Self> {
        let obj_file = object::File::parse(data)?;
        let mut parsed = Self::new();
        let mut object_section_to_parsed = HashMap::new();

        // Phase 1: Parse sections
        for section in obj_file.sections() {
            if section.kind() == SectionKind::Metadata {
                continue; // Skip debug/metadata sections
            }

            let name = section.name().unwrap_or("<unnamed>").to_string();
            let mut section_data = section.data().unwrap_or(&[]).to_vec();

            let (section_type, flags, data_kind) = match section.kind() {
                SectionKind::Text => (SectionType::Code, SECTION_FLAG_READ | SECTION_FLAG_EXEC, None),
                SectionKind::Data => (
                    SectionType::Data,
                    SECTION_FLAG_READ | SECTION_FLAG_WRITE,
                    Some(DataSectionKind::Mutable),
                ),
                SectionKind::ReadOnlyData | SectionKind::ReadOnlyDataWithRel | SectionKind::ReadOnlyString => {
                    (SectionType::RoData, SECTION_FLAG_READ, Some(DataSectionKind::ReadOnly))
                }
                SectionKind::UninitializedData => {
                    section_data.resize(section.size() as usize, 0);
                    (
                        SectionType::Bss,
                        SECTION_FLAG_READ | SECTION_FLAG_WRITE,
                        Some(DataSectionKind::Mutable),
                    )
                }
                _ => continue, // Skip other section types
            };

            let smf_section = SmfSection {
                name: name.clone(),
                section_type,
                flags,
                data: section_data,
                alignment: section.align() as u32,
            };

            let index = parsed.sections.len();
            parsed.section_name_to_index.insert(name, index);
            parsed.sections.push(smf_section);
            object_section_to_parsed.insert(section.index(), index);
        }

        // SMF loads all code sections into one contiguous code buffer. Object
        // symbols and relocation offsets are section-relative, so normalize
        // them to that flattened layout before serializing the SMF.
        let first_code_section = parsed
            .sections
            .iter()
            .position(|section| section.section_type == SectionType::Code)
            .map(|index| (index as u16) + 1);
        let mut code_offset = 0u64;
        let mut code_layout = HashMap::new();
        for (index, section) in parsed.sections.iter().enumerate() {
            if section.section_type == SectionType::Code {
                code_layout.insert(index, code_offset);
                code_offset += section.data.len() as u64;
            }
        }

        // Phase 2: Parse symbols
        let mut object_symbol_indices = HashMap::new();
        let mut object_section_symbols = Vec::new();
        for symbol in obj_file.symbols() {
            let object_symbol_index = symbol.index();
            if symbol.kind() == SymbolKind::Section {
                if let Some(section_index) = symbol.section_index() {
                    object_section_symbols.push((object_symbol_index, section_index));
                }
                continue;
            }
            let name = symbol.name().unwrap_or("<unnamed>").to_string();

            // Skip unnamed or invalid symbols
            if name.is_empty() || name == "<unnamed>" {
                continue;
            }

            let binding = if symbol.is_global() {
                SymbolBinding::Global
            } else if symbol.is_local() {
                SymbolBinding::Local
            } else if symbol.is_weak() {
                SymbolBinding::Weak
            } else {
                SymbolBinding::Local
            };

            let sym_type = match symbol.kind() {
                SymbolKind::Text => SymbolType::Function,
                SymbolKind::Data => SymbolType::Data,
                _ => SymbolType::None,
            };

            // Get section index
            let mut value = symbol.address();
            let section_index = if let Some(section_idx) = symbol.section_index() {
                // Find SMF section index from object section index
                let object_section = obj_file.section_by_index(section_idx)?;
                value = value.checked_sub(object_section.address()).ok_or_else(|| {
                    ObjectParseError::InvalidSection(format!("symbol {} address precedes its section base", name))
                })?;
                let parsed_section_index = object_section_to_parsed.get(&section_idx).copied();
                if let Some(offset) = parsed_section_index.and_then(|index| code_layout.get(&index)) {
                    value += offset;
                    first_code_section.unwrap_or(0)
                } else {
                    parsed_section_index.map(|index| (index as u16) + 1).unwrap_or(0)
                }
            } else {
                0 // Undefined symbol
            };

            let smf_symbol = SmfSymbol {
                name: name.clone(),
                binding,
                sym_type,
                section_index,
                value,
                size: symbol.size(),
                layout_phase: 2, // Default to steady phase
                is_event_loop_anchor: false,
                layout_pinned: false,
            };

            let index = parsed.symbols.len();
            parsed.symbol_name_to_index.insert(name, index);
            parsed.symbols.push(smf_symbol);
            object_symbol_indices.insert(object_symbol_index, index as u32);
        }

        // Some relocatable formats target a section plus an addend instead of
        // a named symbol. Preserve those targets as synthetic local symbols;
        // dropping them leaves Cranelift's placeholder call displacement in
        // place (typically a recursive call to the next instruction).
        let mut section_symbol_indices = HashMap::new();
        for section in obj_file.sections() {
            let Some(&parsed_index) = object_section_to_parsed.get(&section.index()) else {
                continue;
            };
            let (section_index, value) = if let Some(offset) = code_layout.get(&parsed_index) {
                (first_code_section.unwrap_or(0), *offset)
            } else {
                ((parsed_index as u16) + 1, 0)
            };
            let symbol_index = parsed.symbols.len() as u32;
            parsed.symbols.push(SmfSymbol {
                name: format!("__smf_section_{}", section.index().0),
                binding: SymbolBinding::Local,
                sym_type: SymbolType::None,
                section_index,
                value,
                size: section.size(),
                layout_phase: 2,
                is_event_loop_anchor: false,
                layout_pinned: false,
            });
            section_symbol_indices.insert(section.index(), symbol_index);
        }
        for (symbol_index, section_index) in object_section_symbols {
            if let Some(&synthetic_index) = section_symbol_indices.get(&section_index) {
                object_symbol_indices.insert(symbol_index, synthetic_index);
            }
        }

        // Phase 3: Parse relocations
        for section in obj_file.sections() {
            let section_idx = object_section_to_parsed.get(&section.index()).copied();

            if section_idx.is_none() {
                continue; // Skip sections we didn't parse
            }

            for (offset, reloc) in section.relocations() {
                if parsed.sections[section_idx.unwrap()].section_type != SectionType::Code {
                    return Err(ObjectParseError::InvalidSection(format!(
                        "relocation source section {} is not executable code",
                        section.name().unwrap_or("<unnamed>")
                    )));
                }
                let symbol_index = match reloc.target() {
                    RelocationTarget::Symbol(sym_idx) => *object_symbol_indices
                        .get(&sym_idx)
                        .ok_or_else(|| ObjectParseError::SymbolNotFound(format!("object symbol {}", sym_idx.0)))?,
                    RelocationTarget::Section(section_idx) => *section_symbol_indices
                        .get(&section_idx)
                        .ok_or_else(|| ObjectParseError::SymbolNotFound(format!("section {}", section_idx.0)))?,
                    _ => continue,
                };

                // Map object relocation to SMF relocation type
                let reloc_type = map_relocation_type(reloc.kind(), reloc.encoding(), reloc.flags())?;

                let smf_reloc = SmfRelocation {
                    offset: section_idx
                        .and_then(|index| code_layout.get(&index).copied())
                        .unwrap_or(0)
                        + offset,
                    symbol_index,
                    reloc_type,
                    addend: reloc.addend(),
                };

                parsed.relocations.push(smf_reloc);
            }
        }

        Ok(parsed)
    }

    /// Get section by name
    pub fn get_section(&self, name: &str) -> Option<&SmfSection> {
        self.section_name_to_index
            .get(name)
            .and_then(|&idx| self.sections.get(idx))
    }

    /// Get symbol by name
    pub fn get_symbol(&self, name: &str) -> Option<&SmfSymbol> {
        self.symbol_name_to_index
            .get(name)
            .and_then(|&idx| self.symbols.get(idx))
    }
}

impl Default for ParsedObject {
    fn default() -> Self {
        Self::new()
    }
}

/// Map object relocation type to SMF relocation type
fn map_relocation_type(
    kind: object::RelocationKind,
    encoding: object::RelocationEncoding,
    flags: object::RelocationFlags,
) -> ParseResult<RelocationType> {
    use object::RelocationEncoding::*;
    use object::RelocationFlags::*;
    use object::RelocationKind::*;

    // Map based on relocation kind and encoding
    match (kind, encoding) {
        (Absolute, Generic) => Ok(RelocationType::Abs64),
        (Relative, Generic) => Ok(RelocationType::Pc32),
        (Relative, AArch64Call) => Ok(RelocationType::Arm64Branch26),
        (PltRelative, _) => Ok(RelocationType::Plt32),
        (Got, _) | (GotRelative, _) => Ok(RelocationType::GotPcRel),
        _ => match flags {
            MachO { r_type, .. } => match r_type {
                object::macho::ARM64_RELOC_BRANCH26 => Ok(RelocationType::Arm64Branch26),
                object::macho::ARM64_RELOC_PAGE21 => Ok(RelocationType::Arm64Page21),
                object::macho::ARM64_RELOC_PAGEOFF12 => Ok(RelocationType::Arm64PageOff12),
                object::macho::ARM64_RELOC_GOT_LOAD_PAGE21 => Ok(RelocationType::Arm64GotLoadPage21),
                object::macho::ARM64_RELOC_GOT_LOAD_PAGEOFF12 => Ok(RelocationType::Arm64GotLoadPageOff12),
                _ => Ok(RelocationType::None),
            },
            _ => {
                // Default to none for unknown types
                Ok(RelocationType::None)
            }
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parsed_object_new() {
        let parsed = ParsedObject::new();
        assert_eq!(parsed.sections.len(), 0);
        assert_eq!(parsed.symbols.len(), 0);
        assert_eq!(parsed.relocations.len(), 0);
    }

    #[test]
    fn test_map_relocation_type() {
        use object::RelocationEncoding::Generic;
        use object::RelocationFlags;
        use object::RelocationKind::*;

        assert_eq!(
            map_relocation_type(
                Absolute,
                Generic,
                RelocationFlags::Generic {
                    kind: Absolute,
                    encoding: Generic,
                    size: 64
                }
            )
            .unwrap(),
            RelocationType::Abs64
        );
        assert_eq!(
            map_relocation_type(
                Relative,
                Generic,
                RelocationFlags::Generic {
                    kind: Relative,
                    encoding: Generic,
                    size: 32
                }
            )
            .unwrap(),
            RelocationType::Pc32
        );
        assert_eq!(
            map_relocation_type(
                object::RelocationKind::Unknown,
                object::RelocationEncoding::Generic,
                RelocationFlags::MachO {
                    r_type: object::macho::ARM64_RELOC_BRANCH26,
                    r_pcrel: true,
                    r_length: 2,
                }
            )
            .unwrap(),
            RelocationType::Arm64Branch26
        );
    }

    #[test]
    fn flattens_duplicate_code_sections_and_preserves_section_relocation_identity() {
        use object::write::{Object as WriteObject, Relocation};
        use object::{Architecture, BinaryFormat, Endianness, RelocationEncoding, RelocationFlags, RelocationKind};

        let mut object = WriteObject::new(BinaryFormat::Elf, Architecture::X86_64, Endianness::Little);
        let helper = object.add_section(Vec::new(), b".text".to_vec(), SectionKind::Text);
        object.append_section_data(helper, &[0xc3], 1);
        let main = object.add_section(Vec::new(), b".text".to_vec(), SectionKind::Text);
        object.append_section_data(main, &[0xe8, 0, 0, 0, 0, 0xc3], 1);
        let helper_section_symbol = object.section_symbol(helper);
        object
            .add_relocation(
                main,
                Relocation {
                    offset: 1,
                    symbol: helper_section_symbol,
                    addend: -4,
                    flags: RelocationFlags::Generic {
                        kind: RelocationKind::Relative,
                        encoding: RelocationEncoding::Generic,
                        size: 32,
                    },
                },
            )
            .unwrap();

        let parsed = ParsedObject::parse(&object.write().unwrap()).unwrap();
        let relocation = parsed.relocations.first().expect("relocation must survive parsing");
        let target = &parsed.symbols[relocation.symbol_index as usize];

        assert_eq!(
            relocation.offset, 2,
            "second section relocation must be flattened after the first byte"
        );
        assert_eq!(
            target.value, 0,
            "section relocation must still target the first code section"
        );
        assert!(target.name.starts_with("__smf_section_"));
    }

    #[test]
    fn normalizes_macho_symbol_address_before_flattening_code_sections() {
        use object::write::{Object as WriteObject, Symbol, SymbolSection};
        use object::{Architecture, BinaryFormat, Endianness, SymbolFlags, SymbolScope};

        let mut object = WriteObject::new(BinaryFormat::MachO, Architecture::Aarch64, Endianness::Little);
        let first = object.add_section(b"__TEXT".to_vec(), b"__text".to_vec(), SectionKind::Text);
        object.append_section_data(first, &[0xc0, 0x03, 0x5f, 0xd6], 4);
        let second = object.add_section(b"__TEXT".to_vec(), b"__text".to_vec(), SectionKind::Text);
        object.append_section_data(second, &[0xc0, 0x03, 0x5f, 0xd6], 16);
        object.add_symbol(Symbol {
            name: b"later".to_vec(),
            value: 0,
            size: 4,
            kind: SymbolKind::Text,
            scope: SymbolScope::Linkage,
            weak: false,
            section: SymbolSection::Section(second),
            flags: SymbolFlags::None,
        });

        let parsed = ParsedObject::parse(&object.write().unwrap()).unwrap();
        let later = parsed
            .get_symbol("_later")
            .expect("named Mach-O symbol must survive parsing");

        assert_eq!(
            later.value, 4,
            "later section symbol must use flattened code offset exactly once"
        );
    }
}
