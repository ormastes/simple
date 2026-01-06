//! Object file parsing for SMF generation
//!
//! Parses ELF, Mach-O, and COFF object files produced by Cranelift
//! and extracts sections, symbols, and relocations for SMF generation.

use object::{
    Object, ObjectSection, ObjectSymbol, RelocationTarget, SectionKind, SymbolKind,
};
use std::collections::HashMap;
use thiserror::Error;

use super::smf_writer::{
    DataSectionKind, RelocationType, SmfRelocation, SmfSection, SmfSymbol, SectionType,
    SymbolBinding, SymbolType, SECTION_FLAG_EXEC, SECTION_FLAG_READ, SECTION_FLAG_WRITE,
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

        // Phase 1: Parse sections
        for section in obj_file.sections() {
            if section.kind() == SectionKind::Metadata {
                continue; // Skip debug/metadata sections
            }

            let name = section.name().unwrap_or("<unnamed>").to_string();
            let section_data = section.data().unwrap_or(&[]).to_vec();

            let (section_type, flags, data_kind) = match section.kind() {
                SectionKind::Text => (
                    SectionType::Code,
                    SECTION_FLAG_READ | SECTION_FLAG_EXEC,
                    None,
                ),
                SectionKind::Data => (
                    SectionType::Data,
                    SECTION_FLAG_READ | SECTION_FLAG_WRITE,
                    Some(DataSectionKind::Mutable),
                ),
                SectionKind::ReadOnlyData => (
                    SectionType::RoData,
                    SECTION_FLAG_READ,
                    Some(DataSectionKind::ReadOnly),
                ),
                SectionKind::UninitializedData => {
                    // BSS - skip for now
                    continue;
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
        }

        // Phase 2: Parse symbols
        for (sym_idx, symbol) in obj_file.symbols().enumerate() {
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
            let section_index = if let Some(section_idx) = symbol.section_index() {
                // Find SMF section index from object section index
                let obj_section = obj_file.section_by_index(section_idx)?;
                let section_name = obj_section.name().unwrap_or("");
                parsed.section_name_to_index.get(section_name).copied().unwrap_or(0) as u16
            } else {
                0 // Undefined symbol
            };

            let smf_symbol = SmfSymbol {
                name: name.clone(),
                binding,
                sym_type,
                section_index,
                value: symbol.address(),
                size: symbol.size(),
                layout_phase: 2, // Default to steady phase
                is_event_loop_anchor: false,
                layout_pinned: false,
            };

            let index = parsed.symbols.len();
            parsed.symbol_name_to_index.insert(name, index);
            parsed.symbols.push(smf_symbol);
        }

        // Phase 3: Parse relocations
        for section in obj_file.sections() {
            let section_name = section.name().unwrap_or("");
            let section_idx = parsed.section_name_to_index.get(section_name).copied();

            if section_idx.is_none() {
                continue; // Skip sections we didn't parse
            }

            for (offset, reloc) in section.relocations() {
                let symbol_index = match reloc.target() {
                    RelocationTarget::Symbol(sym_idx) => {
                        // Find symbol in our parsed symbols
                        let obj_symbol = obj_file.symbol_by_index(sym_idx)?;
                        let sym_name = obj_symbol.name().unwrap_or("");
                        parsed.symbol_name_to_index.get(sym_name).copied().unwrap_or(0) as u32
                    }
                    _ => continue, // Skip non-symbol relocations
                };

                // Map object relocation to SMF relocation type
                let reloc_type = map_relocation_type(reloc.kind(), reloc.encoding())?;

                let smf_reloc = SmfRelocation {
                    offset,
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
) -> ParseResult<RelocationType> {
    use object::RelocationEncoding::*;
    use object::RelocationKind::*;

    // Map based on relocation kind and encoding
    match (kind, encoding) {
        (Absolute, Generic) => Ok(RelocationType::Abs64),
        (Relative, Generic) => Ok(RelocationType::Pc32),
        (PltRelative, _) => Ok(RelocationType::Plt32),
        (Got, _) | (GotRelative, _) => Ok(RelocationType::GotPcRel),
        _ => {
            // Default to none for unknown types
            Ok(RelocationType::None)
        }
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
        use object::RelocationKind::*;

        assert_eq!(
            map_relocation_type(Absolute, Generic).unwrap(),
            RelocationType::Abs64
        );
        assert_eq!(
            map_relocation_type(Relative, Generic).unwrap(),
            RelocationType::Pc32
        );
    }
}
