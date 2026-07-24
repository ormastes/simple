use std::collections::HashMap;
use std::io::{self, Write};
use thiserror::Error;

use crate::hir::{HirType, TypeId, TypeRegistry};
use crate::mir::MirModule;
use simple_common::smf::{SmfFieldType, SmfNamedType, SmfTypeInfo, SmfTypeKind, SmfTypeRef, SMF_TYPE_INFO_VERSION};

// Re-export SMF types from common (single source of truth)
pub use simple_common::smf::{
    RelocationType, SectionType, SymbolBinding, SymbolType, SECTION_FLAG_EXEC, SECTION_FLAG_READ, SECTION_FLAG_WRITE,
    SMF_FLAG_EXECUTABLE, SMF_MAGIC,
};

/// SMF version constants
pub const SMF_VERSION_MAJOR: u8 = 1;
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

/// Converts registry types to the portable, name-based SMF metadata format.
pub fn smf_type_info_from_registry(registry: &TypeRegistry) -> Result<SmfTypeInfo, String> {
    let mut types = Vec::new();
    for (id, ty) in registry.iter() {
        let (name, kind, fields): (&str, SmfTypeKind, &[(String, TypeId)]) = match ty {
            HirType::Struct { name, fields, .. } => (
                name,
                if registry.is_value_struct(id) {
                    SmfTypeKind::Struct
                } else {
                    SmfTypeKind::Class
                },
                fields,
            ),
            HirType::Enum { name, .. } => (name, SmfTypeKind::Enum, &[]),
            HirType::Mixin { name, fields, .. } => (name, SmfTypeKind::Opaque, fields),
            HirType::Bitfield { name, .. } | HirType::ExternClass { name } => {
                (name, SmfTypeKind::Opaque, &[])
            }
            _ => continue,
        };
        if name.is_empty() {
            return Err("SMF type info cannot encode an unnamed type".to_string());
        }
        if registry.lookup(name) != Some(id) {
            continue;
        }
        types.push(SmfNamedType {
            name: name.to_string(),
            is_public: registry.is_public_type(id),
            kind,
            fields: fields
                .iter()
                .map(|(name, ty)| {
                    Ok(SmfFieldType {
                        name: name.clone(),
                        type_ref: smf_type_ref_from_id(registry, *ty)?,
                    })
                })
                .collect::<Result<_, String>>()?,
        });
    }
    types.sort_by(|left, right| left.name.cmp(&right.name));
    Ok(SmfTypeInfo {
        version: SMF_TYPE_INFO_VERSION,
        types,
    })
}

/// Resolves a HIR type through the registry; SMF never stores compiler-local IDs.
pub fn smf_type_ref_from_id(registry: &TypeRegistry, id: TypeId) -> Result<SmfTypeRef, String> {
    let ty = registry
        .get(id)
        .ok_or_else(|| format!("SMF type info cannot resolve type id {}", id.0))?;
    let primitive = |name: &str| Ok(SmfTypeRef::Primitive(name.to_string()));
    match ty {
        HirType::Void => primitive("void"),
        HirType::Bool => primitive("bool"),
        HirType::Any => primitive("any"),
        HirType::Char => primitive("char"),
        HirType::Int { bits, signedness } => {
            primitive(&format!("{}{}", if signedness.is_signed() { "i" } else { "u" }, bits))
        }
        HirType::Float { bits } => primitive(&format!("f{bits}")),
        HirType::String => primitive("text"),
        HirType::Nil => primitive("nil"),
        HirType::Pointer {
            kind,
            capability,
            inner,
        } => Ok(SmfTypeRef::Pointer {
            inner: Box::new(smf_type_ref_from_id(registry, *inner)?),
            kind: match kind {
                crate::hir::PointerKind::Unique => "Unique",
                crate::hir::PointerKind::Shared => "Shared",
                crate::hir::PointerKind::Weak => "Weak",
                crate::hir::PointerKind::Handle => "Handle",
                crate::hir::PointerKind::Borrow => "Borrow",
                crate::hir::PointerKind::BorrowMut => "BorrowMut",
                crate::hir::PointerKind::RawConst => "RawConst",
                crate::hir::PointerKind::RawMut => "RawMut",
            }
            .to_string(),
            capability: Some(
                match capability {
                    simple_parser::ast::ReferenceCapability::Shared => "Shared",
                    simple_parser::ast::ReferenceCapability::Exclusive => "Exclusive",
                    simple_parser::ast::ReferenceCapability::Isolated => "Isolated",
                }
                .to_string(),
            ),
        }),
        HirType::Array { element, size } => Ok(SmfTypeRef::Array {
            element: Box::new(smf_type_ref_from_id(registry, *element)?),
            size: *size,
        }),
        HirType::Simd { lanes, element } => Ok(SmfTypeRef::Simd {
            lanes: *lanes,
            element: Box::new(smf_type_ref_from_id(registry, *element)?),
        }),
        HirType::Tuple(items) => Ok(SmfTypeRef::Tuple(
            items
                .iter()
                .map(|id| smf_type_ref_from_id(registry, *id))
                .collect::<Result<_, _>>()?,
        )),
        HirType::LabeledTuple(items) => Ok(SmfTypeRef::LabeledTuple(
            items
                .iter()
                .map(|(name, id)| Ok((name.clone(), smf_type_ref_from_id(registry, *id)?)))
                .collect::<Result<_, String>>()?,
        )),
        HirType::Dict { key, value } => Ok(SmfTypeRef::Dict {
            key: Box::new(smf_type_ref_from_id(registry, *key)?),
            value: Box::new(smf_type_ref_from_id(registry, *value)?),
        }),
        HirType::Function { params, ret } => Ok(SmfTypeRef::Function {
            params: params
                .iter()
                .map(|id| smf_type_ref_from_id(registry, *id))
                .collect::<Result<_, _>>()?,
            ret: Box::new(smf_type_ref_from_id(registry, *ret)?),
        }),
        HirType::Struct { name, .. }
        | HirType::Enum { name, .. }
        | HirType::Mixin { name, .. }
        | HirType::Bitfield { name, .. }
        | HirType::ExternClass { name }
            if !name.is_empty() =>
        {
            Ok(SmfTypeRef::Named(name.clone()))
        }
        HirType::Union { variants } => Ok(SmfTypeRef::Union(
            variants
                .iter()
                .map(|id| smf_type_ref_from_id(registry, *id))
                .collect::<Result<_, _>>()?,
        )),
        HirType::Promise { inner } => Ok(SmfTypeRef::Promise(Box::new(smf_type_ref_from_id(registry, *inner)?))),
        HirType::UnitType {
            name,
            repr,
            bits,
            signedness,
            is_float,
            ..
        } if !name.is_empty() => {
            let repr = match smf_type_ref_from_id(registry, *repr)? {
                SmfTypeRef::Primitive(name) | SmfTypeRef::Named(name) => name,
                _ => return Err(format!("SMF unit {name} has a non-name representation")),
            };
            Ok(SmfTypeRef::Unit {
                name: name.clone(),
                repr,
                bits: u16::from(*bits),
                signed: signedness.is_signed(),
                is_float: *is_float,
            })
        }
        HirType::Unknown
        | HirType::Struct { .. }
        | HirType::Enum { .. }
        | HirType::Mixin { .. }
        | HirType::Bitfield { .. }
        | HirType::ExternClass { .. }
        | HirType::UnitType { .. } => Err("SMF type info encountered an unresolved or unnamed type".to_string()),
    }
}

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

    /// Add an arbitrary SMF section while preserving its bytes and alignment.
    pub fn add_custom_section(
        &mut self,
        name: &str,
        section_type: SectionType,
        flags: u32,
        data: Vec<u8>,
        alignment: u32,
    ) -> usize {
        let section = SmfSection {
            name: name.to_string(),
            section_type,
            flags,
            data,
            alignment,
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
            .find(|symbol| matches!(symbol.name.as_str(), "spl_main" | "_spl_main"))
            .or_else(|| {
                self.symbols
                    .iter()
                    .find(|symbol| matches!(symbol.name.as_str(), "main" | "_main"))
            })
            .map(|symbol| symbol.value)
            .unwrap_or(0);
        let exported_count = self
            .symbols
            .iter()
            .filter(|symbol| symbol.binding != SymbolBinding::Local)
            .count() as u32;

        let target = simple_common::target::Target::host();
        // Zero-initialize so repr(C) padding bytes (e.g. bytes 20-23 between section_count
        // and section_table_offset) are deterministically 0x00 on disk.
        let mut header: LoaderHeader = unsafe { std::mem::zeroed() };
        header.magic = *SMF_MAGIC;
        header.version_major = SMF_VERSION_MAJOR;
        header.version_minor = SMF_VERSION_MINOR;
        header.platform = Platform::from_target_os(target.os) as u8;
        header.arch = Arch::from_target_arch(target.arch) as u8;
        header.flags = SMF_FLAG_EXECUTABLE;
        header.section_count = loader_sections.len() as u32;
        header.section_table_offset = section_table_offset;
        header.symbol_table_offset = symbol_table_offset;
        header.symbol_count = self.symbols.len() as u32;
        header.exported_count = exported_count;
        header.entry_point = entry_point;

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
                visibility: if symbol.section_index != 0 { 1 } else { 0 },
                flags,
                value: symbol.value,
                size: symbol.size,
                type_id: 0,
                version: 0,
                template_param_count: 0,
                reserved: [
                    (symbol.section_index & 0xff) as u8,
                    ((symbol.section_index >> 8) & 0xff) as u8,
                    0,
                ],
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
            let parsed_section_idx = symbol.section_index.saturating_sub(1) as usize;
            if symbol.section_index != 0 {
                if let Some(&smf_idx) = section_mapping.get(&parsed_section_idx) {
                    symbol.section_index = (smf_idx as u16) + 1;
                }
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

        let type_info = smf_type_info_from_registry(&mir.type_registry).map_err(SmfWriteError::InvalidData)?;
        if !type_info.types.is_empty() {
            writer.add_custom_section(
                ".type_info",
                SectionType::TypeInfo,
                SECTION_FLAG_READ,
                type_info.to_bytes().map_err(SmfWriteError::InvalidData)?,
                8,
            );
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
    fn type_info_is_named_sorted_and_uses_registry_semantics() {
        let mut registry = TypeRegistry::new();
        let beta = registry.register_named("Beta".to_string(), HirType::Struct {
            name: "Beta".to_string(),
            fields: vec![],
            has_snapshot: false,
            generic_params: vec![],
            is_generic_template: false,
            type_bindings: HashMap::new(),
        });
        let alpha = registry.register_named("Alpha".to_string(), HirType::Struct {
            name: "Alpha".to_string(),
            fields: vec![("child".to_string(), beta), ("count".to_string(), TypeId::U32)],
            has_snapshot: false,
            generic_params: vec![],
            is_generic_template: false,
            type_bindings: HashMap::new(),
        });
        registry.set_value_struct(alpha, true);
        registry.set_public_type(alpha, true);

        let info = smf_type_info_from_registry(&registry).unwrap();
        assert_eq!(
            info.types.iter().map(|ty| ty.name.as_str()).collect::<Vec<_>>(),
            ["Alpha", "Beta"]
        );
        assert_eq!(info.types[0].kind, SmfTypeKind::Struct);
        assert!(info.types[0].is_public);
        assert_eq!(info.types[0].fields[0].type_ref, SmfTypeRef::Named("Beta".to_string()));
        assert_eq!(
            info.types[0].fields[1].type_ref,
            SmfTypeRef::Primitive("u32".to_string())
        );
        assert_eq!(info.types[1].kind, SmfTypeKind::Class);

        let pointer = registry.register(HirType::Pointer {
            kind: crate::hir::PointerKind::BorrowMut,
            capability: simple_parser::ast::ReferenceCapability::Exclusive,
            inner: TypeId::U32,
        });
        assert_eq!(
            smf_type_ref_from_id(&registry, pointer).unwrap(),
            SmfTypeRef::Pointer {
                inner: Box::new(SmfTypeRef::Primitive("u32".to_string())),
                kind: "BorrowMut".to_string(),
                capability: Some("Exclusive".to_string()),
            }
        );
    }

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
