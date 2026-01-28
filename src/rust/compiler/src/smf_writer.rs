//! Extended SMF writer with template section support.
//!
//! This module extends the basic SMF builder to include:
//! - TemplateCode sections (serialized generic definitions)
//! - TemplateMeta sections (monomorphization metadata)
//!
//! Enables .smf files to store both native code AND templates for deferred instantiation.

use std::sync::Arc;

use simple_common::gc::GcAllocator;
use simple_common::target::Target;
use simple_loader::smf::{
    hash_name, Arch, SectionType, SmfHeader, SmfSection, SmfSymbol, SymbolBinding, SymbolType,
    SECTION_FLAG_EXEC, SECTION_FLAG_READ, SMF_FLAG_EXECUTABLE, SMF_MAGIC,
};

use crate::elf_utils::extract_code_from_object;
use crate::monomorphize::{GenericTemplates, MonomorphizationMetadata, NoteSdnMetadata};

/// Generate SMF from object code with optional template sections.
///
/// If templates and metadata are provided, adds TemplateCode and TemplateMeta sections
/// to enable deferred monomorphization.
pub fn generate_smf_with_templates(
    object_code: &[u8],
    templates: Option<&GenericTemplates>,
    metadata: Option<&MonomorphizationMetadata>,
    gc: Option<&Arc<dyn GcAllocator>>,
    target: Target,
) -> Vec<u8> {
    generate_smf_with_all_sections(object_code, templates, metadata, None, gc, target)
}

/// Generate SMF from object code with all optional sections.
///
/// Includes templates, metadata, and note.sdn for full instantiation tracking.
pub fn generate_smf_with_all_sections(
    object_code: &[u8],
    templates: Option<&GenericTemplates>,
    metadata: Option<&MonomorphizationMetadata>,
    note_sdn: Option<&NoteSdnMetadata>,
    gc: Option<&Arc<dyn GcAllocator>>,
    target: Target,
) -> Vec<u8> {
    let code_bytes = extract_code_from_object(object_code);

    // If no templates, use simple builder
    if templates.is_none() && metadata.is_none() && note_sdn.is_none() {
        return build_smf_with_code_for_target(&code_bytes, gc, target);
    }

    // Build SMF with template sections
    build_smf_with_all_sections(&code_bytes, templates, metadata, note_sdn, gc, target)
}

/// Build an SMF module with code and optional template sections.
fn build_smf_with_templates(
    code_bytes: &[u8],
    templates: Option<&GenericTemplates>,
    metadata: Option<&MonomorphizationMetadata>,
    gc: Option<&Arc<dyn GcAllocator>>,
    target: Target,
) -> Vec<u8> {
    build_smf_with_all_sections(code_bytes, templates, metadata, None, gc, target)
}

/// Build an SMF module with code and all optional sections.
fn build_smf_with_all_sections(
    code_bytes: &[u8],
    templates: Option<&GenericTemplates>,
    metadata: Option<&MonomorphizationMetadata>,
    note_sdn: Option<&NoteSdnMetadata>,
    gc: Option<&Arc<dyn GcAllocator>>,
    target: Target,
) -> Vec<u8> {
    // Serialize templates if present
    let template_bytes = templates.map(|t| serialize_templates(t)).unwrap_or_default();
    let metadata_bytes = metadata.map(|m| serialize_metadata(m)).unwrap_or_default();
    let note_sdn_bytes = note_sdn.map(|n| serialize_note_sdn(n)).unwrap_or_default();

    let has_templates = !template_bytes.is_empty();
    let has_metadata = !metadata_bytes.is_empty();
    let has_note_sdn = !note_sdn_bytes.is_empty();

    // Calculate section count
    let mut section_count = 1; // Code section
    if has_templates {
        section_count += 1;
    }
    if has_metadata {
        section_count += 1;
    }
    if has_note_sdn {
        section_count += 1; // note.sdn section
    }

    // Calculate offsets
    let section_table_offset = SmfHeader::SIZE as u64;
    let section_table_size = (std::mem::size_of::<SmfSection>() * section_count) as u64;
    let code_offset = section_table_offset + section_table_size;
    let template_offset = code_offset + code_bytes.len() as u64;
    let metadata_offset = template_offset + template_bytes.len() as u64;
    let note_sdn_offset = metadata_offset + metadata_bytes.len() as u64;
    let symbol_table_offset = note_sdn_offset + note_sdn_bytes.len() as u64;

    if let Some(gc) = gc {
        let _ = gc.alloc_bytes(code_bytes);
    }

    // Build header
    let header = SmfHeader {
        magic: *SMF_MAGIC,
        version_major: 0,
        version_minor: 1,
        platform: simple_loader::smf::Platform::from_target_os(target.os) as u8,
        arch: Arch::from_target_arch(target.arch) as u8,
        flags: SMF_FLAG_EXECUTABLE,
        compression: 0,  // No compression
        compression_level: 0,
        reserved_compression: [0; 2],
        section_count: section_count as u32,
        section_table_offset,
        symbol_table_offset,
        symbol_count: 1,
        exported_count: 1,
        entry_point: 0,
        stub_size: 0,    // Pure SMF (no stub)
        smf_data_offset: 0,
        module_hash: 0,
        source_hash: 0,
        app_type: 0,
        window_width: 0,
        window_height: 0,
        prefetch_hint: 0,
        prefetch_file_count: 0,
        reserved: [0; 5],  // Updated to 5 bytes
    };

    // Build sections
    let mut sections = Vec::new();

    // Code section
    let mut sec_name = [0u8; 16];
    sec_name[..4].copy_from_slice(b"code");
    sections.push(SmfSection {
        section_type: SectionType::Code,
        flags: SECTION_FLAG_READ | SECTION_FLAG_EXEC,
        offset: code_offset,
        size: code_bytes.len() as u64,
        virtual_size: code_bytes.len() as u64,
        alignment: 16,
        name: sec_name,
    });

    // Template code section
    if has_templates {
        let mut sec_name = [0u8; 16];
        sec_name[..12].copy_from_slice(b"template_code");
        sections.push(SmfSection {
            section_type: SectionType::TemplateCode,
            flags: SECTION_FLAG_READ,
            offset: template_offset,
            size: template_bytes.len() as u64,
            virtual_size: template_bytes.len() as u64,
            alignment: 8,
            name: sec_name,
        });
    }

    // Template metadata section
    if has_metadata {
        let mut sec_name = [0u8; 16];
        sec_name[..13].copy_from_slice(b"template_meta");
        sections.push(SmfSection {
            section_type: SectionType::TemplateMeta,
            flags: SECTION_FLAG_READ,
            offset: metadata_offset,
            size: metadata_bytes.len() as u64,
            virtual_size: metadata_bytes.len() as u64,
            alignment: 8,
            name: sec_name,
        });
    }

    // note.sdn section (zero-size trick: size=0 in section table)
    if has_note_sdn {
        let mut sec_name = [0u8; 16];
        sec_name[..8].copy_from_slice(b"note.sdn");
        sections.push(SmfSection {
            section_type: SectionType::TemplateMeta, // Reuse TemplateMeta type
            flags: SECTION_FLAG_READ,
            offset: note_sdn_offset,
            size: 0, // ⭐ Zero-size trick: actual size determined by scanning for terminator
            virtual_size: 0,
            alignment: 1,
            name: sec_name,
        });
    }

    // Build symbol table
    let string_table = b"main\0".to_vec();
    let symbol = SmfSymbol {
        name_offset: 0,
        name_hash: hash_name("main"),
        sym_type: SymbolType::Function,
        binding: SymbolBinding::Global,
        visibility: 0,
        flags: 0,
        value: 0,
        size: code_bytes.len() as u64,
        type_id: 0,
        version: 0,
        template_param_count: 0,
        reserved: [0; 3],
        template_offset: 0,
    };

    // Assemble SMF
    let mut buf = Vec::new();

    // Write header
    push_struct(&mut buf, &header);

    // Write section table
    for section in &sections {
        push_struct(&mut buf, section);
    }

    // Write code
    buf.extend_from_slice(code_bytes);

    // Write templates
    if has_templates {
        buf.extend_from_slice(&template_bytes);
    }

    // Write metadata
    if has_metadata {
        buf.extend_from_slice(&metadata_bytes);
    }

    // Write note.sdn
    if has_note_sdn {
        buf.extend_from_slice(&note_sdn_bytes);
    }

    // Write symbol table
    push_struct(&mut buf, &symbol);

    // Write string table
    buf.extend_from_slice(&string_table);

    buf
}

/// Serialize generic templates to bytes.
///
/// Binary format:
/// - Header: magic (u32), version (u16), template_count (u32)
/// - For each template: kind (u8), serialized AST node
fn serialize_templates(templates: &GenericTemplates) -> Vec<u8> {
    let mut buf = Vec::new();

    // Header
    buf.extend_from_slice(b"GTPL"); // Generic TeMPLates magic
    buf.extend_from_slice(&1u16.to_le_bytes()); // version

    let total_count = templates.functions.len()
        + templates.structs.len()
        + templates.classes.len()
        + templates.enums.len()
        + templates.traits.len();
    buf.extend_from_slice(&(total_count as u32).to_le_bytes());

    // TODO: Implement actual AST serialization
    // For now, just write placeholders
    // In Phase 3 (serialization), we'll implement proper serialization

    // Functions
    for func in &templates.functions {
        buf.push(0); // kind = Function
        serialize_function_placeholder(&mut buf, func);
    }

    // Structs
    for struct_def in &templates.structs {
        buf.push(1); // kind = Struct
        serialize_struct_placeholder(&mut buf, struct_def);
    }

    // Classes
    for class_def in &templates.classes {
        buf.push(2); // kind = Class
        serialize_class_placeholder(&mut buf, class_def);
    }

    // Enums
    for enum_def in &templates.enums {
        buf.push(3); // kind = Enum
        serialize_enum_placeholder(&mut buf, enum_def);
    }

    // Traits
    for trait_def in &templates.traits {
        buf.push(4); // kind = Trait
        serialize_trait_placeholder(&mut buf, trait_def);
    }

    buf
}

/// Serialize monomorphization metadata to bytes.
fn serialize_metadata(metadata: &MonomorphizationMetadata) -> Vec<u8> {
    let mut buf = Vec::new();

    // Header
    buf.extend_from_slice(b"META"); // METAdata magic
    buf.extend_from_slice(&1u16.to_le_bytes()); // version

    // Count of each category
    buf.extend_from_slice(&(metadata.functions.len() as u32).to_le_bytes());
    buf.extend_from_slice(&(metadata.structs.len() as u32).to_le_bytes());
    buf.extend_from_slice(&(metadata.enums.len() as u32).to_le_bytes());
    buf.extend_from_slice(&(metadata.traits.len() as u32).to_le_bytes());

    // TODO: Implement full metadata serialization
    // For now, just write counts

    buf
}

// Placeholder serialization functions (will be replaced in Phase 3)
fn serialize_function_placeholder(buf: &mut Vec<u8>, func: &simple_parser::ast::FunctionDef) {
    // Write name length and name
    let name_bytes = func.name.as_bytes();
    buf.extend_from_slice(&(name_bytes.len() as u32).to_le_bytes());
    buf.extend_from_slice(name_bytes);

    // Write generic param count
    buf.extend_from_slice(&(func.generic_params.len() as u8).to_le_bytes());
}

fn serialize_struct_placeholder(buf: &mut Vec<u8>, struct_def: &simple_parser::ast::StructDef) {
    let name_bytes = struct_def.name.as_bytes();
    buf.extend_from_slice(&(name_bytes.len() as u32).to_le_bytes());
    buf.extend_from_slice(name_bytes);
    buf.extend_from_slice(&(struct_def.generic_params.len() as u8).to_le_bytes());
}

fn serialize_class_placeholder(buf: &mut Vec<u8>, class_def: &simple_parser::ast::ClassDef) {
    let name_bytes = class_def.name.as_bytes();
    buf.extend_from_slice(&(name_bytes.len() as u32).to_le_bytes());
    buf.extend_from_slice(name_bytes);
    buf.extend_from_slice(&(class_def.generic_params.len() as u8).to_le_bytes());
}

fn serialize_enum_placeholder(buf: &mut Vec<u8>, enum_def: &simple_parser::ast::EnumDef) {
    let name_bytes = enum_def.name.as_bytes();
    buf.extend_from_slice(&(name_bytes.len() as u32).to_le_bytes());
    buf.extend_from_slice(name_bytes);
    buf.extend_from_slice(&(enum_def.generic_params.len() as u8).to_le_bytes());
}

fn serialize_trait_placeholder(buf: &mut Vec<u8>, trait_def: &simple_parser::ast::TraitDef) {
    let name_bytes = trait_def.name.as_bytes();
    buf.extend_from_slice(&(name_bytes.len() as u32).to_le_bytes());
    buf.extend_from_slice(name_bytes);
    buf.extend_from_slice(&(trait_def.generic_params.len() as u8).to_le_bytes());
}

/// Build an SMF module with the given code bytes for a specific target architecture.
fn build_smf_with_code_for_target(code_bytes: &[u8], gc: Option<&Arc<dyn GcAllocator>>, target: Target) -> Vec<u8> {
    // Delegate to the original smf_builder
    crate::smf_builder::generate_smf_from_object_for_target(
        &code_bytes_to_object(code_bytes),
        gc,
        target,
    )
}

/// Helper to convert code bytes to a minimal object format for compatibility.
fn code_bytes_to_object(code: &[u8]) -> Vec<u8> {
    // For now, just return the code as-is
    // In reality, we'd need to wrap it in an object file format
    code.to_vec()
}

/// Serialize note.sdn metadata to SDN format with terminator.
///
/// The terminator `\n# END_NOTE\n` allows dynamic size calculation at load time.
fn serialize_note_sdn(note_sdn: &NoteSdnMetadata) -> Vec<u8> {
    let sdn_content = note_sdn.to_sdn();
    sdn_content.into_bytes()
}

/// Helper to write a struct to a byte buffer.
fn push_struct<T: Copy>(buf: &mut Vec<u8>, value: &T) {
    let bytes = unsafe { std::slice::from_raw_parts(value as *const T as *const u8, std::mem::size_of::<T>()) };
    buf.extend_from_slice(bytes);
}
