//! Settlement Types Tests
//!
//! Tests for Settlement SMF format types and structures

use simple_loader::smf::settlement::{
    SettlementHeader, NATIVE_LIB_SHARED, NATIVE_LIB_STATIC, NATIVE_LIB_SYSTEM, SSMF_FLAG_COMPRESSED,
    SSMF_FLAG_DEBUG, SSMF_FLAG_EXECUTABLE, SSMF_FLAG_HAS_NATIVES, SSMF_FLAG_RELOADABLE, SSMF_MAGIC, SSMF_VERSION,
};

// =============================================================================
// SettlementHeader Tests
// =============================================================================

#[test]
fn test_settlement_header_default() {
    let header = SettlementHeader::default();
    // Default should have zeroed fields
    assert_eq!(header.version, 0);
    assert_eq!(header.flags, 0);
}

#[test]
fn test_settlement_header_magic_constant() {
    // Verify SSMF magic number is correct
    assert_eq!(SSMF_MAGIC, *b"SSMF");
    assert_eq!(SSMF_MAGIC.len(), 4);
}

#[test]
fn test_settlement_header_version_constant() {
    // Verify version is set
    assert_eq!(SSMF_VERSION, 1);
}

#[test]
fn test_settlement_header_flag_values() {
    // Verify flag constants have correct values
    assert_eq!(SSMF_FLAG_EXECUTABLE, 0x0001);
    assert_eq!(SSMF_FLAG_RELOADABLE, 0x0002);
    assert_eq!(SSMF_FLAG_HAS_NATIVES, 0x0004);
    assert_eq!(SSMF_FLAG_COMPRESSED, 0x0008);
    assert_eq!(SSMF_FLAG_DEBUG, 0x0010);
}

#[test]
fn test_settlement_header_native_lib_types() {
    // Verify native library type constants
    assert_eq!(NATIVE_LIB_STATIC, 0x01);
    assert_eq!(NATIVE_LIB_SHARED, 0x02);
    assert_eq!(NATIVE_LIB_SYSTEM, 0x03);
}

#[test]
fn test_settlement_header_clone() {
    let mut header = SettlementHeader::default();
    header.version = SSMF_VERSION;
    header.flags = SSMF_FLAG_EXECUTABLE;

    let cloned = header.clone();
    assert_eq!(cloned.version, header.version);
    assert_eq!(cloned.flags, header.flags);
}

#[test]
fn test_settlement_header_copy() {
    let mut header = SettlementHeader::default();
    header.version = SSMF_VERSION;
    header.flags = SSMF_FLAG_RELOADABLE;

    let copied = header;
    assert_eq!(copied.version, header.version);
    assert_eq!(copied.flags, header.flags);
}

#[test]
fn test_settlement_header_section_offsets() {
    let mut header = SettlementHeader::default();
    header.code_offset = 1024;
    header.code_size = 4096;
    header.data_offset = 5120;
    header.data_size = 2048;

    assert_eq!(header.code_offset, 1024);
    assert_eq!(header.code_size, 4096);
    assert_eq!(header.data_offset, 5120);
    assert_eq!(header.data_size, 2048);
}

#[test]
fn test_settlement_header_table_offsets() {
    let mut header = SettlementHeader::default();

    // Function table
    header.func_table_offset = 100;
    header.func_table_size = 200;
    assert_eq!(header.func_table_offset, 100);
    assert_eq!(header.func_table_size, 200);

    // Global table
    header.global_table_offset = 300;
    header.global_table_size = 400;
    assert_eq!(header.global_table_offset, 300);
    assert_eq!(header.global_table_size, 400);

    // Type table
    header.type_table_offset = 500;
    header.type_table_size = 600;
    assert_eq!(header.type_table_offset, 500);
    assert_eq!(header.type_table_size, 600);
}

#[test]
fn test_settlement_header_module_and_native_tables() {
    let mut header = SettlementHeader::default();

    // Module table
    header.module_table_offset = 1000;
    header.module_table_size = 2000;
    assert_eq!(header.module_table_offset, 1000);
    assert_eq!(header.module_table_size, 2000);

    // Native libs table
    header.native_libs_offset = 3000;
    header.native_libs_size = 4000;
    assert_eq!(header.native_libs_offset, 3000);
    assert_eq!(header.native_libs_size, 4000);
}

#[test]
fn test_settlement_header_string_table() {
    let mut header = SettlementHeader::default();
    header.string_table_offset = 10000;
    header.string_table_size = 5000;

    assert_eq!(header.string_table_offset, 10000);
    assert_eq!(header.string_table_size, 5000);
}

#[test]
fn test_settlement_header_dependency_table() {
    let mut header = SettlementHeader::default();
    header.dep_table_offset = 20000;
    header.dep_table_size = 3000;

    assert_eq!(header.dep_table_offset, 20000);
    assert_eq!(header.dep_table_size, 3000);
}

#[test]
fn test_settlement_header_template_table() {
    let mut header = SettlementHeader::default();
    header.template_table_offset = 30000;
    header.template_table_size = 8000;

    assert_eq!(header.template_table_offset, 30000);
    assert_eq!(header.template_table_size, 8000);
}

#[test]
fn test_settlement_header_combined_flags() {
    let mut header = SettlementHeader::default();

    // Combine multiple flags
    header.flags = SSMF_FLAG_EXECUTABLE | SSMF_FLAG_RELOADABLE | SSMF_FLAG_DEBUG;

    // All three flags should be set
    assert_ne!(header.flags & SSMF_FLAG_EXECUTABLE, 0);
    assert_ne!(header.flags & SSMF_FLAG_RELOADABLE, 0);
    assert_ne!(header.flags & SSMF_FLAG_DEBUG, 0);

    // Other flags should not be set
    assert_eq!(header.flags & SSMF_FLAG_HAS_NATIVES, 0);
    assert_eq!(header.flags & SSMF_FLAG_COMPRESSED, 0);
}

#[test]
fn test_settlement_header_size_is_reasonable() {
    let size = std::mem::size_of::<SettlementHeader>();

    // Header should be reasonably sized (not too small, not too large)
    assert!(size >= 64, "Header too small: {} bytes", size);
    assert!(size <= 512, "Header too large: {} bytes", size);
}

#[test]
fn test_settlement_header_arch_field() {
    let mut header = SettlementHeader::default();
    header.arch = 0x01; // x86-64

    assert_eq!(header.arch, 0x01);
}

#[test]
fn test_settlement_header_reserved_fields() {
    let header = SettlementHeader::default();

    // Reserved fields should be zero by default
    assert_eq!(header.reserved, [0; 5]);
}
