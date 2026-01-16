//! Low Coverage Type Tests
//! Tests for public types with 0% or low coverage from public_api.yml
#![allow(unused_imports)]

use std::io::Cursor;
use std::path::PathBuf;
use tempfile::tempdir;

// =============================================================================
// SmfWriter Coverage (compiler/src/linker/smf_writer.rs - 0%)
// =============================================================================

use simple_compiler::linker::{DataSectionKind, SmfRelocation, SmfSymbol as WriterSmfSymbol, SmfWriter};
use simple_loader::smf::{RelocationType, SectionType, SymbolBinding, SymbolType, SMF_MAGIC};

#[test]
fn test_smf_writer_new() {
    let writer = SmfWriter::new();
    let _ = writer;
}

#[test]
fn test_smf_writer_default() {
    let writer = SmfWriter::default();
    let _ = writer;
}

#[test]
fn test_smf_writer_add_string() {
    let mut writer = SmfWriter::new();
    let off1 = writer.add_string("hello");
    let off2 = writer.add_string("world");
    let off3 = writer.add_string("hello"); // duplicate

    assert_eq!(off1, 1); // after null byte
    assert!(off2 > off1);
    assert_eq!(off3, off1); // same offset for duplicate
}

#[test]
fn test_smf_writer_add_code_section() {
    let mut writer = SmfWriter::new();
    let code = vec![0xC3]; // ret instruction
    let idx = writer.add_code_section(".text", code);
    assert_eq!(idx, 0);
}

#[test]
fn test_smf_writer_add_data_section_mutable() {
    let mut writer = SmfWriter::new();
    let data = vec![1, 2, 3, 4];
    let idx = writer.add_data_section(".data", data, DataSectionKind::Mutable);
    assert_eq!(idx, 0);
}

#[test]
fn test_smf_writer_add_data_section_readonly() {
    let mut writer = SmfWriter::new();
    let data = vec![1, 2, 3, 4];
    let idx = writer.add_data_section(".rodata", data, DataSectionKind::ReadOnly);
    assert_eq!(idx, 0);
}

#[test]
fn test_smf_writer_add_rodata_section() {
    let mut writer = SmfWriter::new();
    let idx = writer.add_rodata_section(".rodata", vec![5, 6, 7]);
    assert_eq!(idx, 0);
}

#[test]
fn test_smf_writer_add_mutable_data_section() {
    let mut writer = SmfWriter::new();
    let idx = writer.add_mutable_data_section(".data", vec![8, 9, 10]);
    assert_eq!(idx, 0);
}

#[test]
fn test_smf_writer_add_symbol() {
    let mut writer = SmfWriter::new();

    let symbol = WriterSmfSymbol {
        name: "main".to_string(),
        binding: SymbolBinding::Global,
        sym_type: SymbolType::Function,
        section_index: 0,
        value: 0,
        size: 10,
        layout_phase: 0,
        is_event_loop_anchor: false,
        layout_pinned: false,
    };

    let idx = writer.add_symbol(symbol);
    assert_eq!(idx, 0);
}

#[test]
fn test_smf_writer_add_relocation() {
    let mut writer = SmfWriter::new();

    let reloc = SmfRelocation {
        offset: 0x10,
        symbol_index: 0,
        reloc_type: RelocationType::Abs64,
        addend: 0,
    };

    writer.add_relocation(reloc);
}

#[test]
fn test_smf_writer_write() {
    let mut writer = SmfWriter::new();

    writer.add_code_section(".text", vec![0x90, 0xC3]); // nop, ret
    writer.add_symbol(WriterSmfSymbol {
        name: "entry".to_string(),
        binding: SymbolBinding::Global,
        sym_type: SymbolType::Function,
        section_index: 0,
        value: 0,
        size: 2,
        layout_phase: 0,
        is_event_loop_anchor: false,
        layout_pinned: false,
    });

    let mut output = Vec::new();
    writer.write(&mut output).unwrap();

    // Check magic
    assert_eq!(&output[0..4], SMF_MAGIC);
    assert!(!output.is_empty());
}

// Test DataSectionKind methods
#[test]
fn test_data_section_kind_is_readonly() {
    assert!(!DataSectionKind::Mutable.is_readonly());
    assert!(DataSectionKind::ReadOnly.is_readonly());
}

#[test]
fn test_data_section_kind_to_section_type() {
    assert_eq!(DataSectionKind::Mutable.to_section_type(), SectionType::Data);
    assert_eq!(DataSectionKind::ReadOnly.to_section_type(), SectionType::RoData);
}

#[test]
fn test_data_section_kind_to_flags() {
    let mutable_flags = DataSectionKind::Mutable.to_flags();
    let readonly_flags = DataSectionKind::ReadOnly.to_flags();

    // Mutable should have write flag
    assert!(mutable_flags > readonly_flags);
}

#[test]
fn test_data_section_kind_default() {
    let default = DataSectionKind::default();
    assert_eq!(default, DataSectionKind::Mutable);
}

// =============================================================================
// SymbolTable Coverage (loader/src/smf/symbol.rs - low coverage)
// =============================================================================

use simple_loader::smf::{hash_name, SmfSymbol as LoaderSmfSymbol, SymbolTable};

#[test]
fn test_symbol_table_new() {
    let symbols = vec![LoaderSmfSymbol {
        name_offset: 1,
        name_hash: hash_name("main"),
        sym_type: SymbolType::Function,
        binding: SymbolBinding::Global,
        visibility: 0,
        flags: 0,
        value: 0,
        size: 10,
        type_id: 0,
        version: 0,
    }];

    let string_table = b"\0main\0".to_vec();
    let table = SymbolTable::new(symbols, string_table);
    let _ = table;
}

#[test]
fn test_symbol_table_lookup() {
    let symbols = vec![LoaderSmfSymbol {
        name_offset: 1,
        name_hash: hash_name("entry"),
        sym_type: SymbolType::Function,
        binding: SymbolBinding::Global,
        visibility: 0,
        flags: 0,
        value: 0x1000,
        size: 20,
        type_id: 0,
        version: 0,
    }];

    let string_table = b"\0entry\0".to_vec();
    let table = SymbolTable::new(symbols, string_table);

    // Should find "entry"
    let sym = table.lookup("entry");
    assert!(sym.is_some());
    assert_eq!(sym.unwrap().value, 0x1000);

    // Should not find "missing"
    let missing = table.lookup("missing");
    assert!(missing.is_none());
}

#[test]
fn test_symbol_table_symbol_name() {
    let symbols = vec![LoaderSmfSymbol {
        name_offset: 1,
        name_hash: hash_name("test_func"),
        sym_type: SymbolType::Function,
        binding: SymbolBinding::Local,
        visibility: 0,
        flags: 0,
        value: 0,
        size: 0,
        type_id: 0,
        version: 0,
    }];

    let string_table = b"\0test_func\0".to_vec();
    let table = SymbolTable::new(symbols, string_table);

    let name = table.symbol_name(&table.symbols[0]);
    assert_eq!(name, "test_func");
}

#[test]
fn test_symbol_table_exports() {
    let symbols = vec![
        LoaderSmfSymbol {
            name_offset: 1,
            name_hash: hash_name("local_fn"),
            sym_type: SymbolType::Function,
            binding: SymbolBinding::Local,
            visibility: 0,
            flags: 0,
            value: 0,
            size: 0,
            type_id: 0,
            version: 0,
        },
        LoaderSmfSymbol {
            name_offset: 10,
            name_hash: hash_name("pub_fn"),
            sym_type: SymbolType::Function,
            binding: SymbolBinding::Global,
            visibility: 0,
            flags: 0,
            value: 0x100,
            size: 10,
            type_id: 0,
            version: 0,
        },
    ];

    let string_table = b"\0local_fn\0pub_fn\0".to_vec();
    let table = SymbolTable::new(symbols, string_table);

    let exports: Vec<_> = table.exports().collect();
    assert_eq!(exports.len(), 1);
    assert_eq!(exports[0].binding, SymbolBinding::Global);
}

#[test]
fn test_hash_name() {
    let h1 = hash_name("hello");
    let h2 = hash_name("hello");
    let h3 = hash_name("world");

    assert_eq!(h1, h2); // Same string -> same hash
    assert_ne!(h1, h3); // Different strings -> different hash
}

// =============================================================================
// SmfHeader Coverage (loader/src/smf/header.rs - 25% coverage)
// =============================================================================

use simple_common::target::{TargetArch, TargetOS};
use simple_loader::smf::{SmfHeader, SMF_FLAG_DEBUG_INFO, SMF_FLAG_EXECUTABLE, SMF_FLAG_RELOADABLE};

#[test]
fn test_smf_header_new_for_target() {
    let header = SmfHeader::new_for_target(TargetArch::X86_64, TargetOS::Linux);

    assert_eq!(header.magic, *SMF_MAGIC);
    assert_eq!(header.version_major, 1);
}

#[test]
fn test_smf_header_is_executable() {
    let mut header = SmfHeader::new_for_target(TargetArch::X86_64, TargetOS::Linux);

    assert!(!header.is_executable());
    header.flags |= SMF_FLAG_EXECUTABLE;
    assert!(header.is_executable());
}

#[test]
fn test_smf_header_is_reloadable() {
    let mut header = SmfHeader::new_for_target(TargetArch::X86_64, TargetOS::Linux);

    assert!(!header.is_reloadable());
    header.flags |= SMF_FLAG_RELOADABLE;
    assert!(header.is_reloadable());
}

#[test]
fn test_smf_header_has_debug_info() {
    let mut header = SmfHeader::new_for_target(TargetArch::X86_64, TargetOS::Linux);

    assert!(!header.has_debug_info());
    header.flags |= SMF_FLAG_DEBUG_INFO;
    assert!(header.has_debug_info());
}

#[test]
fn test_smf_header_target_arch() {
    let header = SmfHeader::new_for_target(TargetArch::X86_64, TargetOS::Linux);
    let arch = header.target_arch();
    assert!(arch.is_some());
}

#[test]
fn test_smf_header_target_os() {
    let header = SmfHeader::new_for_target(TargetArch::X86_64, TargetOS::Linux);
    let os = header.target_os();
    assert!(os.is_some());
}

#[test]
fn test_smf_header_is_compatible_arch() {
    let header = SmfHeader::new_for_target(TargetArch::X86_64, TargetOS::Linux);
    assert!(header.is_compatible_arch(TargetArch::X86_64));
}

#[test]
fn test_smf_header_read() {
    // Create valid SMF header bytes
    let mut header_bytes = vec![0u8; SmfHeader::SIZE];
    header_bytes[0..4].copy_from_slice(SMF_MAGIC);
    header_bytes[4] = 1; // version major
    header_bytes[5] = 0; // version minor

    let mut cursor = Cursor::new(header_bytes);
    let result = SmfHeader::read(&mut cursor);

    assert!(result.is_ok());
    let header = result.unwrap();
    assert_eq!(header.magic, *SMF_MAGIC);
}

#[test]
fn test_smf_header_read_invalid_magic() {
    let mut header_bytes = vec![0u8; SmfHeader::SIZE];
    header_bytes[0..4].copy_from_slice(b"BAD\0");

    let mut cursor = Cursor::new(header_bytes);
    let result = SmfHeader::read(&mut cursor);

    assert!(result.is_err());
}

// =============================================================================
// SmfSection Coverage (loader/src/smf/section.rs)
// Note: This is the loader's SmfSection, not compiler's
// =============================================================================

use simple_loader::smf::{SmfSection, SECTION_FLAG_EXEC, SECTION_FLAG_WRITE};

#[test]
fn test_loader_smf_section_name_str() {
    let mut name = [0u8; 16];
    name[0..5].copy_from_slice(b".text");

    let section = SmfSection {
        section_type: SectionType::Code,
        flags: 0,
        offset: 0,
        size: 0,
        virtual_size: 0,
        alignment: 16,
        name,
    };

    assert_eq!(section.name_str(), ".text");
}

#[test]
fn test_loader_smf_section_is_executable() {
    let mut section = SmfSection {
        section_type: SectionType::Code,
        flags: 0,
        offset: 0,
        size: 0,
        virtual_size: 0,
        alignment: 16,
        name: [0u8; 16],
    };

    assert!(!section.is_executable());
    section.flags = SECTION_FLAG_EXEC;
    assert!(section.is_executable());
}

#[test]
fn test_loader_smf_section_is_writable() {
    let mut section = SmfSection {
        section_type: SectionType::Data,
        flags: 0,
        offset: 0,
        size: 0,
        virtual_size: 0,
        alignment: 8,
        name: [0u8; 16],
    };

    assert!(!section.is_writable());
    section.flags = SECTION_FLAG_WRITE;
    assert!(section.is_writable());
}

// =============================================================================
// ModuleResolver Coverage (compiler/src/module_resolver.rs - 0%)
// =============================================================================

use simple_compiler::{DirectoryManifest, ModuleResolver, ProjectContext};

#[test]
fn test_module_resolver_new() {
    let dir = tempdir().expect("tempdir");
    let resolver = ModuleResolver::new(dir.path().to_path_buf(), dir.path().to_path_buf());
    let _ = resolver;
}

#[test]
fn test_directory_manifest_default() {
    let manifest = DirectoryManifest::default();
    assert!(manifest.name.is_empty());
    assert!(manifest.child_modules.is_empty());
}

// =============================================================================
// ProjectContext Coverage (compiler/src/project.rs - 0%)
// =============================================================================

#[test]
fn test_project_context_new_empty_dir() {
    let dir = tempdir().expect("tempdir");
    let result = ProjectContext::new(dir.path().to_path_buf());

    // Should succeed with defaults (no simple.toml)
    assert!(result.is_ok());
    let ctx = result.unwrap();
    assert!(!ctx.name.is_empty());
}

#[test]
fn test_project_context_with_manifest() {
    let dir = tempdir().expect("tempdir");

    // Create a simple.toml
    let manifest = r#"
[project]
name = "test_project"
root = "src"
"#;
    std::fs::write(dir.path().join("simple.toml"), manifest).expect("write manifest");
    std::fs::create_dir(dir.path().join("src")).expect("create src");

    let result = ProjectContext::new(dir.path().to_path_buf());
    assert!(result.is_ok());

    let ctx = result.unwrap();
    assert_eq!(ctx.name, "test_project");
}

#[test]
fn test_project_context_with_src_dir() {
    let dir = tempdir().expect("tempdir");
    std::fs::create_dir(dir.path().join("src")).expect("create src");

    let result = ProjectContext::new(dir.path().to_path_buf());
    assert!(result.is_ok());

    let ctx = result.unwrap();
    assert!(ctx.source_root.ends_with("src"));
}

#[test]
fn test_project_context_features() {
    let dir = tempdir().expect("tempdir");
    let result = ProjectContext::new(dir.path().to_path_buf());
    let ctx = result.unwrap();

    // Default should have no features
    assert!(ctx.features.is_empty());
}

#[test]
fn test_project_context_lint_config() {
    let dir = tempdir().expect("tempdir");
    let result = ProjectContext::new(dir.path().to_path_buf());
    let ctx = result.unwrap();

    // Should have default lint config
    let _ = ctx.lint_config;
}

// =============================================================================
// Package Commands Coverage (pkg/src/commands/*.rs - 0%)
// =============================================================================

// Note: Package commands require more complex setup with filesystem
// These tests cover the types that can be tested in isolation

use simple_pkg::{Cache as PackageCache, Linker as PackageLinker};

#[test]
fn test_package_cache_at() {
    let dir = tempdir().expect("tempdir");
    let cache = PackageCache::at(dir.path().to_path_buf());
    assert_eq!(cache.root(), dir.path());
}

#[test]
fn test_package_cache_new() {
    // Cache::new() uses system cache directory, may or may not exist
    let result = PackageCache::new();
    // Just test that it returns a result (either Ok or Err)
    let _ = result;
}

#[test]
fn test_package_cache_default() {
    let cache = PackageCache::default();
    let _ = cache.root();
}

#[test]
fn test_package_cache_methods() {
    let dir = tempdir().expect("tempdir");
    let cache = PackageCache::at(dir.path().to_path_buf());

    // Test various path methods
    let _ = cache.git_dir();
    let _ = cache.registry_dir();
    let _ = cache.packages_dir();
    let _ = cache.git_repo_path("https://example.com/repo");
    let _ = cache.package_path("test", "1.0.0");
    assert!(!cache.has_git_repo("https://example.com/fake"));
    assert!(!cache.has_package("fake", "1.0.0"));
}

#[test]
fn test_package_linker_new() {
    let dir = tempdir().expect("tempdir");
    let linker = PackageLinker::new(dir.path());
    let _ = linker;
}

// =============================================================================
// Target/Cross-test Coverage (loader/src/cross_test.rs - 0%)
// =============================================================================

use simple_common::target::Target;
use simple_loader::{CrossTestResults, TargetFixture, TestMatrix};

#[test]
fn test_target_fixture_new() {
    let fixture = TargetFixture::new(Target::host());
    assert!(fixture.is_host());
}

#[test]
fn test_target_fixture_x86_64_linux() {
    let fixture = TargetFixture::x86_64_linux();
    let _ = fixture;
}

#[test]
fn test_target_fixture_aarch64_linux() {
    let fixture = TargetFixture::aarch64_linux();
    let _ = fixture;
}

#[test]
fn test_target_fixture_mock_smf_header() {
    let fixture = TargetFixture::new(Target::host());
    let header = fixture.mock_smf_header();
    assert_eq!(header.magic, *SMF_MAGIC);
}

#[test]
fn test_target_fixture_can_execute() {
    let fixture = TargetFixture::new(Target::host());
    // Host fixture should be able to execute
    assert!(fixture.can_execute());
}

#[test]
fn test_test_matrix_new() {
    let matrix = TestMatrix::new();
    assert!(!matrix.targets().is_empty());
}

#[test]
fn test_test_matrix_minimal() {
    let matrix = TestMatrix::minimal();
    assert!(!matrix.targets().is_empty());
}

#[test]
fn test_test_matrix_comprehensive() {
    let matrix = TestMatrix::comprehensive();
    assert!(!matrix.targets().is_empty());
}

#[test]
fn test_test_matrix_with_target() {
    let matrix = TestMatrix::new().with_target(Target::host());
    assert!(!matrix.targets().is_empty());
}

#[test]
fn test_test_matrix_fixtures() {
    let matrix = TestMatrix::minimal();
    let fixtures = matrix.fixtures();
    assert!(!fixtures.is_empty());
}

#[test]
fn test_cross_test_results_new() {
    let results = CrossTestResults::new();
    assert!(results.all_passed());
    assert_eq!(results.passed_count(), 0);
}

#[test]
fn test_cross_test_results_record_pass() {
    let mut results = CrossTestResults::new();
    results.record_pass(Target::host());

    assert!(results.all_passed());
    assert_eq!(results.passed_count(), 1);
}

#[test]
fn test_cross_test_results_record_fail() {
    let mut results = CrossTestResults::new();
    results.record_fail(Target::host(), "test failure");

    assert!(!results.all_passed());
    assert_eq!(results.failed_count(), 1);
}

#[test]
fn test_cross_test_results_record_skip() {
    let mut results = CrossTestResults::new();
    results.record_skip(Target::host(), "not available");

    assert!(results.all_passed()); // Skips don't count as failures
    assert_eq!(results.skipped_count(), 1);
}

#[test]
fn test_cross_test_results_summary() {
    let mut results = CrossTestResults::new();
    results.record_pass(Target::host());

    let summary = results.summary();
    assert!(summary.contains("passed"));
}

// =============================================================================
// ArchValidator Coverage (loader/src/arch_validate.rs - 0%)
// =============================================================================

use simple_loader::{ArchValidator, ValidationResult};

#[test]
fn test_validation_result_ok() {
    let result = ValidationResult::ok();
    assert!(result.is_ok());
    assert!(!result.is_err());
}

#[test]
fn test_validation_result_summary() {
    let result = ValidationResult::ok();
    let summary = result.summary();
    assert!(!summary.is_empty());
}

#[test]
fn test_arch_validator_new() {
    let validator = ArchValidator::new();
    let _ = validator;
}

#[test]
fn test_arch_validator_for_target() {
    let validator = ArchValidator::for_target(Target::host());
    let _ = validator;
}

#[test]
fn test_arch_validator_allow_any_platform() {
    let validator = ArchValidator::new().allow_any_platform(true);
    let _ = validator;
}

#[test]
fn test_arch_validator_allow_cross_arch() {
    let validator = ArchValidator::new().allow_cross_arch(true);
    let _ = validator;
}

#[test]
fn test_arch_validator_validate_smf() {
    let validator = ArchValidator::for_target(Target::host());
    let header = SmfHeader::new_for_target(TargetArch::X86_64, TargetOS::Linux);
    let result = validator.validate_smf(&header);
    // Result depends on host architecture
    let _ = result;
}

// =============================================================================
// Compilability Coverage (compiler/src/compilability.rs - 0%)
// =============================================================================

use simple_compiler::compilability::{CompilabilityStatus, FallbackReason};

#[test]
fn test_fallback_reason_debug() {
    let reason = FallbackReason::DynamicTypes;
    let display = format!("{:?}", reason);
    assert!(!display.is_empty());
}

#[test]
fn test_compilability_compilable() {
    let comp = CompilabilityStatus::Compilable;
    assert!(comp.is_compilable());
    assert!(comp.reasons().is_empty());
}

#[test]
fn test_compilability_requires_interpreter() {
    let comp = CompilabilityStatus::RequiresInterpreter(vec![FallbackReason::CollectionOps]);
    assert!(!comp.is_compilable());
    assert_eq!(comp.reasons().len(), 1);
}

#[test]
fn test_fallback_reason_variants() {
    // Test various FallbackReason variants exist and can be created
    let _ = FallbackReason::DynamicTypes;
    let _ = FallbackReason::CollectionOps;
    let _ = FallbackReason::CollectionLiteral;
    let _ = FallbackReason::StringOps;
    let _ = FallbackReason::GcInNogcContext;
    let _ = FallbackReason::BlockingInAsync;
    let _ = FallbackReason::ActorOps;
    let _ = FallbackReason::UserMacros;
    let _ = FallbackReason::PatternMatch;
    let _ = FallbackReason::Closure;
    let _ = FallbackReason::ObjectConstruction;
    let _ = FallbackReason::MethodCall;
    let _ = FallbackReason::FieldAccess;
    let _ = FallbackReason::Generator;
    let _ = FallbackReason::AsyncAwait;
}

#[test]
fn test_fallback_reason_with_string() {
    let reason = FallbackReason::UnknownExtern("test_fn".to_string());
    let debug = format!("{:?}", reason);
    assert!(debug.contains("test_fn"));

    let reason2 = FallbackReason::NotYetImplemented("feature".to_string());
    let debug2 = format!("{:?}", reason2);
    assert!(debug2.contains("feature"));
}
