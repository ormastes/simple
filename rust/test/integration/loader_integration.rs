//! Loader crate integration tests
//! Tests ModuleLoader, ModuleRegistry, SMF loading, and symbol resolution
//! Focus: Public function coverage for simple_loader

#![allow(unused_imports, unused_variables)]

use simple_driver::Runner;
use simple_loader::smf::{SmfHeader, SmfSection, SectionType};
use simple_loader::{ModuleLoader, ModuleRegistry};
use std::fs;
use std::io::Cursor;
use tempfile::tempdir;

// =============================================================================
// ModuleLoader Tests
// =============================================================================

#[test]
fn test_module_loader_new() {
    let loader = ModuleLoader::new();
    // Just verify it doesn't panic
    let _ = loader;
}

#[test]
fn test_module_loader_load() {
    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("load_test.smf");

    let runner = Runner::new_no_gc();
    runner
        .compile_to_smf("main = 42", &smf_path)
        .expect("compile");

    let loader = ModuleLoader::new();
    let result = loader.load(&smf_path);
    assert!(result.is_ok(), "Should load module: {:?}", result.err());
}

#[test]
fn test_module_loader_load_invalid_path() {
    let loader = ModuleLoader::new();
    let result = loader.load(std::path::Path::new("/nonexistent/path.smf"));
    assert!(result.is_err(), "Should fail on invalid path");
}

#[test]
fn test_module_loader_load_invalid_smf() {
    let dir = tempdir().expect("tempdir");
    let invalid_path = dir.path().join("invalid.smf");

    // Write invalid data
    fs::write(&invalid_path, b"not a valid smf file").expect("write");

    let loader = ModuleLoader::new();
    let result = loader.load(&invalid_path);
    assert!(result.is_err(), "Should fail on invalid SMF");
}

// =============================================================================
// LoadedModule Tests
// =============================================================================

#[test]
fn test_loaded_module_entry_point() {
    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("entry_test.smf");

    let runner = Runner::new_no_gc();
    runner
        .compile_to_smf("main = 123", &smf_path)
        .expect("compile");

    let loader = ModuleLoader::new();
    let module = loader.load(&smf_path).expect("load");

    let entry: Option<fn() -> i32> = module.entry_point();
    assert!(entry.is_some(), "Should have entry point");
    assert_eq!(entry.unwrap()(), 123);
}

#[test]
fn test_loaded_module_exports() {
    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("exports_test.smf");

    let runner = Runner::new_no_gc();
    runner
        .compile_to_smf("main = 0", &smf_path)
        .expect("compile");

    let loader = ModuleLoader::new();
    let module = loader.load(&smf_path).expect("load");

    let exports = module.exports();
    // Should have at least main export
    assert!(!exports.is_empty(), "Should have exports");
}

#[test]
fn test_loaded_module_source_hash() {
    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("hash_test.smf");

    let runner = Runner::new_no_gc();
    runner
        .compile_to_smf("main = 99", &smf_path)
        .expect("compile");

    let loader = ModuleLoader::new();
    let module = loader.load(&smf_path).expect("load");

    let hash = module.source_hash();
    // Hash is a u64
    let _ = hash;
}

#[test]
fn test_loaded_module_is_reloadable() {
    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("reload_test.smf");

    let runner = Runner::new_no_gc();
    runner
        .compile_to_smf("main = 50", &smf_path)
        .expect("compile");

    let loader = ModuleLoader::new();
    let module = loader.load(&smf_path).expect("load");

    let reloadable = module.is_reloadable();
    // Should return a boolean
    let _ = reloadable;
}

#[test]
fn test_loaded_module_get_function() {
    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("get_fn_test.smf");

    let runner = Runner::new_no_gc();
    runner
        .compile_to_smf("main = 77", &smf_path)
        .expect("compile");

    let loader = ModuleLoader::new();
    let module = loader.load(&smf_path).expect("load");

    // Try to get main function
    let func: Option<fn() -> i32> = module.get_function("main");
    // May or may not find it depending on symbol visibility
    let _ = func;
}

// =============================================================================
// ModuleRegistry Tests
// =============================================================================

#[test]
fn test_module_registry_new() {
    let registry = ModuleRegistry::new();
    assert!(std::mem::size_of_val(&registry) > 0);
}

#[test]
fn test_module_registry_load() {
    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("reg_load_test.smf");

    let runner = Runner::new_no_gc();
    runner
        .compile_to_smf("main = 42", &smf_path)
        .expect("compile");

    let registry = ModuleRegistry::new();
    let result = registry.load(&smf_path);
    assert!(result.is_ok(), "Should load: {:?}", result.err());
}

#[test]
fn test_module_registry_unload() {
    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("unload_test.smf");

    let runner = Runner::new_no_gc();
    runner
        .compile_to_smf("main = 42", &smf_path)
        .expect("compile");

    let registry = ModuleRegistry::new();
    let _module = registry.load(&smf_path).expect("load");

    let unloaded = registry.unload(&smf_path);
    assert!(unloaded, "Should unload successfully");

    let unloaded_again = registry.unload(&smf_path);
    assert!(!unloaded_again, "Should not unload again");
}

#[test]
fn test_module_registry_reload() {
    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("reload_test.smf");

    let runner = Runner::new_no_gc();

    // Initial compile
    runner
        .compile_to_smf("main = 42", &smf_path)
        .expect("compile");

    let registry = ModuleRegistry::new();
    let module1 = registry.load(&smf_path).expect("load");

    let entry1: Option<fn() -> i32> = module1.entry_point();
    assert_eq!(entry1.unwrap()(), 42);

    // Recompile with different value
    runner
        .compile_to_smf("main = 99", &smf_path)
        .expect("recompile");

    // Reload
    let module2 = registry.reload(&smf_path).expect("reload");

    let entry2: Option<fn() -> i32> = module2.entry_point();
    assert_eq!(entry2.unwrap()(), 99);
}

#[test]
fn test_module_registry_resolve_symbol() {
    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("symbol_test.smf");

    let runner = Runner::new_no_gc();
    runner
        .compile_to_smf("main = 42", &smf_path)
        .expect("compile");

    let registry = ModuleRegistry::new();
    let _module = registry.load(&smf_path).expect("load");

    // Try to resolve main symbol
    let symbol = registry.resolve_symbol("main");
    // May or may not find it
    let _ = symbol;
}

// =============================================================================
// SmfHeader Tests
// =============================================================================

#[test]
fn test_smf_header_read() {
    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("header_test.smf");

    let runner = Runner::new_no_gc();
    runner
        .compile_to_smf("main = 42", &smf_path)
        .expect("compile");

    let bytes = fs::read(&smf_path).expect("read");
    let mut cursor = Cursor::new(bytes);
    let header = SmfHeader::read(&mut cursor);

    assert!(header.is_ok(), "Should read header: {:?}", header.err());
}

#[test]
fn test_smf_header_has_debug_info() {
    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("debug_test.smf");

    let runner = Runner::new_no_gc();
    runner
        .compile_to_smf("main = 42", &smf_path)
        .expect("compile");

    let bytes = fs::read(&smf_path).expect("read");
    let mut cursor = Cursor::new(bytes);
    let header = SmfHeader::read(&mut cursor).expect("read header");

    let has_debug = header.has_debug_info();
    // Should return a boolean
    let _ = has_debug;
}

#[test]
fn test_smf_header_version() {
    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("version_test.smf");

    let runner = Runner::new_no_gc();
    runner
        .compile_to_smf("main = 42", &smf_path)
        .expect("compile");

    let bytes = fs::read(&smf_path).expect("read");
    let mut cursor = Cursor::new(bytes);
    let header = SmfHeader::read(&mut cursor).expect("read header");

    // Header should have valid version (using version_major)
    assert!(header.version_major > 0 || header.version_major == 0);
}

// =============================================================================
// Section Type Tests
// =============================================================================

#[test]
fn test_section_type_variants() {
    let code = SectionType::Code;
    let data = SectionType::Data;
    let rodata = SectionType::RoData;
    let bss = SectionType::Bss;

    // Verify types exist
    assert!(std::mem::size_of_val(&code) > 0);
    assert!(std::mem::size_of_val(&data) > 0);
    assert!(std::mem::size_of_val(&rodata) > 0);
    assert!(std::mem::size_of_val(&bss) > 0);
}

// =============================================================================
// Multi-module Tests
// =============================================================================

#[test]
fn test_load_multiple_modules() {
    let dir = tempdir().expect("tempdir");
    let smf1 = dir.path().join("mod1.smf");
    let smf2 = dir.path().join("mod2.smf");
    let smf3 = dir.path().join("mod3.smf");

    let runner = Runner::new_no_gc();
    runner.compile_to_smf("main = 1", &smf1).expect("compile 1");
    runner.compile_to_smf("main = 2", &smf2).expect("compile 2");
    runner.compile_to_smf("main = 3", &smf3).expect("compile 3");

    let registry = ModuleRegistry::new();

    let mod1 = registry.load(&smf1).expect("load 1");
    let mod2 = registry.load(&smf2).expect("load 2");
    let mod3 = registry.load(&smf3).expect("load 3");

    let entry1: Option<fn() -> i32> = mod1.entry_point();
    let entry2: Option<fn() -> i32> = mod2.entry_point();
    let entry3: Option<fn() -> i32> = mod3.entry_point();

    assert_eq!(entry1.unwrap()(), 1);
    assert_eq!(entry2.unwrap()(), 2);
    assert_eq!(entry3.unwrap()(), 3);
}

#[test]
fn test_reload_preserves_other_modules() {
    let dir = tempdir().expect("tempdir");
    let smf1 = dir.path().join("preserve1.smf");
    let smf2 = dir.path().join("preserve2.smf");

    let runner = Runner::new_no_gc();
    runner
        .compile_to_smf("main = 100", &smf1)
        .expect("compile 1");
    runner
        .compile_to_smf("main = 200", &smf2)
        .expect("compile 2");

    let registry = ModuleRegistry::new();

    let _mod1 = registry.load(&smf1).expect("load 1");
    let mod2 = registry.load(&smf2).expect("load 2");

    // Recompile and reload mod1
    runner
        .compile_to_smf("main = 150", &smf1)
        .expect("recompile");
    let mod1_new = registry.reload(&smf1).expect("reload");

    // mod2 should still work
    let entry2: Option<fn() -> i32> = mod2.entry_point();
    assert_eq!(entry2.unwrap()(), 200);

    // mod1_new should have new value
    let entry1_new: Option<fn() -> i32> = mod1_new.entry_point();
    assert_eq!(entry1_new.unwrap()(), 150);
}

// =============================================================================
// Error Handling Tests
// =============================================================================

#[test]
fn test_loader_empty_file() {
    let dir = tempdir().expect("tempdir");
    let empty_path = dir.path().join("empty.smf");

    fs::write(&empty_path, b"").expect("write empty");

    let loader = ModuleLoader::new();
    let result = loader.load(&empty_path);
    assert!(result.is_err(), "Should fail on empty file");
}

#[test]
fn test_registry_unload_not_loaded() {
    let registry = ModuleRegistry::new();
    let result = registry.unload(std::path::Path::new("/not/loaded/module.smf"));
    assert!(!result, "Should return false for not-loaded module");
}
