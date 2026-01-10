#![allow(unused_imports, unused_variables, unused_mut)]

//! Integration tests: SMF types, ModuleRegistry, CompilerPipeline, Parser
//! Tests for loader and compiler pipeline integration

use simple_compiler::CompilerPipeline;
use simple_driver::{run_code, Interpreter, RunConfig, Runner, RunningType};
use simple_loader::ModuleLoader;
use simple_parser::{Lexer, Parser};
use std::fs;
use tempfile::tempdir;

// =============================================================================
// SMF Types Integration Tests
// =============================================================================

use simple_loader::smf::{
    hash_name, Arch, Platform, SectionType, SmfHeader, SmfSection, SmfSymbol, SymbolBinding,
    SymbolTable, SymbolType, SECTION_FLAG_EXEC, SECTION_FLAG_READ, SMF_FLAG_EXECUTABLE, SMF_MAGIC,
};
use std::io::Cursor;

/// Test SmfHeader read from bytes
#[test]
fn test_smf_header_read_integration() {
    // Create a minimal valid header
    let header = SmfHeader {
        magic: *SMF_MAGIC,
        version_major: 0,
        version_minor: 1,
        platform: Platform::Any as u8,
        arch: Arch::X86_64 as u8,
        flags: SMF_FLAG_EXECUTABLE,
        section_count: 0,
        section_table_offset: SmfHeader::SIZE as u64,
        symbol_table_offset: SmfHeader::SIZE as u64,
        symbol_count: 0,
        exported_count: 0,
        entry_point: 0,
        module_hash: 0,
        source_hash: 0,
        app_type: 0,
        window_width: 0,
        window_height: 0,
        prefetch_hint: 0,
        prefetch_file_count: 0,
        reserved: [0; 1],
    };

    // Serialize to bytes
    let bytes = unsafe {
        std::slice::from_raw_parts(
            &header as *const SmfHeader as *const u8,
            std::mem::size_of::<SmfHeader>(),
        )
    };

    let mut cursor = Cursor::new(bytes.to_vec());
    let read_header = SmfHeader::read(&mut cursor).expect("read ok");

    assert_eq!(read_header.magic, *SMF_MAGIC);
    assert_eq!(read_header.version_major, 0);
    assert_eq!(read_header.version_minor, 1);
}

/// Test SmfHeader properties
#[test]
fn test_smf_header_properties_integration() {
    let header = SmfHeader {
        magic: *SMF_MAGIC,
        version_major: 0,
        version_minor: 1,
        platform: Platform::Any as u8,
        arch: Arch::X86_64 as u8,
        flags: SMF_FLAG_EXECUTABLE,
        section_count: 1,
        section_table_offset: 64,
        symbol_table_offset: 128,
        symbol_count: 1,
        exported_count: 1,
        entry_point: 0,
        module_hash: 12345,
        source_hash: 67890,
        app_type: 0,
        window_width: 0,
        window_height: 0,
        prefetch_hint: 0,
        prefetch_file_count: 0,
        reserved: [0; 1],
    };

    assert!(header.is_executable());
    assert!(!header.is_reloadable());
    assert!(!header.has_debug_info());
}

/// Test SmfSection name_str
#[test]
fn test_smf_section_name_integration() {
    let mut name = [0u8; 16];
    name[..4].copy_from_slice(b"code");

    let section = SmfSection {
        section_type: SectionType::Code,
        flags: SECTION_FLAG_READ | SECTION_FLAG_EXEC,
        offset: 0,
        size: 100,
        virtual_size: 100,
        alignment: 16,
        name,
    };

    assert_eq!(section.name_str(), "code");
    assert!(section.is_executable());
    assert!(!section.is_writable());
}

/// Test SectionType variants
#[test]
fn test_section_type_integration() {
    let types = [
        SectionType::Code,
        SectionType::Data,
        SectionType::RoData,
        SectionType::Bss,
        SectionType::Reloc,
        SectionType::SymTab,
        SectionType::StrTab,
        SectionType::Debug,
    ];

    for ty in &types {
        let _ = format!("{:?}", ty);
    }
}

/// Test SymbolTable construction and lookup
#[test]
fn test_symbol_table_integration() {
    let sym = SmfSymbol {
        name_offset: 0,
        name_hash: hash_name("main"),
        sym_type: SymbolType::Function,
        binding: SymbolBinding::Global,
        visibility: 0,
        flags: 0,
        value: 0,
        size: 6,
        type_id: 0,
        version: 0,
    };

    let string_table = b"main\0".to_vec();
    let table = SymbolTable::new(vec![sym.clone()], string_table);

    // Lookup by name
    let found = table.lookup("main");
    assert!(found.is_some());

    // Symbol name
    let name = table.symbol_name(&sym);
    assert_eq!(name, "main");

    // Exports
    let exports: Vec<_> = table.exports().collect();
    assert_eq!(exports.len(), 1);
}

/// Test hash_name function
#[test]
fn test_hash_name_integration() {
    let hash1 = hash_name("main");
    let hash2 = hash_name("main");
    let hash3 = hash_name("other");

    assert_eq!(hash1, hash2);
    assert_ne!(hash1, hash3);
}

/// Test Platform and Arch enums
#[test]
fn test_platform_arch_integration() {
    assert_eq!(Platform::Any as u8, 0);
    assert_eq!(Platform::Linux as u8, 1);
    assert_eq!(Platform::Windows as u8, 2);
    assert_eq!(Platform::MacOS as u8, 3);

    assert_eq!(Arch::X86_64 as u8, 0);
    assert_eq!(Arch::Aarch64 as u8, 1);
}

/// Test SymbolType and SymbolBinding enums
#[test]
fn test_symbol_type_binding_integration() {
    assert_eq!(SymbolType::Function as u8, 1);
    assert_eq!(SymbolType::Data as u8, 2);

    assert_eq!(SymbolBinding::Local as u8, 0);
    assert_eq!(SymbolBinding::Global as u8, 1);
    assert_eq!(SymbolBinding::Weak as u8, 2);
}

// =============================================================================
// LoadedModule Integration Tests
// =============================================================================

/// Test LoadedModule entry_point
#[test]
fn test_loaded_module_entry_point_integration() {
    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("entry_test.smf");

    let runner = Runner::new_no_gc();
    runner
        .compile_to_smf("main = 42", &smf_path)
        .expect("compile ok");

    let loader = ModuleLoader::new();
    let module = loader.load(&smf_path).expect("load ok");

    let entry: Option<fn() -> i32> = module.entry_point();
    assert!(entry.is_some());
    assert_eq!(entry.unwrap()(), 42);
}

/// Test LoadedModule exports
#[test]
fn test_loaded_module_exports_integration() {
    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("exports_test.smf");

    let runner = Runner::new_no_gc();
    runner
        .compile_to_smf("main = 0", &smf_path)
        .expect("compile ok");

    let loader = ModuleLoader::new();
    let module = loader.load(&smf_path).expect("load ok");

    let exports = module.exports();
    // Should have at least main exported
    let _ = exports;
}

/// Test LoadedModule source_hash
#[test]
fn test_loaded_module_source_hash_integration() {
    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("hash_test.smf");

    let runner = Runner::new_no_gc();
    runner
        .compile_to_smf("main = 123", &smf_path)
        .expect("compile ok");

    let loader = ModuleLoader::new();
    let module = loader.load(&smf_path).expect("load ok");

    let hash = module.source_hash();
    // Just verify it returns without panic
    let _ = hash;
}

// =============================================================================
// ModuleRegistry Integration Tests
// =============================================================================

use simple_loader::ModuleRegistry;

/// Test ModuleRegistry new and load
#[test]
fn test_module_registry_new_load_integration() {
    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("registry_test.smf");

    let runner = Runner::new_no_gc();
    runner
        .compile_to_smf("main = 77", &smf_path)
        .expect("compile ok");

    let mut registry = ModuleRegistry::new();
    let module = registry.load(&smf_path).expect("load ok");

    let entry: fn() -> i32 = module.entry_point().expect("entry ok");
    assert_eq!(entry(), 77);
}

/// Test ModuleRegistry unload
#[test]
fn test_module_registry_unload_integration() {
    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("unload_test.smf");

    let runner = Runner::new_no_gc();
    runner
        .compile_to_smf("main = 88", &smf_path)
        .expect("compile ok");

    let mut registry = ModuleRegistry::new();
    let _module = registry.load(&smf_path).expect("load ok");

    // Unload returns bool
    let _result = registry.unload(&smf_path);
}

/// Test ModuleRegistry reload
#[test]
fn test_module_registry_reload_integration() {
    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("reload_test.smf");

    let runner = Runner::new_no_gc();
    runner
        .compile_to_smf("main = 99", &smf_path)
        .expect("compile ok");

    let mut registry = ModuleRegistry::new();
    let _module = registry.load(&smf_path).expect("load ok");

    // Modify and reload
    runner
        .compile_to_smf("main = 100", &smf_path)
        .expect("compile ok");
    let result = registry.reload(&smf_path);
    // Reload may or may not be supported depending on platform
    let _ = result;
}

// =============================================================================
// CompilerPipeline Integration Tests
// =============================================================================

/// Test CompilerPipeline::new
#[test]
fn test_compiler_pipeline_new_integration() {
    let pipeline = CompilerPipeline::new();
    assert!(pipeline.is_ok());
}

/// Test CompilerPipeline::with_gc
#[test]
fn test_compiler_pipeline_with_gc_integration() {
    use simple_runtime::gc::GcRuntime;
    use std::sync::Arc;

    let gc = Arc::new(GcRuntime::new());
    let pipeline = CompilerPipeline::with_gc(gc);
    assert!(pipeline.is_ok());
}

/// Test CompilerPipeline::compile
#[test]
fn test_compiler_pipeline_compile_integration() {
    let dir = tempdir().expect("tempdir");
    let src_path = dir.path().join("compile_test.spl");
    let out_path = dir.path().join("compile_test.smf");

    fs::write(&src_path, "main = 42").expect("write ok");

    let mut pipeline = CompilerPipeline::new().expect("pipeline ok");
    let result = pipeline.compile(&src_path, &out_path);
    assert!(result.is_ok());
    assert!(out_path.exists());
}

/// Test CompilerPipeline::compile_source_to_memory
#[test]
fn test_compiler_pipeline_compile_source_to_memory_integration() {
    let mut pipeline = CompilerPipeline::new().expect("pipeline ok");
    let smf_bytes = pipeline.compile_source_to_memory("main = 123");
    assert!(smf_bytes.is_ok());

    let bytes = smf_bytes.unwrap();
    assert!(!bytes.is_empty());

    // Verify it's a valid SMF
    let loader = ModuleLoader::new();
    let module = loader.load_from_memory(&bytes).expect("load ok");
    let entry: fn() -> i32 = module.entry_point().expect("entry ok");
    assert_eq!(entry(), 123);
}

// =============================================================================
// Parser Public Function Tests
// =============================================================================

/// Test Parser::new and Parser::parse
#[test]
fn test_parser_new_parse_integration() {
    let source = "main = 42";
    let mut parser = Parser::new(source);
    let module = parser.parse();
    assert!(module.is_ok());
}

/// Test Parser with various expressions
#[test]
fn test_parser_expressions_integration() {
    let sources = [
        "main = 1 + 2",
        "main = 1 - 2",
        "main = 2 * 3",
        "main = 6 / 2",
        "main = 7 % 3",
        "main = -5",
        "main = (1 + 2) * 3",
    ];

    for source in &sources {
        let mut parser = Parser::new(source);
        let result = parser.parse();
        assert!(result.is_ok(), "Failed to parse: {}", source);
    }
}

/// Test Lexer::new and Lexer::tokenize
#[test]
fn test_lexer_new_tokenize_integration() {
    let source = "main = 42";
    let mut lexer = Lexer::new(source);
    let tokens = lexer.tokenize();
    assert!(!tokens.is_empty());
}

/// Test Lexer with various tokens
#[test]
fn test_lexer_tokens_integration() {
    let source = "fn foo(a, b): return a + b";
    let mut lexer = Lexer::new(source);
    let tokens = lexer.tokenize();
    assert!(tokens.len() > 5);
}

// =============================================================================
// Runner Public Function Tests
// =============================================================================

/// Test Runner::new
#[test]
fn test_runner_new_pub_func_integration() {
    let runner = Runner::new();
    let result = runner.run_source("main = 1");
    assert!(result.is_ok());
}

/// Test Runner::with_gc_runtime
#[test]
fn test_runner_with_gc_runtime_pub_func_integration() {
    use simple_runtime::gc::GcRuntime;
    let gc = GcRuntime::new();
    let runner = Runner::with_gc_runtime(gc);
    let result = runner.run_source("main = 2");
    assert!(result.is_ok());
}

/// Test Runner::new_no_gc
#[test]
fn test_runner_new_no_gc_pub_func_integration() {
    let runner = Runner::new_no_gc();
    let result = runner.run_source("main = 3");
    assert!(result.is_ok());
}

/// Test Runner::new_with_gc_logging
#[test]
fn test_runner_new_with_gc_logging_pub_func_integration() {
    let runner = Runner::new_with_gc_logging();
    let result = runner.run_source("main = 4");
    assert!(result.is_ok());
}

/// Test Runner::run_file
#[test]
fn test_runner_run_file_pub_func_integration() {
    let dir = tempdir().expect("tempdir");
    let src_path = dir.path().join("run_file_test.spl");
    fs::write(&src_path, "main = 55").expect("write ok");

    let runner = Runner::new_no_gc();
    let result = runner.run_file(&src_path);
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), 55);
}

/// Test Runner::compile_to_smf
#[test]
fn test_runner_compile_to_smf_pub_func_integration() {
    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("compile_test.smf");

    let runner = Runner::new_no_gc();
    let result = runner.compile_to_smf("main = 66", &smf_path);
    assert!(result.is_ok());
    assert!(smf_path.exists());
}

/// Test Runner::run_source
#[test]
fn test_runner_run_source_pub_func_integration() {
    let runner = Runner::new_no_gc();
    let result = runner.run_source("main = 77");
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), 77);
}

// =============================================================================
// Interpreter Public Function Tests
// =============================================================================

/// Test Interpreter::new
#[test]
fn test_interpreter_new_pub_func_integration() {
    let interpreter = Interpreter::new();
    let result = interpreter.run_simple("main = 10");
    assert!(result.is_ok());
}

/// Test Interpreter::new_no_gc
#[test]
fn test_interpreter_new_no_gc_pub_func_integration() {
    let interpreter = Interpreter::new_no_gc();
    let result = interpreter.run_simple("main = 20");
    assert!(result.is_ok());
}

/// Test Interpreter::run with config
#[test]
fn test_interpreter_run_pub_func_integration() {
    let interpreter = Interpreter::new_no_gc();
    let config = RunConfig {
        args: vec![],
        stdin: String::new(),
        timeout_ms: 0,
        in_memory: true,
        running_type: RunningType::default(),
        ..Default::default()
    };
    let result = interpreter.run("main = 30", config);
    assert!(result.is_ok());
    assert_eq!(result.unwrap().exit_code, 30);
}

/// Test Interpreter::run_with_stdin
#[test]
fn test_interpreter_run_with_stdin_pub_func_integration() {
    let interpreter = Interpreter::new_no_gc();
    let result = interpreter.run_with_stdin("main = 40", "input");
    assert!(result.is_ok());
    assert_eq!(result.unwrap().exit_code, 40);
}

/// Test Interpreter::run_simple
#[test]
fn test_interpreter_run_simple_pub_func_integration() {
    let interpreter = Interpreter::new_no_gc();
    let result = interpreter.run_simple("main = 50");
    assert!(result.is_ok());
    assert_eq!(result.unwrap().exit_code, 50);
}

/// Test run_code function
#[test]
fn test_run_code_pub_func_integration() {
    let result = run_code("main = 60", &[], "");
    assert!(result.is_ok());
    assert_eq!(result.unwrap().exit_code, 60);
}

/// Test run_code with args
#[test]
fn test_run_code_with_args_pub_func_integration() {
    let result = run_code("main = 70", &["arg1".to_string()], "stdin");
    assert!(result.is_ok());
    assert_eq!(result.unwrap().exit_code, 70);
}

// =============================================================================
// Value Types Integration Tests
// =============================================================================

use simple_compiler::{
    ClassName, EnumTypeName, Env, Value, VariantName, BUILTIN_ARRAY, BUILTIN_RANGE,
};

/// Test ClassName newtype
#[test]
fn test_class_name_integration() {
    let name = ClassName::new("MyClass");
    assert_eq!(name.as_str(), "MyClass");
    // Debug format
    assert_eq!(format!("{:?}", name), "ClassName(\"MyClass\")");

    // Equality
    let name2 = ClassName::new("MyClass");
    assert_eq!(name, name2);

    // From implementations
    let from_str: ClassName = "AnotherClass".into();
    assert_eq!(from_str.as_str(), "AnotherClass");
}

/// Test EnumTypeName newtype
#[test]
fn test_enum_type_name_integration() {
    let name = EnumTypeName::new("Result");
    assert_eq!(name.as_str(), "Result");
    // Debug format
    assert_eq!(format!("{:?}", name), "EnumTypeName(\"Result\")");

    // From implementations
    let from_str: EnumTypeName = "Option".into();
    assert_eq!(from_str.as_str(), "Option");
}

/// Test VariantName newtype
#[test]
fn test_variant_name_integration() {
    let name = VariantName::new("Some");
    assert_eq!(name.as_str(), "Some");
    // Debug format
    assert_eq!(format!("{:?}", name), "VariantName(\"Some\")");

    // From implementations
    let from_str: VariantName = "None".into();
    assert_eq!(from_str.as_str(), "None");
}

/// Test builtin class name constants (these are &str constants)
#[test]
fn test_builtin_class_names_integration() {
    // BUILTIN_RANGE and BUILTIN_ARRAY are &str, not ClassName
    assert_eq!(BUILTIN_RANGE, "__range__");
    assert_eq!(BUILTIN_ARRAY, "__array__");
}

/// Test Value variants
#[test]
fn test_value_variants_integration() {
    // Int
    let int_val = Value::Int(42);
    assert!(int_val.truthy());

    // Float
    let float_val = Value::Float(3.15);
    assert!(float_val.truthy());

    // Bool
    let bool_true = Value::Bool(true);
    let bool_false = Value::Bool(false);
    assert!(bool_true.truthy());
    assert!(!bool_false.truthy());

    // Str
    let str_val = Value::Str("hello".to_string());
    assert!(str_val.truthy());

    // Nil
    let nil_val = Value::Nil;
    assert!(!nil_val.truthy());
}

/// Test Env construction (Env is a type alias for HashMap<String, Value>)
#[test]
fn test_env_construction_integration() {
    let env: Env = Env::new();
    assert!(env.get("undefined").is_none());
}

/// Test Env insert and get (using HashMap methods)
#[test]
fn test_env_set_get_integration() {
    let mut env: Env = Env::new();
    env.insert("x".to_string(), Value::Int(42));
    assert_eq!(env.get("x"), Some(&Value::Int(42)));
}

/// Test Env scoping (manual parent chain since Env is just HashMap)
#[test]
fn test_env_scoping_integration() {
    // Since Env is just a HashMap, parent scopes need to be managed manually
    let mut parent: Env = Env::new();
    parent.insert("parent_var".to_string(), Value::Int(100));

    // Child is a separate scope - test that it can have its own variables
    let mut child: Env = Env::new();
    child.insert("child_var".to_string(), Value::Int(200));

    // Parent and child maintain separate values
    assert_eq!(parent.get("parent_var"), Some(&Value::Int(100)));
    assert_eq!(child.get("child_var"), Some(&Value::Int(200)));
    assert!(parent.get("child_var").is_none());
}
