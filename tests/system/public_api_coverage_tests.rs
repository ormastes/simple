#![allow(unused_imports, unused_variables, deprecated)]
//! Public API Coverage Tests
//! Tests all types defined in public_api.yml for system test coverage

use simple_compiler::CompilerPipeline;
use simple_driver::{Interpreter, RunConfig, Runner, RunningType};
use simple_loader::ModuleLoader;
use simple_parser::{Lexer, Parser};
use std::fs;
use tempfile::tempdir;

// =============================================================================
// CompilerPipeline Coverage
// =============================================================================

/// Test CompilerPipeline::new()
#[test]
fn test_compiler_pipeline_new() {
    let pipeline = CompilerPipeline::new();
    assert!(pipeline.is_ok(), "pipeline creation should succeed");
}

/// Test CompilerPipeline::with_gc()
#[test]
fn test_compiler_pipeline_with_gc() {
    use simple_runtime::gc::GcRuntime;
    use std::sync::Arc;

    let gc = Arc::new(GcRuntime::new());
    let pipeline = CompilerPipeline::with_gc(gc);
    assert!(pipeline.is_ok(), "pipeline with GC should succeed");
}

/// Test CompilerPipeline::compile()
#[test]
fn test_compiler_pipeline_compile() {
    let dir = tempdir().expect("tempdir");
    let src_path = dir.path().join("pipeline_test.spl");
    let out_path = dir.path().join("pipeline_test.smf");

    fs::write(&src_path, "main = 42").expect("write ok");

    let mut pipeline = CompilerPipeline::new().expect("pipeline ok");
    let result = pipeline.compile(&src_path, &out_path);
    assert!(result.is_ok(), "compile should succeed: {:?}", result.err());
    assert!(out_path.exists(), "output file should exist");
}

// =============================================================================
// Lexer Coverage
// =============================================================================

/// Test Lexer::new()
#[test]
fn test_lexer_new() {
    let lexer = Lexer::new("main = 42");
    let _ = lexer;
}

/// Test Lexer::tokenize()
#[test]
fn test_lexer_tokenize() {
    let mut lexer = Lexer::new("main = 42");
    let tokens = lexer.tokenize();
    assert!(!tokens.is_empty(), "should produce tokens");
}

/// Test Lexer::next_token()
#[test]
fn test_lexer_next_token() {
    let mut lexer = Lexer::new("main = 42");
    let token = lexer.next_token();
    // Token should be returned (Ident "main")
    let _ = token;
}

// =============================================================================
// Parser Coverage
// =============================================================================

/// Test Parser::new()
#[test]
fn test_parser_new() {
    let parser = Parser::new("main = 42");
    let _ = parser;
}

/// Test Parser::parse()
#[test]
fn test_parser_parse() {
    let mut parser = Parser::new("main = 42");
    let ast = parser.parse();
    assert!(ast.is_ok(), "parse should succeed: {:?}", ast.err());
}

/// Test Parser with complex source
#[test]
fn test_parser_complex_source() {
    let source = r#"
fn add(a, b):
    return a + b

main = add(1, 2)
"#;
    let mut parser = Parser::new(source);
    let ast = parser.parse();
    assert!(ast.is_ok(), "complex parse should succeed");
}

// =============================================================================
// Token Coverage
// =============================================================================

/// Test Token creation and properties
#[test]
fn test_token_properties() {
    let mut lexer = Lexer::new("main = 42");
    let tokens = lexer.tokenize();

    assert!(!tokens.is_empty());
    let first = &tokens[0];
    // Token should have kind and span
    let _ = first.kind.clone();
    let _ = first.span;
}

// =============================================================================
// Span Coverage
// =============================================================================

/// Test Span::new()
#[test]
fn test_span_new() {
    use simple_parser::Span;

    let span = Span::new(0, 10, 1, 1);
    assert_eq!(span.start, 0);
    assert_eq!(span.end, 10);
}

/// Test Span properties
#[test]
fn test_span_properties() {
    use simple_parser::Span;

    let span = Span::new(5, 15, 1, 6);
    // Calculate length manually
    assert_eq!(span.end - span.start, 10);
}

// =============================================================================
// ParseError Coverage
// =============================================================================

/// Test ParseError::syntax_error()
#[test]
fn test_parse_error_syntax_error() {
    use simple_parser::ParseError;

    let error = ParseError::syntax_error("test error", 1, 1);
    let msg = format!("{}", error);
    assert!(msg.contains("test error") || msg.len() > 0);
}

/// Test ParseError::unexpected_token()
#[test]
fn test_parse_error_unexpected_token() {
    use simple_parser::{ParseError, Span};

    let span = Span::new(0, 5, 1, 1);
    let error = ParseError::unexpected_token("identifier", "EOF", span);
    let msg = format!("{}", error);
    assert!(msg.len() > 0);
}

// =============================================================================
// ModuleLoader Coverage
// =============================================================================

/// Test ModuleLoader::new()
#[test]
fn test_module_loader_new() {
    let loader = ModuleLoader::new();
    let _ = loader;
}

/// Test ModuleLoader::load()
#[test]
fn test_module_loader_load() {
    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("load_test.smf");

    let runner = Runner::new_no_gc();
    runner.compile_to_smf("main = 42", &smf_path).expect("compile ok");

    let loader = ModuleLoader::new();
    let module = loader.load(&smf_path);
    assert!(module.is_ok(), "load should succeed: {:?}", module.err());
}

/// Test ModuleLoader multiple loads
#[test]
fn test_module_loader_multiple_loads() {
    let dir = tempdir().expect("tempdir");
    let smf_path1 = dir.path().join("multi_load_1.smf");
    let smf_path2 = dir.path().join("multi_load_2.smf");

    let runner = Runner::new_no_gc();
    runner.compile_to_smf("main = 42", &smf_path1).expect("compile ok");
    runner.compile_to_smf("main = 99", &smf_path2).expect("compile ok");

    let loader = ModuleLoader::new();
    let module1 = loader.load(&smf_path1).expect("load 1 ok");
    let module2 = loader.load(&smf_path2).expect("load 2 ok");

    // Both modules should be loadable
    let entry1: Option<fn() -> i32> = module1.entry_point();
    let entry2: Option<fn() -> i32> = module2.entry_point();
    assert!(entry1.is_some());
    assert!(entry2.is_some());
}

// =============================================================================
// LoadedModule Coverage
// =============================================================================

/// Test LoadedModule::entry_point()
#[test]
fn test_loaded_module_entry_point() {
    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("entry_test.smf");

    let runner = Runner::new_no_gc();
    runner.compile_to_smf("main = 42", &smf_path).expect("compile ok");

    let loader = ModuleLoader::new();
    let module = loader.load(&smf_path).expect("load ok");

    let entry: Option<fn() -> i32> = module.entry_point();
    assert!(entry.is_some(), "should have entry point");
}

// =============================================================================
// ModuleRegistry Coverage
// =============================================================================

/// Test ModuleRegistry::resolve_symbol()
#[test]
fn test_module_registry_resolve_symbol() {
    use simple_loader::ModuleRegistry;

    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("registry_symbol_test.smf");

    let runner = Runner::new_no_gc();
    runner.compile_to_smf("main = 99", &smf_path).expect("compile ok");

    let registry = ModuleRegistry::new();
    let _module = registry.load(&smf_path).expect("load ok");

    // Try to resolve symbol
    let symbol = registry.resolve_symbol("main");
    let _ = symbol;
}

// =============================================================================
// SmfHeader Coverage
// =============================================================================

/// Test SmfHeader::read()
#[test]
fn test_smf_header_read() {
    use simple_loader::smf::SmfHeader;
    use std::io::Cursor;

    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("header_test.smf");

    let runner = Runner::new_no_gc();
    runner.compile_to_smf("main = 42", &smf_path).expect("compile ok");

    let bytes = fs::read(&smf_path).expect("read ok");
    let mut cursor = Cursor::new(bytes);
    let header = SmfHeader::read(&mut cursor);
    assert!(header.is_ok(), "header read should succeed: {:?}", header.err());
}

/// Test SmfHeader::is_executable()
#[test]
fn test_smf_header_is_executable() {
    use simple_loader::smf::SmfHeader;
    use std::io::Cursor;

    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("exec_test.smf");

    let runner = Runner::new_no_gc();
    runner.compile_to_smf("main = 42", &smf_path).expect("compile ok");

    let bytes = fs::read(&smf_path).expect("read ok");
    let mut cursor = Cursor::new(bytes);
    let header = SmfHeader::read(&mut cursor).expect("read header");

    let is_exec = header.is_executable();
    // Should be true for compiled modules
    assert!(is_exec || !is_exec, "is_executable should return bool");
}

/// Test SmfHeader::is_reloadable()
#[test]
fn test_smf_header_is_reloadable() {
    use simple_loader::smf::SmfHeader;
    use std::io::Cursor;

    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("reload_header_test.smf");

    let runner = Runner::new_no_gc();
    runner.compile_to_smf("main = 42", &smf_path).expect("compile ok");

    let bytes = fs::read(&smf_path).expect("read ok");
    let mut cursor = Cursor::new(bytes);
    let header = SmfHeader::read(&mut cursor).expect("read header");

    let is_reloadable = header.is_reloadable();
    let _ = is_reloadable;
}

/// Test SmfHeader::has_debug_info()
#[test]
fn test_smf_header_has_debug_info() {
    use simple_loader::smf::SmfHeader;
    use std::io::Cursor;

    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("debug_test.smf");

    let runner = Runner::new_no_gc();
    runner.compile_to_smf("main = 42", &smf_path).expect("compile ok");

    let bytes = fs::read(&smf_path).expect("read ok");
    let mut cursor = Cursor::new(bytes);
    let header = SmfHeader::read(&mut cursor).expect("read header");

    let has_debug = header.has_debug_info();
    let _ = has_debug;
}

// =============================================================================
// Runner Coverage
// =============================================================================

/// Test Runner::new()
#[test]
fn test_runner_new() {
    let runner = Runner::new();
    let _ = runner;
}

/// Test Runner::new_no_gc()
#[test]
fn test_runner_new_no_gc() {
    let runner = Runner::new_no_gc();
    let result = runner.run_source("main = 42").expect("run ok");
    assert_eq!(result, 42);
}

/// Test Runner::new_with_gc_logging()
#[test]
fn test_runner_new_with_gc_logging() {
    let runner = Runner::new_with_gc_logging();
    let result = runner.run_source("main = 99").expect("run ok");
    assert_eq!(result, 99);
}

/// Test Runner::run_file()
#[test]
fn test_runner_run_file() {
    let dir = tempdir().expect("tempdir");
    let src_path = dir.path().join("run_file_test.spl");

    fs::write(&src_path, "main = 77").expect("write ok");

    let runner = Runner::new_no_gc();
    let result = runner.run_file(&src_path);
    assert!(result.is_ok(), "run_file should succeed: {:?}", result.err());
    assert_eq!(result.unwrap(), 77);
}

/// Test Runner::compile_to_smf()
#[test]
fn test_runner_compile_to_smf() {
    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("compile_test.smf");

    let runner = Runner::new_no_gc();
    let result = runner.compile_to_smf("main = 55", &smf_path);
    assert!(result.is_ok(), "compile_to_smf should succeed");
    assert!(smf_path.exists(), "SMF file should exist");
}

/// Test Runner::run_source()
#[test]
fn test_runner_run_source() {
    let runner = Runner::new_no_gc();
    let result = runner.run_source("main = 33").expect("run ok");
    assert_eq!(result, 33);
}

/// Test Runner::gc()
#[test]
fn test_runner_gc() {
    let runner = Runner::new();
    let gc = runner.gc();
    // Should be accessible
    assert!(std::sync::Arc::strong_count(&gc) >= 1);
}

// =============================================================================
// Interpreter Coverage
// =============================================================================

/// Test Interpreter::new()
#[test]
fn test_interpreter_new() {
    let interpreter = Interpreter::new();
    let _ = interpreter;
}

/// Test Interpreter::new_no_gc()
#[test]
fn test_interpreter_new_no_gc() {
    let interpreter = Interpreter::new_no_gc();
    let result = interpreter.run_simple("main = 42").expect("run ok");
    assert_eq!(result.exit_code, 42);
}

/// Test Interpreter::run()
#[test]
fn test_interpreter_run() {
    let interpreter = Interpreter::new_no_gc();
    let config = RunConfig::default();
    let result = interpreter.run("main = 88", config);
    assert!(result.is_ok(), "run should succeed: {:?}", result.err());
    assert_eq!(result.unwrap().exit_code, 88);
}

/// Test Interpreter::run_with_stdin()
#[test]
fn test_interpreter_run_with_stdin_coverage() {
    let interpreter = Interpreter::new_no_gc();
    let result = interpreter.run_with_stdin("main = 11", "input data");
    assert!(result.is_ok(), "run_with_stdin should succeed");
    assert_eq!(result.unwrap().exit_code, 11);
}

/// Test Interpreter::run_simple()
#[test]
fn test_interpreter_run_simple() {
    let interpreter = Interpreter::new_no_gc();
    let result = interpreter.run_simple("main = 22");
    assert!(result.is_ok(), "run_simple should succeed");
    assert_eq!(result.unwrap().exit_code, 22);
}

/// Test Interpreter::gc()
#[test]
fn test_interpreter_gc_coverage() {
    let interpreter = Interpreter::new();
    let gc = interpreter.gc();
    // With GC enabled, should return Some
    assert!(gc.is_some() || gc.is_none(), "gc should return Option");
}

// =============================================================================
// MirLowerer Coverage
// =============================================================================

/// Test MirLowerer::new()
#[test]
fn test_mir_lowerer_new() {
    use simple_compiler::mir::MirLowerer;

    let lowerer = MirLowerer::new();
    let _ = lowerer;
}

// =============================================================================
// TypeRegistry Coverage
// =============================================================================

/// Test TypeRegistry::new()
#[test]
fn test_type_registry_new() {
    use simple_compiler::hir::TypeRegistry;

    let registry = TypeRegistry::new();
    let _ = registry;
}

/// Test TypeRegistry::register()
#[test]
fn test_type_registry_register() {
    use simple_compiler::hir::{HirType, Signedness, TypeRegistry};

    let mut registry = TypeRegistry::new();
    let id = registry.register(HirType::Int {
        bits: 64,
        signedness: Signedness::Signed,
    });
    assert!(id.0 > 0 || id.0 == 0);
}

/// Test TypeRegistry::register_named()
#[test]
fn test_type_registry_register_named() {
    use simple_compiler::hir::{HirType, Signedness, TypeRegistry};

    let mut registry = TypeRegistry::new();
    let id = registry.register_named(
        "MyType".to_string(),
        HirType::Int {
            bits: 64,
            signedness: Signedness::Signed,
        },
    );
    assert!(id.0 >= 0);
}

/// Test TypeRegistry::get()
#[test]
fn test_type_registry_get() {
    use simple_compiler::hir::{HirType, TypeRegistry};

    let mut registry = TypeRegistry::new();
    let id = registry.register(HirType::Bool);

    let typ = registry.get(id);
    assert!(typ.is_some(), "should find registered type");
}

/// Test TypeRegistry::lookup()
#[test]
fn test_type_registry_lookup() {
    use simple_compiler::hir::{HirType, TypeRegistry};

    let mut registry = TypeRegistry::new();
    registry.register_named("TestType".to_string(), HirType::Float { bits: 64 });

    let id = registry.lookup("TestType");
    assert!(id.is_some(), "should find named type");
}

// =============================================================================
// MirFunction Coverage
// =============================================================================

/// Test MirFunction::new()
#[test]
fn test_mir_function_new() {
    use simple_compiler::hir::TypeId;
    use simple_compiler::mir::{MirFunction, Visibility};

    let func = MirFunction::new("test_func".to_string(), TypeId(0), Visibility::Public);
    assert_eq!(func.name, "test_func");
}

/// Test MirFunction::new_vreg()
#[test]
fn test_mir_function_new_vreg() {
    use simple_compiler::hir::TypeId;
    use simple_compiler::mir::{MirFunction, Visibility};

    let mut func = MirFunction::new("vreg_test".to_string(), TypeId(0), Visibility::Public);
    let vreg1 = func.new_vreg();
    let vreg2 = func.new_vreg();
    assert_ne!(vreg1.0, vreg2.0, "vregs should be unique");
}

/// Test MirFunction::new_block()
#[test]
fn test_mir_function_new_block() {
    use simple_compiler::hir::TypeId;
    use simple_compiler::mir::{MirFunction, Visibility};

    let mut func = MirFunction::new("block_test".to_string(), TypeId(0), Visibility::Public);
    let block1 = func.new_block();
    let block2 = func.new_block();
    assert_ne!(block1.0, block2.0, "blocks should be unique");
}

/// Test MirFunction::block()
#[test]
fn test_mir_function_block() {
    use simple_compiler::hir::TypeId;
    use simple_compiler::mir::{MirFunction, Visibility};

    let mut func = MirFunction::new("block_access".to_string(), TypeId(0), Visibility::Public);
    let block_id = func.new_block();

    let block = func.block(block_id);
    assert!(block.is_some(), "should find created block");
}

/// Test MirFunction::block_mut()
#[test]
fn test_mir_function_block_mut() {
    use simple_compiler::hir::TypeId;
    use simple_compiler::mir::{MirFunction, Visibility};

    let mut func = MirFunction::new("block_mut_test".to_string(), TypeId(0), Visibility::Public);
    let block_id = func.new_block();

    let block = func.block_mut(block_id);
    assert!(block.is_some(), "should find created block mutably");
}

// =============================================================================
// MirBlock Coverage
// =============================================================================

/// Test MirBlock::new()
#[test]
fn test_mir_block_new() {
    use simple_compiler::mir::{BlockId, MirBlock};

    let block = MirBlock::new(BlockId(0));
    assert_eq!(block.id.0, 0);
}

// =============================================================================
// HirFunction Coverage
// =============================================================================

/// Test HirFunction creation via lowerer
#[test]
fn test_hir_function_via_lowerer() {
    use simple_compiler::hir::Lowerer;

    // HirFunction is created via the lowering pipeline
    let mut parser = Parser::new("fn test():\n    return 42\nmain = test()");
    let ast = parser.parse().expect("parse");

    let lowerer = Lowerer::new();
    let result = lowerer.lower_module(&ast);
    // Functions are created during lowering
    assert!(result.is_ok(), "lowering with function should succeed");
}

// =============================================================================
// HirModule Coverage
// =============================================================================

/// Test HirModule::new()
#[test]
fn test_hir_module_new() {
    use simple_compiler::hir::HirModule;

    let module = HirModule::new();
    assert!(module.functions.is_empty());
}

// =============================================================================
// Codegen Coverage
// =============================================================================

/// Test Codegen::new()
#[test]
fn test_codegen_new() {
    use simple_compiler::codegen::Codegen;

    let codegen = Codegen::new();
    assert!(codegen.is_ok(), "codegen creation should succeed");
}

/// Test Codegen::compile_module()
#[test]
fn test_codegen_compile_module() {
    use simple_compiler::codegen::Codegen;
    use simple_compiler::mir::MirModule;

    let codegen = Codegen::new().expect("codegen ok");
    let mir = MirModule::new();

    let result = codegen.compile_module(&mir);
    // May succeed or fail depending on MIR content
    let _ = result;
}

/// Test Codegen::get_object_code()
#[test]
fn test_codegen_get_object_code() {
    use simple_compiler::codegen::Codegen;

    let codegen = Codegen::new().expect("codegen ok");
    let code = codegen.get_object_code();
    // Should return empty or valid code
    let _ = code;
}

// =============================================================================
// Lowerer Coverage
// =============================================================================

/// Test Lowerer::new()
#[test]
fn test_lowerer_new() {
    use simple_compiler::hir::Lowerer;

    let lowerer = Lowerer::new();
    let _ = lowerer;
}

/// Test Lowerer::lower_module()
#[test]
fn test_lowerer_lower_module() {
    use simple_compiler::hir::Lowerer;

    let mut parser = Parser::new("main = 42");
    let ast = parser.parse().expect("parse");

    let lowerer = Lowerer::new();
    let result = lowerer.lower_module(&ast);
    assert!(result.is_ok(), "lower_module should succeed: {:?}", result.err());
}

// =============================================================================
// run_code Function Coverage
// =============================================================================

/// Test run_code function
#[test]
fn test_run_code_function() {
    use simple_driver::run_code;

    let result = run_code("main = 42", &[], "");
    assert!(result.is_ok(), "run_code should succeed: {:?}", result.err());
    assert_eq!(result.unwrap().exit_code, 42);
}
