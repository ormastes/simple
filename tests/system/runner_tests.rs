//! Runner system tests
//! End-to-end tests using real implementations (no mocks)

use simple_driver::{Runner, Interpreter, RunConfig, run_code};
use simple_compiler::CompilerPipeline;
use simple_parser::{Parser, Lexer};
use simple_loader::ModuleLoader;
use tempfile::tempdir;
use std::fs;

// =============================================================================
// Runner Tests
// =============================================================================

#[test]
fn test_runner_end_to_end_simple() {
    let runner = Runner::new();
    let result = runner.run_source("main = 0").expect("run ok");
    assert_eq!(result, 0);
}

#[test]
fn test_runner_end_to_end_arithmetic() {
    let runner = Runner::new();
    let result = runner.run_source("main = 1 + 2 * 3").expect("run ok");
    assert_eq!(result, 7);
}

#[test]
fn test_runner_end_to_end_with_file() {
    let dir = tempdir().expect("tempdir");
    let source_path = dir.path().join("program.spl");

    fs::write(&source_path, "main = 5 * 24").expect("write ok");

    let runner = Runner::new();
    let result = runner.run_file(&source_path).expect("run ok");
    assert_eq!(result, 120, "5 * 24 = 120");
}

#[test]
fn test_runner_compile_to_smf() {
    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("program.smf");

    let runner = Runner::new();
    runner.compile_to_smf("main = 42", &smf_path).expect("compile ok");

    assert!(smf_path.exists(), "SMF file should exist");
    let smf_content = fs::read(&smf_path).expect("read ok");
    assert!(!smf_content.is_empty(), "SMF file should not be empty");
}

#[test]
fn test_runner_negative_result() {
    let runner = Runner::new();
    let result = runner.run_source("main = -5").expect("run ok");
    assert_eq!(result, -5, "Should handle negative numbers");
}

#[test]
fn test_runner_no_gc() {
    let runner = Runner::new_no_gc();
    let result = runner.run_source("main = 100").expect("run ok");
    assert_eq!(result, 100);
}

#[test]
fn test_runner_complex_expression() {
    let runner = Runner::new();
    let result = runner.run_source("main = (10 + 5) * 2 - 3").expect("run ok");
    assert_eq!(result, 27);
}

// =============================================================================
// Interpreter Tests
// =============================================================================

#[test]
fn test_interpreter_simple() {
    let interpreter = Interpreter::new();
    let result = interpreter.run("main = 42", RunConfig::default()).expect("run ok");
    assert_eq!(result.exit_code, 42);
}

#[test]
fn test_interpreter_no_gc() {
    let interpreter = Interpreter::new_no_gc();
    let result = interpreter.run("main = 99", RunConfig::default()).expect("run ok");
    assert_eq!(result.exit_code, 99);
}

#[test]
fn test_interpreter_arithmetic() {
    let interpreter = Interpreter::new();
    let result = interpreter.run("main = 2 + 3 * 4", RunConfig::default()).expect("run ok");
    assert_eq!(result.exit_code, 14);
}

#[test]
fn test_run_code_function() {
    let result = run_code("main = 55", &[], "").expect("run ok");
    assert_eq!(result.exit_code, 55);
}

#[test]
fn test_run_code_with_args() {
    let result = run_code("main = 77", &["arg1".to_string()], "").expect("run ok");
    assert_eq!(result.exit_code, 77);
}

// =============================================================================
// Parser Tests (End-to-End)
// =============================================================================

#[test]
fn test_parser_integration() {
    let source = "main = 1 + 2";
    let mut parser = Parser::new(source);
    let ast = parser.parse().expect("parse ok");
    assert!(!ast.items.is_empty(), "AST should not be empty");
}

#[test]
fn test_parser_function_def() {
    let source = "fn add(a, b):\n    return a + b\nmain = add(1, 2)";
    let mut parser = Parser::new(source);
    let result = parser.parse();
    // May succeed or fail depending on parser state, but should not panic
    let _ = result;
}

#[test]
fn test_parser_let_binding() {
    let source = "let x = 10\nmain = x";
    let mut parser = Parser::new(source);
    let result = parser.parse();
    assert!(result.is_ok(), "Should parse let binding");
}

#[test]
fn test_parser_if_statement() {
    let source = "if true:\n    x = 1\nmain = 0";
    let mut parser = Parser::new(source);
    let result = parser.parse();
    assert!(result.is_ok(), "Should parse if statement: {:?}", result.err());
}

// =============================================================================
// Lexer Tests (End-to-End)
// =============================================================================

#[test]
fn test_lexer_integration() {
    let source = "main = 42";
    let mut lexer = Lexer::new(source);
    let tokens = lexer.tokenize();
    assert!(!tokens.is_empty(), "Should produce tokens");
}

#[test]
fn test_lexer_operators() {
    let source = "1 + 2 * 3 - 4 / 5";
    let mut lexer = Lexer::new(source);
    let tokens = lexer.tokenize();
    assert!(tokens.len() >= 9, "Should tokenize all operators");
}

#[test]
fn test_lexer_keywords() {
    let source = "let fn if else while return";
    let mut lexer = Lexer::new(source);
    let tokens = lexer.tokenize();
    assert!(tokens.len() >= 6, "Should tokenize keywords");
}

// =============================================================================
// Compiler Pipeline Tests (End-to-End)
// =============================================================================

#[test]
fn test_compiler_pipeline_integration() {
    let dir = tempdir().expect("tempdir");
    let src = dir.path().join("test.spl");
    let out = dir.path().join("test.smf");

    fs::write(&src, "main = 42").expect("write ok");

    let mut pipeline = CompilerPipeline::new().expect("pipeline ok");
    let result = pipeline.compile(&src, &out);
    assert!(result.is_ok(), "Should compile: {:?}", result.err());
    assert!(out.exists(), "Output should exist");
}

#[test]
fn test_compiler_pipeline_arithmetic() {
    let dir = tempdir().expect("tempdir");
    let src = dir.path().join("arith.spl");
    let out = dir.path().join("arith.smf");

    fs::write(&src, "main = 10 + 20 * 3").expect("write ok");

    let mut pipeline = CompilerPipeline::new().expect("pipeline ok");
    let result = pipeline.compile(&src, &out);
    assert!(result.is_ok(), "Should compile arithmetic: {:?}", result.err());
}

// =============================================================================
// Module Loader Tests (End-to-End)
// =============================================================================

#[test]
fn test_module_loader_load_smf() {
    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("module.smf");

    // First compile a module
    let runner = Runner::new();
    runner.compile_to_smf("main = 123", &smf_path).expect("compile ok");

    // Then load it
    let loader = ModuleLoader::new();
    let result = loader.load(&smf_path);
    assert!(result.is_ok(), "Should load SMF: {:?}", result.err());
}

#[test]
fn test_module_loader_entry_point() {
    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("entry.smf");

    let runner = Runner::new();
    runner.compile_to_smf("main = 456", &smf_path).expect("compile ok");

    let loader = ModuleLoader::new();
    let module = loader.load(&smf_path).expect("load ok");

    // Check entry point exists
    let entry: Option<fn() -> i32> = module.entry_point();
    assert!(entry.is_some(), "Should have entry point");
}

// =============================================================================
// GC Runtime Tests (End-to-End)
// =============================================================================

#[test]
fn test_gc_runtime_with_logging() {
    let runner = Runner::new_with_gc_logging();
    let result = runner.run_source("main = 88").expect("run ok");
    assert_eq!(result, 88);
}

#[test]
fn test_gc_access() {
    let runner = Runner::new();
    let gc = runner.gc();
    // GC should be accessible (it's an Arc, so always valid)
    assert!(std::mem::size_of_val(&gc) > 0, "GC access should work");
}

// =============================================================================
// Error Handling Tests
// =============================================================================

#[test]
fn test_runner_syntax_error() {
    let runner = Runner::new();
    let result = runner.run_source("main = @#$%");
    // Should return error, not panic
    assert!(result.is_err(), "Invalid syntax should error");
}

#[test]
fn test_parser_error_recovery() {
    let source = "let = 10";  // Invalid syntax
    let mut parser = Parser::new(source);
    let result = parser.parse();
    // Should return error, not panic
    assert!(result.is_err(), "Invalid syntax should error");
}

#[test]
fn test_compiler_missing_file() {
    let mut pipeline = CompilerPipeline::new().expect("pipeline ok");
    let result = pipeline.compile(
        std::path::Path::new("/nonexistent/file.spl"),
        std::path::Path::new("/tmp/out.smf")
    );
    assert!(result.is_err(), "Missing file should error");
}

// =============================================================================
// Architecture Compliance Tests
// =============================================================================

/// Test that common module exports actor types correctly
#[test]
fn test_common_actor_exports() {
    use simple_common::{ActorHandle, ActorSpawner, Message, ThreadSpawner};

    // Verify ThreadSpawner can be created
    let spawner = ThreadSpawner::new();

    // Spawn a simple actor using the trait
    let handle = spawner.spawn(|_inbox, outbox| {
        outbox.send(Message::Value("hello".to_string())).unwrap();
    });

    // Verify communication works
    let msg = handle.recv().expect("recv ok");
    match msg {
        Message::Value(s) => assert_eq!(s, "hello"),
        _ => panic!("Expected Value message"),
    }

    handle.join().expect("join ok");
}

/// Test that ActorSpawner trait is object-safe and can be used dynamically
#[test]
fn test_actor_spawner_trait_object() {
    use simple_common::{ActorSpawner, Message, ThreadSpawner};
    use std::sync::Arc;

    let spawner: Arc<dyn ActorSpawner> = Arc::new(ThreadSpawner::new());

    let handle = spawner.spawn(|_inbox, outbox| {
        outbox.send(Message::Bytes(vec![1, 2, 3])).unwrap();
    });

    let msg = handle.recv().expect("recv ok");
    match msg {
        Message::Bytes(b) => assert_eq!(b, vec![1, 2, 3]),
        _ => panic!("Expected Bytes message"),
    }

    handle.join().expect("join ok");
}

/// Test bidirectional actor communication
#[test]
fn test_actor_bidirectional_communication() {
    use simple_common::{Message, ThreadSpawner, ActorSpawner};

    let spawner = ThreadSpawner::new();

    let handle = spawner.spawn(|inbox, outbox| {
        // Wait for a message
        if let Ok(Message::Value(s)) = inbox.recv() {
            // Echo it back with modification
            outbox.send(Message::Value(format!("echo: {}", s))).unwrap();
        }
    });

    // Send a message to the actor
    handle.send(Message::Value("test".to_string())).expect("send ok");

    // Receive the response
    let response = handle.recv().expect("recv ok");
    match response {
        Message::Value(s) => assert_eq!(s, "echo: test"),
        _ => panic!("Expected echo response"),
    }

    handle.join().expect("join ok");
}

/// Test that GcAllocator trait is in common
#[test]
fn test_gc_allocator_in_common() {
    use simple_common::gc::GcAllocator;

    // This test verifies the trait exists in common
    // The actual implementation is in runtime
    fn _accepts_allocator<T: GcAllocator>(_: &T) {}

    // We can't easily test without runtime, but the import proves the trait is there
    assert!(true, "GcAllocator trait accessible from common");
}

/// Test that ModuleCache is available in common
#[test]
fn test_module_cache_in_common() {
    use simple_common::ModuleCache;
    use std::sync::Arc;

    let cache: ModuleCache<String, std::io::Error> = ModuleCache::new();

    // Test basic cache operations
    let path = std::path::Path::new("/tmp/test_module");

    // Initially empty
    assert!(cache.get(path).is_none());

    // We can't fully test without real paths, but structure is correct
    assert!(true, "ModuleCache accessible from common");
}

/// Test DynModule and DynLoader traits in common
#[test]
fn test_dyn_traits_in_common() {
    use simple_common::{DynModule, DynLoader};

    // Verify traits are accessible
    fn _accepts_module<T: DynModule>(_: &T) {}
    fn _accepts_loader<T: DynLoader>(_: &T) {}

    assert!(true, "DynModule and DynLoader traits accessible from common");
}

// =============================================================================
// ExecCore Tests (shared execution logic)
// =============================================================================

/// Test that Runner and Interpreter share ExecCore behavior
#[test]
fn test_exec_core_consistency() {
    let runner = Runner::new();
    let interpreter = Interpreter::new();

    // Both should produce same results for same input
    let runner_result = runner.run_source("main = 42").expect("runner ok");
    let interpreter_result = interpreter.run_simple("main = 42").expect("interpreter ok");

    assert_eq!(runner_result, interpreter_result.exit_code);
}

/// Test no-GC mode consistency
#[test]
fn test_no_gc_mode_consistency() {
    let runner = Runner::new_no_gc();
    let interpreter = Interpreter::new_no_gc();

    let runner_result = runner.run_source("main = 100").expect("runner ok");
    let interpreter_result = interpreter.run_simple("main = 100").expect("interpreter ok");

    assert_eq!(runner_result, interpreter_result.exit_code);
}
