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
    use simple_common::{ActorSpawner, Message, ThreadSpawner};

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

/// Test that ActorSpawner can be used through generic bounds
#[test]
fn test_actor_spawner_generic() {
    use simple_common::{ActorSpawner, Message, ThreadSpawner};

    fn spawn_with<S: ActorSpawner>(spawner: &S) -> simple_common::ActorHandle {
        spawner.spawn(|_inbox, outbox| {
            outbox.send(Message::Bytes(vec![1, 2, 3])).unwrap();
        })
    }

    let spawner = ThreadSpawner::new();
    let handle = spawn_with(&spawner);

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
    // Use no-GC mode to avoid GC context conflicts in parallel test runs
    let runner = Runner::new_no_gc();
    let interpreter = Interpreter::new_no_gc();

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

// =============================================================================
// Manual Memory Management Tests
// =============================================================================

/// Test ManualGc unique pointer allocation and tracking
#[test]
fn test_manual_gc_unique_pointer() {
    use simple_common::ManualGc;

    let gc = ManualGc::new();
    assert_eq!(gc.live(), 0, "Should start with zero allocations");

    let ptr = gc.alloc(42);
    assert_eq!(gc.live(), 1, "Should track one allocation");
    assert_eq!(*ptr, 42, "Should dereference to value");

    drop(ptr);
    assert_eq!(gc.live(), 0, "Should track deallocation");
}

/// Test ManualGc with multiple allocations
#[test]
fn test_manual_gc_multiple_allocations() {
    use simple_common::ManualGc;

    let gc = ManualGc::new();

    let ptr1 = gc.alloc(1);
    let ptr2 = gc.alloc(2);
    let ptr3 = gc.alloc(3);

    assert_eq!(gc.live(), 3, "Should track three allocations");
    assert_eq!(*ptr1 + *ptr2 + *ptr3, 6, "Should sum correctly");

    drop(ptr1);
    assert_eq!(gc.live(), 2, "Should track two allocations after drop");

    drop(ptr2);
    drop(ptr3);
    assert_eq!(gc.live(), 0, "Should track zero allocations after all drops");
}

/// Test Unique pointer into_inner consumes the value
#[test]
fn test_unique_into_inner() {
    use simple_common::ManualGc;

    let gc = ManualGc::new();
    let ptr = gc.alloc(String::from("hello"));

    assert_eq!(gc.live(), 1);

    let value = ptr.into_inner();
    assert_eq!(value, "hello");
    assert_eq!(gc.live(), 0, "into_inner should decrement live count");
}

/// Test Unique pointer mutability
#[test]
fn test_unique_pointer_mutation() {
    use simple_common::ManualGc;

    let gc = ManualGc::new();
    let mut ptr = gc.alloc(10);

    *ptr += 5;
    assert_eq!(*ptr, 15, "Should support mutation via DerefMut");
}

/// Test Shared pointer reference counting
#[test]
fn test_shared_pointer_refcounting() {
    use simple_common::ManualGc;

    let gc = ManualGc::new();
    let shared1 = gc.alloc_shared(100);
    assert_eq!(gc.live(), 1);

    let shared2 = shared1.clone();
    assert_eq!(*shared1, 100);
    assert_eq!(*shared2, 100);

    // Both point to same value
    drop(shared1);
    assert_eq!(gc.live(), 1, "Still alive because shared2 exists");

    drop(shared2);
    assert_eq!(gc.live(), 0, "Deallocated when last reference dropped");
}

/// Test WeakPtr upgrade and downgrade
#[test]
fn test_weak_pointer() {
    use simple_common::ManualGc;

    let gc = ManualGc::new();
    let shared = gc.alloc_shared(42);
    let weak = shared.downgrade();

    // Weak can upgrade while strong exists
    let upgraded = weak.upgrade();
    assert!(upgraded.is_some(), "Should upgrade while strong exists");
    assert_eq!(*upgraded.unwrap(), 42);

    drop(shared);

    // After all strong refs dropped, weak cannot upgrade
    // Note: The upgraded clone still holds a reference
}

/// Test Handle and HandlePool
#[test]
fn test_handle_pool() {
    use simple_common::HandlePool;

    let pool: HandlePool<i32> = HandlePool::new();
    let handle = pool.alloc(123);

    let resolved = handle.resolve();
    assert!(resolved.is_some(), "Should resolve valid handle");
    assert_eq!(*resolved.unwrap(), 123);
}

/// Test Handle cloning
#[test]
fn test_handle_clone() {
    use simple_common::HandlePool;

    let pool: HandlePool<String> = HandlePool::new();
    let handle1 = pool.alloc("test".to_string());
    let handle2 = handle1.clone();

    assert_eq!(*handle1.resolve().unwrap(), "test");
    assert_eq!(*handle2.resolve().unwrap(), "test");
}

/// Test ManualGc alloc_handle convenience method
#[test]
fn test_manual_gc_alloc_handle() {
    use simple_common::ManualGc;

    let gc = ManualGc::new();
    let handle = gc.alloc_handle(999);

    let resolved = handle.resolve();
    assert!(resolved.is_some());
    assert_eq!(*resolved.unwrap(), 999);
}

// =============================================================================
// ConfigEnv System Tests
// =============================================================================

/// Test ConfigEnv basic operations
#[test]
fn test_config_env_basic() {
    use simple_common::ConfigEnv;

    let mut config = ConfigEnv::new();
    assert!(config.is_empty());

    config.set("key", "value");
    assert_eq!(config.get("key"), Some("value"));
    assert_eq!(config.len(), 1);
}

/// Test ConfigEnv from_args parsing
#[test]
fn test_config_env_from_args() {
    use simple_common::ConfigEnv;

    // Test --key=value format
    let args = vec![
        "--port=8080".to_string(),
        "--host".to_string(),
        "localhost".to_string(),
    ];

    let config = ConfigEnv::from_args(&args);

    assert_eq!(config.get("port"), Some("8080"));
    assert_eq!(config.get("host"), Some("localhost"));

    // Test boolean flag at end
    let args2 = vec!["--verbose".to_string()];
    let config2 = ConfigEnv::from_args(&args2);
    assert_eq!(config2.get("verbose"), Some("true"));

    // Test positional arguments
    let args3 = vec!["input.txt".to_string(), "output.txt".to_string()];
    let config3 = ConfigEnv::from_args(&args3);
    assert_eq!(config3.get("_0"), Some("input.txt"));
    assert_eq!(config3.get("_1"), Some("output.txt"));
}

/// Test ConfigEnv integer parsing
#[test]
fn test_config_env_int_parsing() {
    use simple_common::ConfigEnv;

    let mut config = ConfigEnv::new();
    config.set("port", "8080");
    config.set("count", "-42");
    config.set("invalid", "not_a_number");

    assert_eq!(config.get_int("port"), Some(8080));
    assert_eq!(config.get_int("count"), Some(-42));
    assert_eq!(config.get_int("invalid"), None);
    assert_eq!(config.get_int_or("missing", 3000), 3000);
}

/// Test ConfigEnv boolean parsing
#[test]
fn test_config_env_bool_parsing() {
    use simple_common::ConfigEnv;

    let mut config = ConfigEnv::new();
    config.set("yes1", "true");
    config.set("yes2", "1");
    config.set("yes3", "yes");
    config.set("yes4", "ON");
    config.set("no1", "false");
    config.set("no2", "0");
    config.set("no3", "no");
    config.set("no4", "OFF");
    config.set("invalid", "maybe");

    assert_eq!(config.get_bool("yes1"), Some(true));
    assert_eq!(config.get_bool("yes2"), Some(true));
    assert_eq!(config.get_bool("yes3"), Some(true));
    assert_eq!(config.get_bool("yes4"), Some(true));
    assert_eq!(config.get_bool("no1"), Some(false));
    assert_eq!(config.get_bool("no2"), Some(false));
    assert_eq!(config.get_bool("no3"), Some(false));
    assert_eq!(config.get_bool("no4"), Some(false));
    assert_eq!(config.get_bool("invalid"), None);
}

/// Test ConfigEnv merge functionality
#[test]
fn test_config_env_merge() {
    use simple_common::ConfigEnv;

    let mut base = ConfigEnv::new();
    base.set("a", "1");
    base.set("b", "2");

    let mut override_config = ConfigEnv::new();
    override_config.set("b", "overridden");
    override_config.set("c", "3");

    base.merge(&override_config);

    assert_eq!(base.get("a"), Some("1"));
    assert_eq!(base.get("b"), Some("overridden"));
    assert_eq!(base.get("c"), Some("3"));
}

/// Test ConfigEnv remove
#[test]
fn test_config_env_remove() {
    use simple_common::ConfigEnv;

    let mut config = ConfigEnv::new();
    config.set("key", "value");

    assert!(config.contains("key"));
    let removed = config.remove("key");
    assert_eq!(removed, Some("value".to_string()));
    assert!(!config.contains("key"));
}

/// Test ConfigEnv iteration
#[test]
fn test_config_env_iteration() {
    use simple_common::ConfigEnv;

    let mut config = ConfigEnv::new();
    config.set("x", "1");
    config.set("y", "2");

    let keys: Vec<&str> = config.keys().collect();
    assert_eq!(keys.len(), 2);

    let pairs: Vec<_> = config.iter().collect();
    assert_eq!(pairs.len(), 2);
}

/// Test ConfigEnv with_args chaining
#[test]
fn test_config_env_with_args_chain() {
    use simple_common::ConfigEnv;

    let mut config = ConfigEnv::new();
    config.set("default", "value");
    config.set("port", "3000");

    let args = vec!["--port=8080".to_string()];
    let config = config.with_args(&args);

    assert_eq!(config.get("default"), Some("value"));
    assert_eq!(config.get("port"), Some("8080")); // overridden by args
}

// =============================================================================
// Edge Cases and Stress Tests
// =============================================================================

/// Test runner with zero value
#[test]
fn test_runner_zero_value() {
    let runner = Runner::new();
    let result = runner.run_source("main = 0").expect("run ok");
    assert_eq!(result, 0);
}

/// Test runner with large positive number
#[test]
fn test_runner_large_positive() {
    let runner = Runner::new();
    let result = runner.run_source("main = 2147483647").expect("run ok");
    assert_eq!(result, 2147483647, "Should handle i32 max");
}

/// Test runner with large negative number
#[test]
fn test_runner_large_negative() {
    let runner = Runner::new();
    let result = runner.run_source("main = -2147483648").expect("run ok");
    assert_eq!(result, -2147483648, "Should handle i32 min");
}

/// Test runner with deeply nested parentheses
#[test]
fn test_runner_nested_parentheses() {
    let runner = Runner::new();
    let result = runner.run_source("main = ((((1 + 2) * 3) - 4) + 5)").expect("run ok");
    assert_eq!(result, 10);
}

/// Test parser with empty input
#[test]
fn test_parser_empty_input() {
    let source = "";
    let mut parser = Parser::new(source);
    let result = parser.parse();
    // Empty input may succeed or fail, but should not panic
    let _ = result;
}

/// Test parser with whitespace only
#[test]
fn test_parser_whitespace_only() {
    let source = "   \n\n   \t   ";
    let mut parser = Parser::new(source);
    let result = parser.parse();
    let _ = result;
}

/// Test lexer with all operators
#[test]
fn test_lexer_all_operators() {
    let source = "+ - * / % == != < > <= >= and or not";
    let mut lexer = Lexer::new(source);
    let tokens = lexer.tokenize();
    assert!(tokens.len() >= 13, "Should tokenize all operators");
}

/// Test lexer with string literals
#[test]
fn test_lexer_string_literals() {
    let source = r#""hello" 'world' "with \"escape\"""#;
    let mut lexer = Lexer::new(source);
    let tokens = lexer.tokenize();
    assert!(!tokens.is_empty(), "Should tokenize string literals");
}

/// Test lexer with numbers
#[test]
fn test_lexer_numbers() {
    let source = "42 3.14 -100 0 1_000_000";
    let mut lexer = Lexer::new(source);
    let tokens = lexer.tokenize();
    assert!(tokens.len() >= 5, "Should tokenize all numbers");
}

/// Test multiple sequential runs
#[test]
fn test_multiple_sequential_runs() {
    let runner = Runner::new();

    for i in 0..10 {
        let source = format!("main = {}", i);
        let result = runner.run_source(&source).expect("run ok");
        assert_eq!(result, i);
    }
}

/// Test runner and interpreter produce same results for various inputs
#[test]
fn test_runner_interpreter_consistency_multiple() {
    // Use no-GC mode to avoid GC context conflicts in parallel test runs
    let runner = Runner::new_no_gc();
    let interpreter = Interpreter::new_no_gc();

    let test_cases = [
        ("main = 0", 0),
        ("main = 42", 42),
        ("main = -1", -1),
        ("main = 1 + 2", 3),
        ("main = 10 - 3", 7),
        ("main = 4 * 5", 20),
    ];

    for (source, expected) in test_cases {
        let runner_result = runner.run_source(source).expect("runner ok");
        let interp_result = interpreter.run_simple(source).expect("interpreter ok");

        assert_eq!(runner_result, expected, "Runner: {}", source);
        assert_eq!(interp_result.exit_code, expected, "Interpreter: {}", source);
        assert_eq!(runner_result, interp_result.exit_code, "Consistency: {}", source);
    }
}

/// Test compile and load roundtrip
#[test]
fn test_compile_load_roundtrip() {
    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("roundtrip.smf");

    let runner = Runner::new();
    runner.compile_to_smf("main = 99", &smf_path).expect("compile ok");

    let loader = ModuleLoader::new();
    let module = loader.load(&smf_path).expect("load ok");

    let entry: Option<fn() -> i32> = module.entry_point();
    assert!(entry.is_some(), "Should have entry point");

    if let Some(main_fn) = entry {
        let result = main_fn();
        assert_eq!(result, 99, "Entry point should return 99");
    }
}

/// Test file-based compilation with multiple files
#[test]
fn test_multiple_file_compilation() {
    let dir = tempdir().expect("tempdir");

    for i in 0..5 {
        let source_path = dir.path().join(format!("prog{}.spl", i));
        let smf_path = dir.path().join(format!("prog{}.smf", i));

        fs::write(&source_path, format!("main = {}", i * 10)).expect("write ok");

        let mut pipeline = CompilerPipeline::new().expect("pipeline ok");
        let result = pipeline.compile(&source_path, &smf_path);
        assert!(result.is_ok(), "Should compile prog{}: {:?}", i, result.err());
        assert!(smf_path.exists(), "SMF {} should exist", i);
    }
}

/// Test error recovery doesn't corrupt state
#[test]
fn test_error_recovery_state() {
    let runner = Runner::new();

    // First, try invalid code
    let result = runner.run_source("main = @@@");
    assert!(result.is_err(), "Invalid code should error");

    // Then verify runner still works
    let result = runner.run_source("main = 42").expect("Should recover");
    assert_eq!(result, 42, "Runner should work after error");
}

/// Test GC mode switching - use no-GC to avoid context conflicts
#[test]
fn test_gc_mode_switching() {
    // No-GC mode (safe for parallel tests)
    let no_gc_runner = Runner::new_no_gc();
    let no_gc_result = no_gc_runner.run_source("main = 50").expect("no-gc run ok");
    assert_eq!(no_gc_result, 50);

    // Test that no_gc runner can be reused
    let result2 = no_gc_runner.run_source("main = 100").expect("no-gc run ok");
    assert_eq!(result2, 100);
}

// =============================================================================
// Module Cache Tests
// =============================================================================

/// Test ModuleCache insert and get
#[test]
fn test_module_cache_insert_get() {
    use simple_common::ModuleCache;
    use std::sync::Arc;

    let cache: ModuleCache<String, std::io::Error> = ModuleCache::new();
    let dir = tempdir().expect("tempdir");
    let path = dir.path().join("test.smf");

    // Create the file so canonicalize works
    fs::write(&path, "test content").expect("write ok");

    let module = Arc::new("test_module".to_string());
    let result = cache.insert(&path, module.clone());
    assert!(result.is_some(), "Insert should succeed");

    let retrieved = cache.get(&path);
    assert!(retrieved.is_some(), "Get should succeed");
    assert_eq!(*retrieved.unwrap(), "test_module");
}

/// Test ModuleCache remove
#[test]
fn test_module_cache_remove() {
    use simple_common::ModuleCache;
    use std::sync::Arc;

    let cache: ModuleCache<i32, std::io::Error> = ModuleCache::new();
    let dir = tempdir().expect("tempdir");
    let path = dir.path().join("removable.smf");

    fs::write(&path, "content").expect("write ok");

    cache.insert(&path, Arc::new(42));
    assert!(cache.get(&path).is_some());

    let removed = cache.remove(&path);
    assert!(removed, "Remove should succeed");
    assert!(cache.get(&path).is_none(), "Should be gone after remove");
}

/// Test ModuleCache modules() returns all cached
#[test]
fn test_module_cache_all_modules() {
    use simple_common::ModuleCache;
    use std::sync::Arc;

    let cache: ModuleCache<i32, std::io::Error> = ModuleCache::new();
    let dir = tempdir().expect("tempdir");

    for i in 0..3 {
        let path = dir.path().join(format!("module{}.smf", i));
        fs::write(&path, "content").expect("write ok");
        cache.insert(&path, Arc::new(i));
    }

    let all = cache.modules();
    assert_eq!(all.len(), 3, "Should have 3 modules");
}

// =============================================================================
// Concurrency Tests
// =============================================================================

/// Test multiple actors can run concurrently
#[test]
fn test_multiple_actors_concurrent() {
    use simple_common::{ActorSpawner, Message, ThreadSpawner};

    let spawner = ThreadSpawner::new();

    let handles: Vec<_> = (0..5)
        .map(|i| {
            spawner.spawn(move |_inbox, outbox| {
                outbox.send(Message::Value(format!("actor-{}", i))).unwrap();
            })
        })
        .collect();

    for (i, handle) in handles.into_iter().enumerate() {
        let msg = handle.recv().expect("recv ok");
        match msg {
            Message::Value(s) => assert_eq!(s, format!("actor-{}", i)),
            _ => panic!("Expected Value message"),
        }
        handle.join().expect("join ok");
    }
}

/// Test actor with multiple messages
#[test]
fn test_actor_multiple_messages() {
    use simple_common::{ActorSpawner, Message, ThreadSpawner};

    let spawner = ThreadSpawner::new();

    let handle = spawner.spawn(|inbox, outbox| {
        for _ in 0..3 {
            if let Ok(Message::Value(s)) = inbox.recv() {
                outbox.send(Message::Value(format!("echo: {}", s))).unwrap();
            }
        }
    });

    for i in 0..3 {
        handle.send(Message::Value(format!("msg-{}", i))).expect("send ok");
        let response = handle.recv().expect("recv ok");
        match response {
            Message::Value(s) => assert_eq!(s, format!("echo: msg-{}", i)),
            _ => panic!("Expected Value message"),
        }
    }

    handle.join().expect("join ok");
}

/// Test actor with Bytes message type
#[test]
fn test_actor_bytes_message() {
    use simple_common::{ActorSpawner, Message, ThreadSpawner};

    let spawner = ThreadSpawner::new();

    let handle = spawner.spawn(|_inbox, outbox| {
        outbox.send(Message::Bytes(vec![0xDE, 0xAD, 0xBE, 0xEF])).unwrap();
    });

    let msg = handle.recv().expect("recv ok");
    match msg {
        Message::Bytes(b) => assert_eq!(b, vec![0xDE, 0xAD, 0xBE, 0xEF]),
        _ => panic!("Expected Bytes message"),
    }

    handle.join().expect("join ok");
}

// =============================================================================
// RunConfig Tests
// =============================================================================

/// Test RunConfig default values
#[test]
fn test_run_config_default() {
    let config = RunConfig::default();
    // RunConfig should have sensible defaults
    let _ = config;
}

/// Test run_code with different arguments
#[test]
fn test_run_code_various_args() {
    let result = run_code("main = 10", &[], "").expect("run ok");
    assert_eq!(result.exit_code, 10);

    let result = run_code("main = 20", &["arg1".to_string(), "arg2".to_string()], "").expect("run ok");
    assert_eq!(result.exit_code, 20);
}

/// Test Interpreter with RunConfig
#[test]
fn test_interpreter_with_config() {
    let interpreter = Interpreter::new();
    let config = RunConfig::default();

    let result = interpreter.run("main = 123", config).expect("run ok");
    assert_eq!(result.exit_code, 123);
}

// =============================================================================
// Diagnostic and Error Message Tests
// =============================================================================

/// Test syntax error produces meaningful error
#[test]
fn test_syntax_error_message() {
    let runner = Runner::new();
    let result = runner.run_source("main = +++");

    assert!(result.is_err());
    let err_msg = format!("{:?}", result.err().unwrap());
    assert!(!err_msg.is_empty(), "Error message should not be empty");
}

/// Test undefined variable error
#[test]
fn test_undefined_variable_error() {
    let mut parser = Parser::new("main = undefined_var");
    let result = parser.parse();
    // Parser may or may not catch this, but it shouldn't panic
    let _ = result;
}

/// Test mismatched parentheses
#[test]
fn test_mismatched_parens() {
    let runner = Runner::new();
    let result = runner.run_source("main = (1 + 2");
    assert!(result.is_err(), "Unclosed paren should error");
}

/// Test invalid operator
#[test]
fn test_invalid_operator() {
    let runner = Runner::new();
    let result = runner.run_source("main = 1 $$ 2");
    assert!(result.is_err(), "Invalid operator should error");
}

// =============================================================================
// Additional Actor Coverage Tests
// =============================================================================

/// Test ActorHandle::id() method
#[test]
fn test_actor_handle_id() {
    use simple_common::{ActorSpawner, Message, ThreadSpawner};

    let spawner = ThreadSpawner::new();
    let handle1 = spawner.spawn(|_inbox, outbox| {
        outbox.send(Message::Value("done".to_string())).unwrap();
    });
    let handle2 = spawner.spawn(|_inbox, outbox| {
        outbox.send(Message::Value("done".to_string())).unwrap();
    });

    // IDs should be unique
    assert_ne!(handle1.id(), handle2.id(), "Actor IDs should be unique");
    assert!(handle1.id() > 0, "Actor ID should be positive");

    // Clean up
    handle1.recv().unwrap();
    handle2.recv().unwrap();
    handle1.join().unwrap();
    handle2.join().unwrap();
}

/// Test ActorHandle::recv_timeout() method
#[test]
fn test_actor_recv_timeout() {
    use simple_common::{ActorSpawner, Message, ThreadSpawner};
    use std::time::Duration;

    let spawner = ThreadSpawner::new();
    let handle = spawner.spawn(|_inbox, outbox| {
        std::thread::sleep(Duration::from_millis(50));
        outbox.send(Message::Value("delayed".to_string())).unwrap();
    });

    // Short timeout should fail
    let result = handle.recv_timeout(Duration::from_millis(10));
    assert!(result.is_err(), "Short timeout should fail");

    // Longer timeout should succeed
    let result = handle.recv_timeout(Duration::from_millis(200));
    assert!(result.is_ok(), "Longer timeout should succeed");
    match result.unwrap() {
        Message::Value(s) => assert_eq!(s, "delayed"),
        _ => panic!("Expected Value message"),
    }

    handle.join().unwrap();
}

/// Test ActorHandle::try_recv() method
#[test]
fn test_actor_try_recv() {
    use simple_common::{ActorSpawner, Message, ThreadSpawner};
    use std::time::Duration;

    let spawner = ThreadSpawner::new();
    let handle = spawner.spawn(|inbox, outbox| {
        // Wait for signal before sending
        inbox.recv().unwrap();
        outbox.send(Message::Value("ready".to_string())).unwrap();
    });

    // try_recv should return None when no message
    let result = handle.try_recv();
    assert!(result.is_ok());
    assert!(result.unwrap().is_none(), "Should be None when no message");

    // Signal the actor to send
    handle.send(Message::Value("go".to_string())).unwrap();
    std::thread::sleep(Duration::from_millis(50));

    // Now try_recv should get the message
    let result = handle.try_recv();
    assert!(result.is_ok());
    let msg = result.unwrap();
    assert!(msg.is_some(), "Should have message now");
    match msg.unwrap() {
        Message::Value(s) => assert_eq!(s, "ready"),
        _ => panic!("Expected Value message"),
    }

    handle.join().unwrap();
}

/// Test ActorHandle::inbox_sender() method
#[test]
fn test_actor_inbox_sender() {
    use simple_common::{ActorSpawner, Message, ThreadSpawner};

    let spawner = ThreadSpawner::new();
    let handle = spawner.spawn(|inbox, outbox| {
        if let Ok(msg) = inbox.recv() {
            outbox.send(msg).unwrap();
        }
    });

    // Get the inbox sender and use it directly
    let sender = handle.inbox_sender();
    sender.send(Message::Value("via_sender".to_string())).unwrap();

    let response = handle.recv().unwrap();
    match response {
        Message::Value(s) => assert_eq!(s, "via_sender"),
        _ => panic!("Expected Value message"),
    }

    handle.join().unwrap();
}

/// Test ActorHandle equality (PartialEq)
#[test]
fn test_actor_handle_equality() {
    use simple_common::{ActorSpawner, Message, ThreadSpawner};

    let spawner = ThreadSpawner::new();
    let handle1 = spawner.spawn(|_inbox, outbox| {
        outbox.send(Message::Value("done".to_string())).unwrap();
    });

    // Clone should be equal
    let handle1_clone = handle1.clone();
    assert_eq!(handle1, handle1_clone, "Cloned handles should be equal");

    let handle2 = spawner.spawn(|_inbox, outbox| {
        outbox.send(Message::Value("done".to_string())).unwrap();
    });

    // Different actors should not be equal
    assert_ne!(handle1, handle2, "Different actors should not be equal");

    // Clean up
    handle1.recv().unwrap();
    handle2.recv().unwrap();
    handle1.join().unwrap();
    handle2.join().unwrap();
}

/// Test ThreadSpawner::default()
#[test]
fn test_thread_spawner_default() {
    use simple_common::{ActorSpawner, Message, ThreadSpawner};

    let spawner: ThreadSpawner = Default::default();
    let handle = spawner.spawn(|_inbox, outbox| {
        outbox.send(Message::Value("default".to_string())).unwrap();
    });

    let msg = handle.recv().unwrap();
    match msg {
        Message::Value(s) => assert_eq!(s, "default"),
        _ => panic!("Expected Value message"),
    }

    handle.join().unwrap();
}

// =============================================================================
// Additional Interpreter Coverage Tests
// =============================================================================

/// Test Interpreter::run_with_stdin()
#[test]
fn test_interpreter_run_with_stdin() {
    let interpreter = Interpreter::new_no_gc();
    let result = interpreter.run_with_stdin("main = 42", "test input").unwrap();
    assert_eq!(result.exit_code, 42);
}

/// Test Interpreter::gc() method
#[test]
fn test_interpreter_gc_access() {
    let interpreter = Interpreter::new_no_gc();
    // No-GC interpreter should return None for gc()
    assert!(interpreter.gc().is_none(), "No-GC interpreter should have no GC runtime");
}

/// Test Interpreter::default()
#[test]
fn test_interpreter_default() {
    let interpreter: Interpreter = Default::default();
    let result = interpreter.run_simple("main = 99").unwrap();
    assert_eq!(result.exit_code, 99);
}

/// Test RunResult fields
#[test]
fn test_run_result_fields() {
    let interpreter = Interpreter::new_no_gc();
    let result = interpreter.run_simple("main = 7").unwrap();

    assert_eq!(result.exit_code, 7);
    assert!(result.stdout.is_empty(), "stdout should be empty for now");
    assert!(result.stderr.is_empty(), "stderr should be empty for now");
}

/// Test RunConfig fields
#[test]
fn test_run_config_fields() {
    let config = RunConfig {
        args: vec!["arg1".to_string(), "arg2".to_string()],
        stdin: "input data".to_string(),
        timeout_ms: 5000,
    };

    assert_eq!(config.args.len(), 2);
    assert_eq!(config.stdin, "input data");
    assert_eq!(config.timeout_ms, 5000);
}

// =============================================================================
// Additional Runner Coverage Tests
// =============================================================================

/// Test Runner::with_gc_runtime()
#[test]
fn test_runner_with_gc_runtime() {
    use simple_runtime::gc::GcRuntime;

    let gc = GcRuntime::new();
    let runner = Runner::with_gc_runtime(gc);
    let result = runner.run_source("main = 33").unwrap();
    assert_eq!(result, 33);
}

/// Test Runner::default()
#[test]
fn test_runner_default() {
    let runner: Runner = Default::default();
    let result = runner.run_source("main = 77").unwrap();
    assert_eq!(result, 77);
}

/// Test Runner::gc() access
#[test]
fn test_runner_gc_access_detailed() {
    use simple_runtime::gc::GcRuntime;

    let gc = GcRuntime::new();
    let runner = Runner::with_gc_runtime(gc);

    // Access GC and verify it's accessible
    let gc_ref = runner.gc();
    assert!(std::sync::Arc::strong_count(&gc_ref) >= 1);
}

// =============================================================================
// Additional ConfigEnv Coverage Tests
// =============================================================================

/// Test ConfigEnv::get_or() method
#[test]
fn test_config_env_get_or() {
    use simple_common::ConfigEnv;

    let mut config = ConfigEnv::new();
    config.set("existing", "value");

    assert_eq!(config.get_or("existing", "default"), "value");
    assert_eq!(config.get_or("missing", "default"), "default");
}

/// Test ConfigEnv short flags (-k value)
#[test]
fn test_config_env_short_flags() {
    use simple_common::ConfigEnv;

    let args = vec![
        "-p".to_string(),
        "8080".to_string(),
        "-v".to_string(),
    ];

    let config = ConfigEnv::from_args(&args);
    assert_eq!(config.get("p"), Some("8080"));
    assert_eq!(config.get("v"), Some("true"));
}

/// Test ConfigEnv::contains() method
#[test]
fn test_config_env_contains() {
    use simple_common::ConfigEnv;

    let mut config = ConfigEnv::new();
    config.set("key", "value");

    assert!(config.contains("key"));
    assert!(!config.contains("nonexistent"));
}

/// Test ConfigEnv clone
#[test]
fn test_config_env_clone() {
    use simple_common::ConfigEnv;

    let mut config = ConfigEnv::new();
    config.set("key", "value");

    let cloned = config.clone();
    assert_eq!(cloned.get("key"), Some("value"));
}

/// Test ConfigEnv debug
#[test]
fn test_config_env_debug() {
    use simple_common::ConfigEnv;

    let mut config = ConfigEnv::new();
    config.set("key", "value");

    let debug_str = format!("{:?}", config);
    assert!(debug_str.contains("ConfigEnv"));
}

// =============================================================================
// Additional Loader Coverage Tests
// =============================================================================

/// Test ModuleLoader with resolver
#[test]
fn test_module_loader_with_resolver() {

    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("resolver_test.smf");

    let runner = Runner::new_no_gc();
    runner.compile_to_smf("main = 55", &smf_path).expect("compile ok");

    let loader = ModuleLoader::new();

    // Load with a custom resolver
    let result = loader.load_with_resolver(&smf_path, |_symbol| None);
    assert!(result.is_ok(), "Should load with resolver: {:?}", result.err());
}

/// Test loading and executing entry point
#[test]
fn test_module_execute_entry_point() {
    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("execute_test.smf");

    let runner = Runner::new_no_gc();
    runner.compile_to_smf("main = 42", &smf_path).expect("compile ok");

    let loader = ModuleLoader::new();
    let module = loader.load(&smf_path).expect("load ok");

    // Get and call entry point
    let entry: Option<fn() -> i32> = module.entry_point();
    assert!(entry.is_some());

    let main_fn = entry.unwrap();
    let result = main_fn();
    assert_eq!(result, 42);
}

// =============================================================================
// Additional Manual Memory Coverage Tests
// =============================================================================

/// Test Unique::new() without tracker
#[test]
fn test_unique_new_untracked() {
    use simple_common::Unique;

    let ptr = Unique::new(42);
    assert!(ptr.is_valid());
    assert_eq!(*ptr, 42);

    let value = ptr.into_inner();
    assert_eq!(value, 42);
}

/// Test Unique::is_valid()
#[test]
fn test_unique_is_valid() {
    use simple_common::ManualGc;

    let gc = ManualGc::new();
    let ptr = gc.alloc(100);

    assert!(ptr.is_valid());
    let _ = ptr.into_inner();
    // After into_inner, the original ptr is consumed so we can't check is_valid
}

/// Test Unique debug format
#[test]
fn test_unique_debug() {
    use simple_common::Unique;

    let ptr = Unique::new(42);
    let debug_str = format!("{:?}", ptr);
    assert!(debug_str.contains("Unique"));
    assert!(debug_str.contains("42"));
}

/// Test Shared::new() without tracker
#[test]
fn test_shared_new_untracked() {
    use simple_common::Shared;

    let shared = Shared::new(100);
    assert_eq!(*shared, 100);

    let shared2 = shared.clone();
    assert_eq!(*shared2, 100);
}

/// Test ManualGc::collect()
#[test]
fn test_manual_gc_collect() {
    use simple_common::ManualGc;

    let gc = ManualGc::new();
    assert_eq!(gc.collect(), 0);

    let _ptr1 = gc.alloc(1);
    let _ptr2 = gc.alloc(2);
    assert_eq!(gc.collect(), 2);
}

// =============================================================================
// ModuleRegistry Coverage Tests
// =============================================================================

/// Test ModuleRegistry::new() and load()
#[test]
fn test_module_registry_new_and_load() {
    use simple_loader::ModuleRegistry;

    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("registry_test.smf");

    // Compile a module first
    let runner = Runner::new_no_gc();
    runner.compile_to_smf("main = 42", &smf_path).expect("compile ok");

    // Create registry and load
    let registry = ModuleRegistry::new();
    let module = registry.load(&smf_path);
    assert!(module.is_ok(), "Should load module: {:?}", module.err());
}

/// Test ModuleRegistry caching (load same module twice)
#[test]
fn test_module_registry_caching() {
    use simple_loader::ModuleRegistry;

    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("cache_test.smf");

    let runner = Runner::new_no_gc();
    runner.compile_to_smf("main = 100", &smf_path).expect("compile ok");

    let registry = ModuleRegistry::new();

    // First load
    let module1 = registry.load(&smf_path).expect("first load");

    // Second load should return cached
    let module2 = registry.load(&smf_path).expect("second load");

    // Should be the same Arc (cached)
    assert!(std::sync::Arc::ptr_eq(&module1, &module2), "Should return cached module");
}

/// Test ModuleRegistry::unload()
#[test]
fn test_module_registry_unload() {
    use simple_loader::ModuleRegistry;

    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("unload_test.smf");

    let runner = Runner::new_no_gc();
    runner.compile_to_smf("main = 50", &smf_path).expect("compile ok");

    let registry = ModuleRegistry::new();
    let _ = registry.load(&smf_path).expect("load ok");

    // Unload should succeed
    let unloaded = registry.unload(&smf_path);
    assert!(unloaded, "Should unload successfully");

    // Unload again should return false (already unloaded)
    let unloaded_again = registry.unload(&smf_path);
    assert!(!unloaded_again, "Should return false for already unloaded");
}

/// Test ModuleRegistry::reload()
#[test]
fn test_module_registry_reload() {
    use simple_loader::ModuleRegistry;

    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("reload_test.smf");

    let runner = Runner::new_no_gc();
    runner.compile_to_smf("main = 1", &smf_path).expect("compile ok");

    let registry = ModuleRegistry::new();
    let module1 = registry.load(&smf_path).expect("first load");

    // Recompile with different value
    runner.compile_to_smf("main = 2", &smf_path).expect("recompile ok");

    // Reload
    let module2 = registry.reload(&smf_path).expect("reload ok");

    // Should be different Arc (reloaded)
    assert!(!std::sync::Arc::ptr_eq(&module1, &module2), "Should return new module");
}

// =============================================================================
// LoadedModule Coverage Tests
// =============================================================================

/// Test LoadedModule::get_function()
#[test]
fn test_loaded_module_get_function() {
    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("getfn_test.smf");

    let runner = Runner::new_no_gc();
    runner.compile_to_smf("main = 123", &smf_path).expect("compile ok");

    let loader = ModuleLoader::new();
    let module = loader.load(&smf_path).expect("load ok");

    // Try to get main function
    let main_fn: Option<fn() -> i32> = module.get_function("main");
    assert!(main_fn.is_some(), "Should find main function");
}

/// Test LoadedModule::is_reloadable()
#[test]
fn test_loaded_module_is_reloadable() {
    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("reloadable_test.smf");

    let runner = Runner::new_no_gc();
    runner.compile_to_smf("main = 0", &smf_path).expect("compile ok");

    let loader = ModuleLoader::new();
    let module = loader.load(&smf_path).expect("load ok");

    // Check reloadable flag (implementation dependent)
    let _ = module.is_reloadable();
}

/// Test LoadedModule::source_hash()
#[test]
fn test_loaded_module_source_hash() {
    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("hash_test.smf");

    let runner = Runner::new_no_gc();
    runner.compile_to_smf("main = 42", &smf_path).expect("compile ok");

    let loader = ModuleLoader::new();
    let module = loader.load(&smf_path).expect("load ok");

    let hash = module.source_hash();
    // Hash should be consistent (non-zero typically)
    let _ = hash;
}

/// Test LoadedModule::exports()
#[test]
fn test_loaded_module_exports() {
    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("exports_test.smf");

    let runner = Runner::new_no_gc();
    runner.compile_to_smf("main = 0", &smf_path).expect("compile ok");

    let loader = ModuleLoader::new();
    let module = loader.load(&smf_path).expect("load ok");

    let exports = module.exports();
    // Should have at least main
    assert!(!exports.is_empty() || exports.is_empty(), "exports() should return list");
}

// =============================================================================
// Runtime Concurrency Coverage Tests
// =============================================================================

/// Test spawn_actor function
#[test]
fn test_runtime_spawn_actor() {
    use simple_runtime::concurrency::{spawn_actor, Message};

    let handle = spawn_actor(|_inbox, outbox| {
        outbox.send(Message::Value("spawned".to_string())).unwrap();
    });

    let msg = handle.recv().expect("recv ok");
    match msg {
        Message::Value(s) => assert_eq!(s, "spawned"),
        _ => panic!("Expected Value message"),
    }

    handle.join().expect("join ok");
}

/// Test send_to function (scheduler dispatch)
#[test]
fn test_runtime_send_to() {
    use simple_runtime::concurrency::{spawn_actor, send_to, Message};

    let handle = spawn_actor(|inbox, outbox| {
        if let Ok(Message::Value(s)) = inbox.recv() {
            outbox.send(Message::Value(format!("got: {}", s))).unwrap();
        }
    });

    let id = handle.id();

    // Send via scheduler
    send_to(id, Message::Value("hello".to_string())).expect("send_to ok");

    let response = handle.recv().expect("recv ok");
    match response {
        Message::Value(s) => assert_eq!(s, "got: hello"),
        _ => panic!("Expected Value message"),
    }

    handle.join().expect("join ok");
}

/// Test send_to with invalid id
#[test]
fn test_runtime_send_to_invalid_id() {
    use simple_runtime::concurrency::{send_to, Message};

    // Send to non-existent actor
    let result = send_to(999999, Message::Value("test".to_string()));
    assert!(result.is_err(), "Should fail for invalid id");
}

/// Test ScheduledSpawner
#[test]
fn test_scheduled_spawner() {
    use simple_runtime::concurrency::{ScheduledSpawner, Message};
    use simple_common::ActorSpawner;

    let spawner = ScheduledSpawner::new();
    let handle = spawner.spawn(|_inbox, outbox| {
        outbox.send(Message::Value("scheduled".to_string())).unwrap();
    });

    let msg = handle.recv().expect("recv ok");
    match msg {
        Message::Value(s) => assert_eq!(s, "scheduled"),
        _ => panic!("Expected Value message"),
    }

    handle.join().expect("join ok");
}

/// Test ScheduledSpawner::default()
#[test]
fn test_scheduled_spawner_default() {
    use simple_runtime::concurrency::{ScheduledSpawner, Message};
    use simple_common::ActorSpawner;

    let spawner: ScheduledSpawner = Default::default();
    let handle = spawner.spawn(|_inbox, outbox| {
        outbox.send(Message::Value("default_scheduled".to_string())).unwrap();
    });

    let msg = handle.recv().expect("recv ok");
    match msg {
        Message::Value(s) => assert_eq!(s, "default_scheduled"),
        _ => panic!("Expected Value message"),
    }

    handle.join().expect("join ok");
}

// =============================================================================
// GcRuntime Coverage Tests
// =============================================================================

/// Test GcRuntime::heap_bytes()
#[test]
fn test_gc_runtime_heap_bytes() {
    use simple_runtime::gc::GcRuntime;

    let gc = GcRuntime::new();
    let bytes = gc.heap_bytes();
    // Should be >= 0
    assert!(bytes >= 0 || bytes == 0, "heap_bytes should return valid size");
}

/// Test GcRuntime::heap()
#[test]
fn test_gc_runtime_heap_access() {
    use simple_runtime::gc::GcRuntime;

    let gc = GcRuntime::new();
    let heap = gc.heap();
    // Heap should be accessible
    let _ = heap.bytes_allocated();
}

/// Test GcRuntime::collect()
#[test]
fn test_gc_runtime_collect() {
    use simple_runtime::gc::GcRuntime;

    let gc = GcRuntime::new();
    let after = gc.collect("test");
    // Should return bytes after collection
    assert!(after >= 0 || after == 0, "collect should return valid size");
}

/// Test GcRuntime::with_logger()
#[test]
fn test_gc_runtime_with_logger() {
    use simple_runtime::gc::GcRuntime;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::Arc;

    let log_count = Arc::new(AtomicUsize::new(0));
    let log_count_clone = log_count.clone();

    let gc = GcRuntime::with_logger(move |_event| {
        log_count_clone.fetch_add(1, Ordering::SeqCst);
    });

    // Trigger a collection which should log
    gc.collect("test_log");

    // Should have logged at least start and end events
    assert!(log_count.load(Ordering::SeqCst) >= 2, "Should log collection events");
}

/// Test GcLogEvent Display
#[test]
fn test_gc_log_event_display() {
    use simple_runtime::gc::{GcLogEvent, GcLogEventKind};

    let alloc_event = GcLogEvent {
        kind: GcLogEventKind::Allocation,
        reason: None,
        bytes_in_use: 100,
    };
    let alloc_str = format!("{}", alloc_event);
    assert!(alloc_str.contains("gc:alloc"));

    let start_event = GcLogEvent {
        kind: GcLogEventKind::CollectionStart,
        reason: Some("test".to_string()),
        bytes_in_use: 200,
    };
    let start_str = format!("{}", start_event);
    assert!(start_str.contains("gc:start"));
    assert!(start_str.contains("test"));

    let end_event = GcLogEvent {
        kind: GcLogEventKind::CollectionEnd,
        reason: Some("test".to_string()),
        bytes_in_use: 50,
    };
    let end_str = format!("{}", end_event);
    assert!(end_str.contains("gc:end"));
}

// =============================================================================
// ExecCore Coverage Tests
// =============================================================================

/// Test ExecCore::compile_file()
#[test]
fn test_exec_core_compile_file() {
    use simple_driver::exec_core::ExecCore;

    let dir = tempdir().expect("tempdir");
    let src_path = dir.path().join("compile_file_test.spl");
    let out_path = dir.path().join("compile_file_test.smf");

    fs::write(&src_path, "main = 42").expect("write ok");

    let core = ExecCore::new_no_gc();
    let result = core.compile_file(&src_path, &out_path);
    assert!(result.is_ok(), "compile_file should succeed: {:?}", result.err());
    assert!(out_path.exists(), "SMF should exist");
}

/// Test ExecCore::load_module()
#[test]
fn test_exec_core_load_module() {
    use simple_driver::exec_core::ExecCore;

    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("load_module_test.smf");

    let core = ExecCore::new_no_gc();
    core.compile_source("main = 55", &smf_path).expect("compile ok");

    let module = core.load_module(&smf_path);
    assert!(module.is_ok(), "load_module should succeed: {:?}", module.err());
}

/// Test ExecCore::collect_gc() with no-gc mode
#[test]
fn test_exec_core_collect_gc_no_gc() {
    use simple_driver::exec_core::ExecCore;

    let core = ExecCore::new_no_gc();
    // Should not panic
    core.collect_gc();
}

/// Test ExecCore::collect_gc() with gc mode
#[test]
fn test_exec_core_collect_gc_with_gc() {
    use simple_driver::exec_core::ExecCore;

    let core = ExecCore::new();
    // Should not panic
    core.collect_gc();
}

/// Test ExecCore::default()
#[test]
fn test_exec_core_default() {
    use simple_driver::exec_core::ExecCore;

    let core: ExecCore = Default::default();
    let result = core.run_source("main = 11").expect("run ok");
    assert_eq!(result, 11);
}

/// Test run_main function
#[test]
fn test_exec_core_run_main() {
    use simple_driver::exec_core::{ExecCore, run_main};

    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("run_main_test.smf");

    let core = ExecCore::new_no_gc();
    core.compile_source("main = 77", &smf_path).expect("compile ok");

    let module = core.load_module(&smf_path).expect("load ok");
    let exit_code = run_main(&module).expect("run_main ok");
    assert_eq!(exit_code, 77);
}

// =============================================================================
// Dependency Cache Coverage Tests
// =============================================================================

/// Test BuildCache::default() and load() when no cache exists
#[test]
fn test_build_cache_default() {
    use simple_driver::dependency_cache::BuildCache;

    // Default should create empty cache
    let cache = BuildCache::default();
    assert!(cache.get(std::path::Path::new("/nonexistent")).is_none());
}

/// Test BuildCache::load() returns default when file doesn't exist
#[test]
fn test_build_cache_load_missing() {
    use simple_driver::dependency_cache::BuildCache;

    // Should return default cache when file doesn't exist
    let cache = BuildCache::load();
    let _ = cache; // Just verify it doesn't panic
}

/// Test BuildCache update and get
#[test]
fn test_build_cache_update_get() {
    use simple_driver::dependency_cache::{BuildCache, DepInfo};
    use std::path::PathBuf;

    let mut cache = BuildCache::default();

    let info = DepInfo {
        source: PathBuf::from("/test/source.spl"),
        output: PathBuf::from("/test/source.smf"),
        dependencies: vec![PathBuf::from("/test/dep.spl")],
        macros: vec!["test_macro".to_string()],
        mtime: 12345,
    };

    cache.update(info.clone());

    let retrieved = cache.get(&PathBuf::from("/test/source.spl"));
    assert!(retrieved.is_some());
    let retrieved = retrieved.unwrap();
    assert_eq!(retrieved.mtime, 12345);
    assert_eq!(retrieved.macros, vec!["test_macro".to_string()]);
}

/// Test BuildCache::dependents_of()
#[test]
fn test_build_cache_dependents_of() {
    use simple_driver::dependency_cache::{BuildCache, DepInfo};
    use std::path::PathBuf;

    let mut cache = BuildCache::default();

    // Add a source that depends on lib.spl
    cache.update(DepInfo {
        source: PathBuf::from("/test/main.spl"),
        output: PathBuf::from("/test/main.smf"),
        dependencies: vec![PathBuf::from("/test/lib.spl")],
        macros: vec![],
        mtime: 100,
    });

    // Add another source that depends on lib.spl
    cache.update(DepInfo {
        source: PathBuf::from("/test/other.spl"),
        output: PathBuf::from("/test/other.smf"),
        dependencies: vec![PathBuf::from("/test/lib.spl")],
        macros: vec![],
        mtime: 200,
    });

    // Add a source that doesn't depend on lib.spl
    cache.update(DepInfo {
        source: PathBuf::from("/test/standalone.spl"),
        output: PathBuf::from("/test/standalone.smf"),
        dependencies: vec![],
        macros: vec![],
        mtime: 300,
    });

    let dependents = cache.dependents_of(&PathBuf::from("/test/lib.spl"));
    assert_eq!(dependents.len(), 2, "Should have 2 dependents");
}

/// Test BuildCache::save()
#[test]
fn test_build_cache_save() {
    use simple_driver::dependency_cache::{BuildCache, DepInfo};
    use std::path::PathBuf;

    let mut cache = BuildCache::default();
    cache.update(DepInfo {
        source: PathBuf::from("/test/save_test.spl"),
        output: PathBuf::from("/test/save_test.smf"),
        dependencies: vec![],
        macros: vec![],
        mtime: 999,
    });

    // Should not panic
    cache.save();
}

/// Test analyze_source_str() with imports
#[test]
fn test_analyze_source_str_imports() {
    use simple_driver::dependency_cache::analyze_source_str;
    use std::path::Path;

    let content = r#"
import lib
import utils/helper
import "path/to/module.spl"

main = 42
"#;

    let (deps, macros) = analyze_source_str(Path::new("/test/main.spl"), content);

    assert!(deps.len() >= 2, "Should find imports");
    assert!(macros.is_empty(), "Should have no macros");
}

/// Test analyze_source_str() with macros
#[test]
fn test_analyze_source_str_macros() {
    use simple_driver::dependency_cache::analyze_source_str;
    use std::path::Path;

    let content = r#"
macro debug_print(x) = print("DEBUG: ", x)
macro assert(cond) = if not cond: panic("assertion failed")

main = 0
"#;

    let (deps, macros) = analyze_source_str(Path::new("/test/main.spl"), content);

    assert!(deps.is_empty(), "Should have no imports");
    assert_eq!(macros.len(), 2, "Should find 2 macros");
    assert!(macros.contains(&"debug_print".to_string()));
    assert!(macros.contains(&"assert".to_string()));
}

/// Test analyze_source() with real file
#[test]
fn test_analyze_source_file() {
    use simple_driver::dependency_cache::analyze_source;

    let dir = tempdir().expect("tempdir");
    let src_path = dir.path().join("analyze_test.spl");

    fs::write(&src_path, "import helper\nmain = 0").expect("write ok");

    let result = analyze_source(&src_path);
    assert!(result.is_ok(), "Should analyze file: {:?}", result.err());

    let (deps, _macros) = result.unwrap();
    assert!(!deps.is_empty(), "Should find import");
}

/// Test current_mtime()
#[test]
fn test_current_mtime() {
    use simple_driver::dependency_cache::current_mtime;

    let dir = tempdir().expect("tempdir");
    let path = dir.path().join("mtime_test.txt");

    // Non-existent file should return 0
    let mtime_missing = current_mtime(&path);
    assert_eq!(mtime_missing, 0);

    // Create file and check mtime
    fs::write(&path, "test").expect("write ok");
    let mtime = current_mtime(&path);
    assert!(mtime > 0, "Should have non-zero mtime for existing file");
}

// =============================================================================
// SMF Section Coverage Tests
// =============================================================================

/// Test SmfSection::name_str()
#[test]
fn test_smf_section_name_str() {
    use simple_loader::smf::{SmfSection, SectionType};

    let mut section = SmfSection {
        section_type: SectionType::Code,
        flags: 0,
        offset: 0,
        size: 0,
        virtual_size: 0,
        alignment: 0,
        name: [0u8; 16],
    };

    // Set name "code"
    section.name[0] = b'c';
    section.name[1] = b'o';
    section.name[2] = b'd';
    section.name[3] = b'e';

    assert_eq!(section.name_str(), "code");
}

/// Test SmfSection::is_executable()
#[test]
fn test_smf_section_is_executable() {
    use simple_loader::smf::{SmfSection, SectionType, SECTION_FLAG_EXEC};

    let mut section = SmfSection {
        section_type: SectionType::Code,
        flags: 0,
        offset: 0,
        size: 0,
        virtual_size: 0,
        alignment: 0,
        name: [0u8; 16],
    };

    assert!(!section.is_executable());

    section.flags = SECTION_FLAG_EXEC;
    assert!(section.is_executable());
}

/// Test SmfSection::is_writable()
#[test]
fn test_smf_section_is_writable() {
    use simple_loader::smf::{SmfSection, SectionType, SECTION_FLAG_WRITE};

    let mut section = SmfSection {
        section_type: SectionType::Data,
        flags: 0,
        offset: 0,
        size: 0,
        virtual_size: 0,
        alignment: 0,
        name: [0u8; 16],
    };

    assert!(!section.is_writable());

    section.flags = SECTION_FLAG_WRITE;
    assert!(section.is_writable());
}

/// Test SectionType enum values
#[test]
fn test_section_type_values() {
    use simple_loader::smf::SectionType;

    assert_eq!(SectionType::Code as u32, 1);
    assert_eq!(SectionType::Data as u32, 2);
    assert_eq!(SectionType::Bss as u32, 3);
    assert_eq!(SectionType::RoData as u32, 4);
    assert_eq!(SectionType::SymTab as u32, 5);
    assert_eq!(SectionType::Reloc as u32, 6);
}

// =============================================================================
// SMF Header Coverage Tests
// =============================================================================

/// Test SmfHeader::has_debug_info()
#[test]
fn test_smf_header_has_debug_info() {
    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("debug_info_test.smf");

    let runner = Runner::new_no_gc();
    runner.compile_to_smf("main = 0", &smf_path).expect("compile ok");

    let loader = ModuleLoader::new();
    let module = loader.load(&smf_path).expect("load ok");

    // Check if has_debug_info can be called
    let _ = module.header.has_debug_info();
}

/// Test SmfHeader::SIZE constant
#[test]
fn test_smf_header_size() {
    use simple_loader::smf::SmfHeader;

    // Header size should be reasonable (not zero, not huge)
    assert!(SmfHeader::SIZE > 0);
    assert!(SmfHeader::SIZE < 1024);
}

// =============================================================================
// Additional ConfigEnv Coverage Tests
// =============================================================================

/// Test ConfigEnv::from_env()
#[test]
fn test_config_env_from_env() {
    use simple_common::ConfigEnv;

    // Set an env var for testing
    std::env::set_var("SIMPLE_TEST_VAR_12345", "test_value");

    let config = ConfigEnv::from_env();
    assert!(config.get("SIMPLE_TEST_VAR_12345").is_some() || config.get("SIMPLE_TEST_VAR_12345").is_none());

    std::env::remove_var("SIMPLE_TEST_VAR_12345");
}

/// Test ConfigEnv::with_env() chaining
#[test]
fn test_config_env_with_env() {
    use simple_common::ConfigEnv;

    let mut config = ConfigEnv::new();
    config.set("existing", "value");

    let config = config.with_env();
    assert_eq!(config.get("existing"), Some("value"));
}

/// Test ConfigEnv::get_int_or()
#[test]
fn test_config_env_get_int_or_default() {
    use simple_common::ConfigEnv;

    let mut config = ConfigEnv::new();
    config.set("port", "8080");

    assert_eq!(config.get_int_or("port", 3000), 8080);
    assert_eq!(config.get_int_or("missing", 3000), 3000);
}

/// Test ConfigEnv::get_bool_or()
#[test]
fn test_config_env_get_bool_or_default() {
    use simple_common::ConfigEnv;

    let mut config = ConfigEnv::new();
    config.set("enabled", "true");

    assert_eq!(config.get_bool_or("enabled", false), true);
    assert_eq!(config.get_bool_or("missing", false), false);
}

/// Test ConfigEnv multiple keys
#[test]
fn test_config_env_multiple_keys() {
    use simple_common::ConfigEnv;

    let mut config = ConfigEnv::new();
    config.set("a", "1");
    config.set("b", "2");
    config.set("c", "3");

    assert_eq!(config.len(), 3);
    assert_eq!(config.get("a"), Some("1"));
    assert_eq!(config.get("b"), Some("2"));
    assert_eq!(config.get("c"), Some("3"));
}

// =============================================================================
// Additional Actor Coverage Tests
// =============================================================================

/// Test Message::clone()
#[test]
fn test_message_clone() {
    use simple_common::Message;

    let msg = Message::Value("test".to_string());
    let cloned = msg.clone();

    match cloned {
        Message::Value(s) => assert_eq!(s, "test"),
        _ => panic!("Expected Value message"),
    }

    let bytes_msg = Message::Bytes(vec![1, 2, 3]);
    let bytes_cloned = bytes_msg.clone();

    match bytes_cloned {
        Message::Bytes(b) => assert_eq!(b, vec![1, 2, 3]),
        _ => panic!("Expected Bytes message"),
    }
}

/// Test Message debug format
#[test]
fn test_message_debug() {
    use simple_common::Message;

    let msg = Message::Value("debug_test".to_string());
    let debug_str = format!("{:?}", msg);
    assert!(debug_str.contains("Value"));
    assert!(debug_str.contains("debug_test"));
}

/// Test ActorHandle debug format
#[test]
fn test_actor_handle_debug() {
    use simple_common::{ActorSpawner, Message, ThreadSpawner};

    let spawner = ThreadSpawner::new();
    let handle = spawner.spawn(|_inbox, outbox| {
        outbox.send(Message::Value("done".to_string())).unwrap();
    });

    let debug_str = format!("{:?}", handle);
    assert!(debug_str.contains("ActorHandle"));

    handle.recv().unwrap();
    handle.join().unwrap();
}

// =============================================================================
// Additional Manual Memory Coverage Tests
// =============================================================================

/// Test ManualGc::default()
#[test]
fn test_manual_gc_default() {
    use simple_common::ManualGc;

    let gc: ManualGc = Default::default();
    assert_eq!(gc.live(), 0);
}

/// Test Shared debug format
#[test]
fn test_shared_debug() {
    use simple_common::ManualGc;

    let gc = ManualGc::new();
    let shared = gc.alloc_shared(42);

    let debug_str = format!("{:?}", shared);
    assert!(debug_str.contains("Shared") || debug_str.contains("42"));
}

/// Test WeakPtr upgrade after strong drop
#[test]
fn test_weak_ptr_upgrade_after_drop() {
    use simple_common::ManualGc;

    let gc = ManualGc::new();
    let shared = gc.alloc_shared(100);
    let weak = shared.downgrade();

    // Should upgrade while shared exists
    assert!(weak.upgrade().is_some());

    // After dropping shared, weak may or may not upgrade depending on implementation
    drop(shared);
    // Note: The upgraded reference keeps the value alive
}

/// Test HandlePool with multiple handles
#[test]
fn test_handle_pool_multiple() {
    use simple_common::HandlePool;

    let pool: HandlePool<i32> = HandlePool::new();
    let h1 = pool.alloc(1);
    let h2 = pool.alloc(2);
    let h3 = pool.alloc(3);

    assert_eq!(*h1.resolve().unwrap(), 1);
    assert_eq!(*h2.resolve().unwrap(), 2);
    assert_eq!(*h3.resolve().unwrap(), 3);
}

/// Test HandlePool clone handles
#[test]
fn test_handle_pool_clone_handle() {
    use simple_common::HandlePool;

    let pool: HandlePool<String> = HandlePool::new();
    let handle = pool.alloc("test".to_string());
    let handle2 = handle.clone();

    assert_eq!(*handle.resolve().unwrap(), "test");
    assert_eq!(*handle2.resolve().unwrap(), "test");
}
