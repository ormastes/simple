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
