#![allow(unused_imports)]
//! Core tests: Edge cases, stress tests, module cache, concurrency, RunConfig
//! Tests for edge cases and stress testing

use simple_compiler::CompilerPipeline;

use simple_driver::{run_code, Interpreter, RunConfig, Runner, RunningType};
use simple_loader::ModuleLoader;
use simple_parser::{Lexer, Parser};
use std::fs;
use tempfile::tempdir;

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
    let result = runner
        .run_source("main = ((((1 + 2) * 3) - 4) + 5)")
        .expect("run ok");
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
    let source = "42 3.15 -100 0 1_000_000";
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
        assert_eq!(
            runner_result, interp_result.exit_code,
            "Consistency: {}",
            source
        );
    }
}

/// Test compile and load roundtrip
#[test]
fn test_compile_load_roundtrip() {
    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("roundtrip.smf");

    let runner = Runner::new();
    runner
        .compile_to_smf("main = 99", &smf_path)
        .expect("compile ok");

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
        assert!(
            result.is_ok(),
            "Should compile prog{}: {:?}",
            i,
            result.err()
        );
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
        handle
            .send(Message::Value(format!("msg-{}", i)))
            .expect("send ok");
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
        outbox
            .send(Message::Bytes(vec![0xDE, 0xAD, 0xBE, 0xEF]))
            .unwrap();
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

    let result =
        run_code("main = 20", &["arg1".to_string(), "arg2".to_string()], "").expect("run ok");
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
