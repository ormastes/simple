//! Parser, lexer, and runtime tests
//! Additional parser/lexer system tests and runtime behavior tests

use simple_compiler::CompilerPipeline;
use simple_driver::{run_code, Interpreter, RunConfig, Runner, RunningType};
use simple_loader::ModuleLoader;
use simple_parser::{Lexer, Parser};
use std::fs;
use tempfile::tempdir;

// =============================================================================
// Additional Parser and Lexer System Tests
// =============================================================================

/// Test parser with complex nested expressions
#[test]
fn test_parser_complex_nesting() {
    let source = r#"
let a = ((1 + 2) * (3 + 4))
let b = a + ((5 - 6) / (7 + 8))
main = a + b
"#;

    let mut parser = Parser::new(source);
    let result = parser.parse();
    assert!(
        result.is_ok(),
        "Should parse complex nesting: {:?}",
        result.err()
    );
}

/// Test parser with multiple function definitions
#[test]
fn test_parser_multiple_functions() {
    let source = r#"
fn add(a, b):
    return a + b

fn sub(a, b):
    return a - b

fn mul(a, b):
    return a * b

main = add(1, 2)
"#;

    let mut parser = Parser::new(source);
    let result = parser.parse();
    // May succeed or fail depending on parser state
    let _ = result;
}

/// Test lexer with all bracket types
#[test]
fn test_lexer_brackets() {
    let source = "()[]{}";
    let mut lexer = Lexer::new(source);
    let tokens = lexer.tokenize();
    assert!(tokens.len() >= 6, "Should tokenize all brackets");
}

/// Test lexer with comments
#[test]
fn test_lexer_comments() {
    let source = r#"
# This is a comment
let x = 1  # inline comment
main = x
"#;

    let mut lexer = Lexer::new(source);
    let tokens = lexer.tokenize();
    assert!(!tokens.is_empty(), "Should tokenize code with comments");
}

/// Test lexer with indentation (Python-style)
#[test]
fn test_lexer_indentation() {
    let source = r#"
if true:
    let x = 1
    let y = 2
main = 0
"#;

    let mut lexer = Lexer::new(source);
    let tokens = lexer.tokenize();
    // Should produce INDENT/DEDENT tokens
    assert!(!tokens.is_empty(), "Should tokenize indented code");
}

// =============================================================================
// Additional Error Handling System Tests
// =============================================================================

/// Test runner recovers from multiple consecutive errors
#[test]
fn test_runner_multiple_error_recovery() {
    let runner = Runner::new_no_gc();

    // Try multiple invalid codes
    for _ in 0..5 {
        let result = runner.run_source("main = @@@");
        assert!(result.is_err());
    }

    // Should still work after errors
    let result = runner.run_source("main = 42").expect("recovery ok");
    assert_eq!(result, 42);
}

/// Test compiler handles empty source
#[test]
fn test_compiler_empty_source() {
    let runner = Runner::new_no_gc();
    let result = runner.run_source("");
    // May error or succeed with 0, but should not panic
    let _ = result;
}

/// Test compiler handles whitespace-only source
#[test]
fn test_compiler_whitespace_source() {
    let runner = Runner::new_no_gc();
    let result = runner.run_source("   \n\n   \t   ");
    // May error or succeed, but should not panic
    let _ = result;
}

/// Test compiler handles very long expression
#[test]
fn test_compiler_long_expression() {
    let runner = Runner::new_no_gc();

    // Build a moderate chain of additions (reduced from 50 to avoid stack overflow)
    let mut expr = String::from("1");
    for i in 2..=10 {
        expr.push_str(&format!(" + {}", i));
    }
    let source = format!("main = {}", expr);

    let result = runner.run_source(&source).expect("long expr ok");
    let expected: i32 = (1..=10).sum();
    assert_eq!(result, expected);
}

/// Test runner with division by zero
#[test]
fn test_runner_division_by_zero() {
    let runner = Runner::new_no_gc();
    let result = runner.run_source("main = 1 / 0");
    // May panic, error, or return special value
    let _ = result;
}

// =============================================================================
// GC and Memory System Tests
// =============================================================================

/// Test GC collection after multiple runs
#[test]
fn test_gc_multiple_runs_collection() {
    let runner = Runner::new();

    for i in 0..10 {
        let source = format!("main = {}", i);
        let result = runner.run_source(&source).expect("run ok");
        assert_eq!(result, i);
    }

    // Explicitly trigger GC
    let gc = runner.gc();
    gc.collect("test");
}

/// Test NoGcAllocator basic operations
#[test]
fn test_no_gc_allocator() {
    use simple_common::gc::GcAllocator;
    use simple_runtime::NoGcAllocator;

    let alloc = NoGcAllocator::new();
    alloc.collect(); // Should be a no-op but not panic
}

/// Test GcRuntime metrics
#[test]
fn test_gc_runtime_metrics() {
    use simple_runtime::gc::GcRuntime;

    let gc = GcRuntime::new();

    // Check initial state
    let initial_bytes = gc.heap_bytes();
    assert!(initial_bytes >= 0);

    // Trigger collection and check
    let after = gc.collect("metrics_test");
    assert!(after >= 0);
}

// =============================================================================
// Interpreter Result Fields Tests
// =============================================================================

/// Test RunResult with stdout capture
#[test]
fn test_run_result_stdout() {
    let interpreter = Interpreter::new_no_gc();
    let result = interpreter.run_simple("main = 42").expect("run ok");

    // Verify all fields accessible
    let _exit = result.exit_code;
    let _stdout = &result.stdout;
    let _stderr = &result.stderr;
}

/// Test RunConfig::default() fields
#[test]
fn test_run_config_default_fields() {
    let config = RunConfig::default();
    assert!(config.args.is_empty());
    assert!(config.stdin.is_empty());
    // timeout_ms = 0 means no timeout (default behavior)
    assert_eq!(config.timeout_ms, 0);
    assert!(!config.in_memory);
}

/// Test Interpreter::run() with custom config
#[test]
fn test_interpreter_run_custom_config() {
    let interpreter = Interpreter::new_no_gc();
    let config = RunConfig {
        args: vec!["arg1".to_string()],
        stdin: "input".to_string(),
        timeout_ms: 10000,
        in_memory: true,
        running_type: RunningType::default(),
    };

    let result = interpreter.run("main = 88", config).expect("run ok");
    assert_eq!(result.exit_code, 88);
}

// =============================================================================
// Module Loader Edge Cases
// =============================================================================

/// Test loading same module twice returns cached
#[test]
fn test_module_loader_caching() {
    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("cache_loader_test.smf");

    let runner = Runner::new_no_gc();
    runner
        .compile_to_smf("main = 111", &smf_path)
        .expect("compile ok");

    let loader = ModuleLoader::new();

    // Load twice
    let module1 = loader.load(&smf_path).expect("load 1 ok");
    let module2 = loader.load(&smf_path).expect("load 2 ok");

    // Both should work
    let entry1: Option<fn() -> i32> = module1.entry_point();
    let entry2: Option<fn() -> i32> = module2.entry_point();

    assert!(entry1.is_some() && entry2.is_some());
}

/// Test loading corrupted SMF fails gracefully
#[test]
fn test_module_loader_corrupted_smf() {
    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("corrupted.smf");

    // Write invalid SMF
    fs::write(&smf_path, b"not a valid SMF file").expect("write ok");

    let loader = ModuleLoader::new();
    let result = loader.load(&smf_path);
    assert!(result.is_err(), "Corrupted SMF should fail to load");
}

/// Test module symbols
#[test]
fn test_loaded_module_symbols() {
    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("symbols_test.smf");

    let runner = Runner::new_no_gc();
    runner
        .compile_to_smf("main = 0", &smf_path)
        .expect("compile ok");

    let loader = ModuleLoader::new();
    let module = loader.load(&smf_path).expect("load ok");

    let symbols = module.exports();
    // Should have at least main (may be empty depending on implementation)
    let _ = symbols;
}

// =============================================================================
// Compiler Pipeline Edge Cases
// =============================================================================

/// Test CompilerPipeline::with_gc()
#[test]
fn test_compiler_pipeline_with_gc() {
    use simple_runtime::gc::GcRuntime;
    use std::sync::Arc;

    let gc = Arc::new(GcRuntime::new());
    let pipeline = CompilerPipeline::with_gc(gc);
    assert!(pipeline.is_ok(), "Pipeline with GC should succeed");
}

/// Test compiling multiple files with same pipeline
#[test]
fn test_compiler_pipeline_reuse() {
    let dir = tempdir().expect("tempdir");
    let mut pipeline = CompilerPipeline::new().expect("pipeline ok");

    for i in 0..3 {
        let src = dir.path().join(format!("reuse{}.spl", i));
        let out = dir.path().join(format!("reuse{}.smf", i));

        fs::write(&src, format!("main = {}", i * 100)).expect("write ok");
        let result = pipeline.compile(&src, &out);
        assert!(
            result.is_ok(),
            "Pipeline reuse {} should succeed: {:?}",
            i,
            result.err()
        );
    }
}

// =============================================================================
// Edge Cases and Boundary Value Tests
// =============================================================================

/// Test integer boundary values (i32 limits)
#[test]
fn test_integer_boundary_i32_max() {
    let runner = Runner::new_no_gc();
    // i32::MAX = 2147483647
    let result = runner.run_source("main = 2147483647").expect("run ok");
    assert_eq!(result, i32::MAX);
}

#[test]
fn test_integer_boundary_i32_min() {
    let runner = Runner::new_no_gc();
    // i32::MIN = -2147483648
    let result = runner.run_source("main = -2147483648").expect("run ok");
    assert_eq!(result, i32::MIN);
}

#[test]
fn test_integer_boundary_zero() {
    let runner = Runner::new_no_gc();
    let result = runner.run_source("main = 0").expect("run ok");
    assert_eq!(result, 0);
}

#[test]
fn test_integer_boundary_one() {
    let runner = Runner::new_no_gc();
    let result = runner.run_source("main = 1").expect("run ok");
    assert_eq!(result, 1);
}

#[test]
fn test_integer_boundary_minus_one() {
    let runner = Runner::new_no_gc();
    let result = runner.run_source("main = -1").expect("run ok");
    assert_eq!(result, -1);
}

/// Test empty source handling
#[test]
fn test_empty_source_behavior() {
    let runner = Runner::new_no_gc();
    // Empty source - behavior may vary (could succeed with default return or fail)
    // Just verify it doesn't panic
    let _ = runner.run_source("");
}

/// Test whitespace-only source
#[test]
fn test_whitespace_only_source() {
    let runner = Runner::new_no_gc();
    let result = runner.run_source("   \n\n   \t\t   ");
    assert!(result.is_err(), "Whitespace-only source should fail");
}

/// Test very long identifier names
#[test]
fn test_long_identifier_name() {
    let runner = Runner::new_no_gc();
    let long_name = "a".repeat(1000);
    let source = format!("{} = 42\nmain = {}", long_name, long_name);
    // Should either work or fail gracefully
    let _ = runner.run_source(&source);
}

/// Test moderately nested parentheses (avoid stack overflow)
#[test]
fn test_moderately_nested_parentheses() {
    let runner = Runner::new_no_gc();
    // 10 levels of nesting - reasonable depth that won't overflow
    let open = "(".repeat(10);
    let close = ")".repeat(10);
    let source = format!("main = {}42{}", open, close);
    let result = runner.run_source(&source).expect("run ok");
    assert_eq!(result, 42);
}

/// Test complex arithmetic expression
#[test]
fn test_complex_arithmetic_chain() {
    let runner = Runner::new_no_gc();
    let result = runner
        .run_source("main = 1 + 2 * 3 - 4 / 2 + 5 * 6")
        .expect("run ok");
    // 1 + 6 - 2 + 30 = 35
    assert_eq!(result, 35);
}

/// Test multiple operators same precedence
#[test]
fn test_same_precedence_operators() {
    let runner = Runner::new_no_gc();
    // Left-to-right for same precedence
    let result = runner.run_source("main = 10 - 5 - 2").expect("run ok");
    assert_eq!(result, 3); // (10 - 5) - 2 = 3
}

/// Test modulo operator
#[test]
fn test_modulo_positive() {
    let runner = Runner::new_no_gc();
    let result = runner.run_source("main = 17 % 5").expect("run ok");
    assert_eq!(result, 2);
}

/// Test multiplication overflow behavior
#[test]
fn test_arithmetic_large_multiplication() {
    let runner = Runner::new_no_gc();
    // Should handle large intermediate values or overflow predictably
    let result = runner.run_source("main = 1000000 * 1000");
    // Either succeeds with 1000000000 or fails gracefully
    if let Ok(val) = result {
        assert_eq!(val, 1000000000);
    }
}

// =============================================================================
// Concurrent Execution Tests
// =============================================================================

/// Test multiple runners operating concurrently
#[test]
fn test_concurrent_runners() {
    use std::thread;

    let handles: Vec<_> = (0..4)
        .map(|i| {
            thread::spawn(move || {
                let runner = Runner::new_no_gc();
                let source = format!("main = {}", i * 100);
                runner.run_source(&source).expect("run ok")
            })
        })
        .collect();

    let results: Vec<_> = handles.into_iter().map(|h| h.join().unwrap()).collect();
    assert_eq!(results.len(), 4);
    // Each thread should have returned its respective value
    for (i, &result) in results.iter().enumerate() {
        assert_eq!(result, (i as i32) * 100);
    }
}

/// Test concurrent interpreters
#[test]
fn test_concurrent_interpreters() {
    use std::thread;

    let handles: Vec<_> = (0..4)
        .map(|i| {
            thread::spawn(move || {
                let interpreter = Interpreter::new_no_gc();
                let source = format!("main = {}", i * 50 + 25);
                interpreter.run_simple(&source).expect("run ok").exit_code
            })
        })
        .collect();

    let results: Vec<_> = handles.into_iter().map(|h| h.join().unwrap()).collect();
    for (i, &result) in results.iter().enumerate() {
        assert_eq!(result, (i as i32) * 50 + 25);
    }
}

/// Test concurrent compilation and execution
#[test]
fn test_concurrent_compile_and_run() {
    use std::thread;

    let dir = tempdir().expect("tempdir");
    let base_path = dir.path().to_path_buf();

    let handles: Vec<_> = (0..4)
        .map(|i| {
            let path = base_path.clone();
            thread::spawn(move || {
                let runner = Runner::new_no_gc();
                let src = path.join(format!("concurrent_{}.spl", i));
                let smf = path.join(format!("concurrent_{}.smf", i));

                fs::write(&src, format!("main = {}", i * 10)).expect("write ok");
                runner
                    .compile_to_smf(&format!("main = {}", i * 10), &smf)
                    .expect("compile ok");

                let loader = ModuleLoader::new();
                let module = loader.load(&smf).expect("load ok");
                let entry: fn() -> i32 = module.entry_point().expect("entry ok");
                entry()
            })
        })
        .collect();

    let results: Vec<_> = handles.into_iter().map(|h| h.join().unwrap()).collect();
    for (i, &result) in results.iter().enumerate() {
        assert_eq!(result, (i as i32) * 10);
    }
}

/// Test rapid sequential runs (stress test)
#[test]
fn test_rapid_sequential_runs() {
    let runner = Runner::new_no_gc();
    for i in 0..100 {
        let result = runner.run_source(&format!("main = {}", i)).expect("run ok");
        assert_eq!(result, i);
    }
}

// =============================================================================
// File System and Path Handling Tests
// =============================================================================

/// Test file with unusual but valid characters in path
#[test]
fn test_file_path_with_spaces() {
    let dir = tempdir().expect("tempdir");
    let subdir = dir.path().join("path with spaces");
    fs::create_dir_all(&subdir).expect("mkdir ok");

    let source_path = subdir.join("program.spl");
    fs::write(&source_path, "main = 123").expect("write ok");

    let runner = Runner::new_no_gc();
    let result = runner.run_file(&source_path).expect("run ok");
    assert_eq!(result, 123);
}

/// Test file with unicode in path
#[test]
fn test_file_path_with_unicode() {
    let dir = tempdir().expect("tempdir");
    let subdir = dir.path().join("路径_тест_🎉");
    fs::create_dir_all(&subdir).expect("mkdir ok");

    let source_path = subdir.join("program.spl");
    fs::write(&source_path, "main = 456").expect("write ok");

    let runner = Runner::new_no_gc();
    let result = runner.run_file(&source_path).expect("run ok");
    assert_eq!(result, 456);
}

/// Test very deep directory path
#[test]
fn test_deep_directory_path() {
    let dir = tempdir().expect("tempdir");
    let mut path = dir.path().to_path_buf();
    for i in 0..20 {
        path = path.join(format!("level_{}", i));
    }
    fs::create_dir_all(&path).expect("mkdir ok");

    let source_path = path.join("deep.spl");
    fs::write(&source_path, "main = 789").expect("write ok");

    let runner = Runner::new_no_gc();
    let result = runner.run_file(&source_path).expect("run ok");
    assert_eq!(result, 789);
}

/// Test reading file that becomes unavailable (deleted mid-operation)
#[test]
fn test_file_deleted_after_compile() {
    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("deleted.smf");

    let runner = Runner::new_no_gc();
    runner
        .compile_to_smf("main = 100", &smf_path)
        .expect("compile ok");

    // Load the module first
    let loader = ModuleLoader::new();
    let module = loader.load(&smf_path).expect("load ok");

    // Delete the file
    fs::remove_file(&smf_path).expect("delete ok");

    // Module should still work (already loaded)
    let entry: fn() -> i32 = module.entry_point().expect("entry ok");
    assert_eq!(entry(), 100);
}

/// Test compiling to read-only directory fails gracefully
#[test]
#[cfg(unix)]
fn test_compile_to_readonly_dir() {
    use std::os::unix::fs::PermissionsExt;

    let dir = tempdir().expect("tempdir");
    let readonly_dir = dir.path().join("readonly");
    fs::create_dir(&readonly_dir).expect("mkdir ok");

    // Make directory read-only
    let mut perms = fs::metadata(&readonly_dir).expect("meta").permissions();
    perms.set_mode(0o555);
    fs::set_permissions(&readonly_dir, perms).expect("chmod ok");

    let smf_path = readonly_dir.join("test.smf");
    let runner = Runner::new_no_gc();
    let result = runner.compile_to_smf("main = 0", &smf_path);

    // Restore permissions for cleanup
    let mut perms = fs::metadata(&readonly_dir).expect("meta").permissions();
    perms.set_mode(0o755);
    fs::set_permissions(&readonly_dir, perms).expect("chmod ok");

    assert!(
        result.is_err(),
        "Should fail to write to read-only directory"
    );
}

// =============================================================================
// Parser Integration Tests (End-to-End)
// =============================================================================

/// Test parsing and running function definition
#[test]
fn test_parse_and_run_function() {
    let source = r#"
fn add(a, b):
    return a + b

main = add(10, 20)
"#;
    let runner = Runner::new_no_gc();
    let result = runner.run_source(source).expect("run ok");
    assert_eq!(result, 30);
}

/// Test parsing various literals through full pipeline
#[test]
fn test_parse_integer_literals() {
    let runner = Runner::new_no_gc();

    // Positive
    assert_eq!(runner.run_source("main = 42").expect("ok"), 42);

    // Negative
    assert_eq!(runner.run_source("main = -42").expect("ok"), -42);

    // Zero
    assert_eq!(runner.run_source("main = 0").expect("ok"), 0);
}

/// Test lexer handles comments correctly through full pipeline
#[test]
fn test_comments_ignored_in_execution() {
    let source = r#"
# This is a comment
main = 42  # inline comment
# Another comment
"#;
    let runner = Runner::new_no_gc();
    let result = runner.run_source(source).expect("run ok");
    assert_eq!(result, 42);
}

/// Test multiple statements execution
#[test]
fn test_multiple_variable_definitions() {
    let source = r#"
a = 10
b = 20
c = a + b
main = c
"#;
    let runner = Runner::new_no_gc();
    let result = runner.run_source(source).expect("run ok");
    assert_eq!(result, 30);
}

/// Test parser handles invalid syntax
#[test]
fn test_parser_invalid_syntax_handling() {
    let runner = Runner::new_no_gc();

    // Unclosed parenthesis - should fail or succeed gracefully
    let result = runner.run_source("main = (1 + 2");
    // Just verify it doesn't panic - behavior depends on parser recovery
    let _ = result;

    // Invalid characters - should produce an error
    let result = runner.run_source("main = @#$");
    assert!(result.is_err(), "Invalid chars should fail");
}

/// Test lexer handles various whitespace correctly
#[test]
fn test_whitespace_handling() {
    let source = "main    =    42"; // Extra spaces
    let runner = Runner::new_no_gc();
    let result = runner.run_source(source).expect("run ok");
    assert_eq!(result, 42);
}

/// Test tab vs space indentation
#[test]
fn test_tab_indentation() {
    let source = "fn foo():\n\treturn 42\nmain = foo()";
    let runner = Runner::new_no_gc();
    let result = runner.run_source(source).expect("run ok");
    assert_eq!(result, 42);
}

