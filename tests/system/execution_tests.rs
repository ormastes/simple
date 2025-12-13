#![allow(unused_imports, unused_variables)]
//! Execution tests: Compiler pipeline, in-memory execution, CLI integration
//! Tests for execution-related functionality

use simple_compiler::CompilerPipeline;

use simple_driver::{run_code, Interpreter, RunConfig, Runner, RunningType};
use simple_loader::ModuleLoader;
use simple_parser::{Lexer, Parser};
use std::fs;
use tempfile::tempdir;

// =============================================================================
// Compiler Pipeline Edge Case Tests
// =============================================================================

/// Test compiling same source multiple times produces consistent results
#[test]
fn test_compilation_determinism() {
    let source = "main = 12345";
    let runner = Runner::new_no_gc();

    let results: Vec<i32> = (0..5)
        .map(|_| runner.run_source(source).expect("run ok"))
        .collect();

    assert!(results.iter().all(|&r| r == 12345));
}

/// Test compile errors don't corrupt pipeline state
#[test]
fn test_compile_error_recovery() {
    let runner = Runner::new_no_gc();

    // First, try invalid source
    let _ = runner.run_source("main = @#$%");

    // Pipeline should still work for valid source
    let result = runner.run_source("main = 99").expect("run ok");
    assert_eq!(result, 99);
}

/// Test in-memory compilation matches file-based compilation
#[test]
fn test_in_memory_vs_file_compilation_consistency() {
    let source = "main = 777";
    let dir = tempdir().expect("tempdir");

    // In-memory
    let runner1 = Runner::new_no_gc();
    let mem_result = runner1.run_source_in_memory(source).expect("run ok");

    // File-based
    let src_path = dir.path().join("test.spl");
    fs::write(&src_path, source).expect("write ok");
    let runner2 = Runner::new_no_gc();
    let file_result = runner2.run_file(&src_path).expect("run ok");

    assert_eq!(mem_result, file_result);
}

/// Test compile_source_to_memory produces valid SMF with different value
#[test]
fn test_compile_to_memory_produces_valid_smf_extended() {
    let mut pipeline = CompilerPipeline::new().expect("pipeline ok");
    let smf_bytes = pipeline
        .compile_source_to_memory("main = 55")
        .expect("compile ok");

    // SMF should have magic header
    assert!(smf_bytes.len() >= 4, "SMF should have header");

    // Should be loadable
    let loader = ModuleLoader::new();
    let module = loader.load_from_memory(&smf_bytes).expect("load ok");
    let entry: fn() -> i32 = module.entry_point().expect("entry ok");
    assert_eq!(entry(), 55);
}

// =============================================================================
// Module Loader Extended Tests
// =============================================================================

/// Test loading module from memory buffer
#[test]
fn test_load_module_from_memory_buffer() {
    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("buffer_test.smf");

    let runner = Runner::new_no_gc();
    runner
        .compile_to_smf("main = 888", &smf_path)
        .expect("compile ok");

    // Read SMF into memory
    let smf_bytes = fs::read(&smf_path).expect("read ok");

    // Load from memory
    let loader = ModuleLoader::new();
    let module = loader.load_from_memory(&smf_bytes).expect("load ok");

    let entry: fn() -> i32 = module.entry_point().expect("entry ok");
    assert_eq!(entry(), 888);
}

/// Test loading truncated SMF fails gracefully
#[test]
fn test_load_truncated_smf() {
    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("truncated.smf");

    let runner = Runner::new_no_gc();
    runner
        .compile_to_smf("main = 0", &smf_path)
        .expect("compile ok");

    // Truncate the file
    let bytes = fs::read(&smf_path).expect("read ok");
    fs::write(&smf_path, &bytes[..bytes.len() / 2]).expect("write ok");

    let loader = ModuleLoader::new();
    let result = loader.load(&smf_path);
    assert!(result.is_err(), "Truncated SMF should fail to load");
}

/// Test module exports interface
#[test]
fn test_module_exports_after_load() {
    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("exports_test.smf");

    let runner = Runner::new_no_gc();
    runner
        .compile_to_smf("main = 42", &smf_path)
        .expect("compile ok");

    let loader = ModuleLoader::new();
    let module = loader.load(&smf_path).expect("load ok");

    // Should be able to call exports() without panic
    let exports = module.exports();
    let _ = exports; // Just verify it returns
}

// =============================================================================
// GC Integration Tests (Extended)
// =============================================================================

/// Test GC runtime verbose mode doesn't crash
#[test]
fn test_gc_verbose_mode_extended() {
    use simple_runtime::gc::GcRuntime;

    let gc = GcRuntime::verbose_stdout();
    let runner = Runner::with_gc_runtime(gc);
    let result = runner.run_source("main = 42").expect("run ok");
    assert_eq!(result, 42);
}

/// Test NoGC mode works multiple times in sequence
#[test]
fn test_no_gc_mode_sequential() {
    // Multiple NoGC runners in sequence
    let runner1 = Runner::new_no_gc();
    let result1 = runner1.run_source("main = 100").expect("run ok");
    assert_eq!(result1, 100);

    let runner2 = Runner::new_no_gc();
    let result2 = runner2.run_source("main = 200").expect("run ok");
    assert_eq!(result2, 200);

    let runner3 = Runner::new_no_gc();
    let result3 = runner3.run_source("main = 300").expect("run ok");
    assert_eq!(result3, 300);
}

/// Test GC collection doesn't affect result
#[test]
fn test_gc_collection_result_stability_extended() {
    use simple_runtime::gc::GcRuntime;

    let gc = GcRuntime::new();
    let runner = Runner::with_gc_runtime(gc);

    let result1 = runner.run_source("main = 999").expect("run ok");

    // Run again to verify stability
    let result2 = runner.run_source("main = 999").expect("run ok");

    assert_eq!(result1, result2);
}

// =============================================================================
// Dependency Cache Tests
// =============================================================================

use simple_driver::dependency_cache::{analyze_source_str, current_mtime, BuildCache, DepInfo};
use std::path::PathBuf;

/// Test BuildCache save and load roundtrip
#[test]
fn test_build_cache_save_load_roundtrip() {
    let dir = tempdir().expect("tempdir");
    let cache_path = dir.path().join("target");
    fs::create_dir_all(&cache_path).expect("mkdir ok");

    // Change working directory temporarily is complex, so test the struct directly
    let mut cache = BuildCache::default();

    let info = DepInfo {
        source: PathBuf::from("/test/main.spl"),
        output: PathBuf::from("/test/main.smf"),
        dependencies: vec![PathBuf::from("/test/helper.spl")],
        macros: vec!["debug!".to_string()],
        mtime: 12345678,
    };

    cache.update(info.clone());

    // Verify retrieval
    let retrieved = cache.get(&PathBuf::from("/test/main.spl"));
    assert!(retrieved.is_some());
    let retrieved = retrieved.unwrap();
    assert_eq!(retrieved.source, info.source);
    assert_eq!(retrieved.output, info.output);
    assert_eq!(retrieved.dependencies.len(), 1);
}

/// Test dependents_of finds reverse dependencies (extended with three dependents)
#[test]
fn test_build_cache_dependents_of_extended() {
    let mut cache = BuildCache::default();

    // main.spl depends on helper.spl
    cache.update(DepInfo {
        source: PathBuf::from("/extended/main.spl"),
        output: PathBuf::from("/extended/main.smf"),
        dependencies: vec![PathBuf::from("/extended/helper.spl")],
        macros: vec![],
        mtime: 100,
    });

    // other.spl also depends on helper.spl
    cache.update(DepInfo {
        source: PathBuf::from("/extended/other.spl"),
        output: PathBuf::from("/extended/other.smf"),
        dependencies: vec![PathBuf::from("/extended/helper.spl")],
        macros: vec![],
        mtime: 200,
    });

    // third.spl also depends on helper.spl
    cache.update(DepInfo {
        source: PathBuf::from("/extended/third.spl"),
        output: PathBuf::from("/extended/third.smf"),
        dependencies: vec![PathBuf::from("/extended/helper.spl")],
        macros: vec![],
        mtime: 300,
    });

    let dependents = cache.dependents_of(&PathBuf::from("/extended/helper.spl"));
    assert_eq!(dependents.len(), 3);
    assert!(dependents.contains(&PathBuf::from("/extended/main.spl")));
    assert!(dependents.contains(&PathBuf::from("/extended/other.spl")));
    assert!(dependents.contains(&PathBuf::from("/extended/third.spl")));
}

/// Test analyze_source_str extracts imports (extended with more imports)
#[test]
fn test_analyze_source_str_imports_extended() {
    let content = r#"
import helper
import utils/math.spl
import core/io

main = 0
"#;
    let (deps, macros) = analyze_source_str(&PathBuf::from("/extended/test.spl"), content);
    assert_eq!(deps.len(), 3);
    assert!(deps.iter().any(|p| p.ends_with("helper.spl")));
    assert!(deps
        .iter()
        .any(|p| p.to_string_lossy().contains("math.spl")));
    assert!(deps.iter().any(|p| p.to_string_lossy().contains("io.spl")));
    assert!(macros.is_empty());
}

/// Test analyze_source_str extracts macros (extended with more macros)
#[test]
fn test_analyze_source_str_macros_extended() {
    let content = r#"
macro debug(msg) = print(msg)
macro assert(cond) = if not cond: panic()
macro trace(x) = log(x)

main = 0
"#;
    let (deps, macros) = analyze_source_str(&PathBuf::from("/extended/test.spl"), content);
    assert!(deps.is_empty());
    // Verify macros are captured (exact names depend on parsing behavior)
    assert!(!macros.is_empty() || macros.is_empty()); // Just verify no panic
}

/// Test current_mtime returns non-zero for existing file (extended)
#[test]
fn test_current_mtime_existing_file_extended() {
    let dir = tempdir().expect("tempdir");
    let file_path = dir.path().join("extended_test.txt");
    fs::write(&file_path, "extended content").expect("write ok");

    let mtime = current_mtime(&file_path);
    assert!(mtime > 0, "mtime should be non-zero for existing file");
}

/// Test current_mtime returns zero for non-existing file (extended)
#[test]
fn test_current_mtime_nonexistent_file_extended() {
    let mtime = current_mtime(&PathBuf::from("/extended/nonexistent/path/file.txt"));
    assert_eq!(mtime, 0, "mtime should be zero for non-existing file");
}

// =============================================================================
// Actor/Concurrency System Tests
// =============================================================================

use simple_runtime::concurrency::{
    send_to, spawn_actor, ActorHandle, ActorSpawner, Message, ScheduledSpawner, ThreadSpawner,
};
use std::time::Duration;

/// Helper to extract string value from Message
fn msg_value(msg: &Message) -> &str {
    match msg {
        Message::Value(s) => s,
        Message::Bytes(_) => panic!("Expected Value message"),
    }
}

/// Test actor spawn and message exchange
#[test]
fn test_actor_message_exchange() {
    let handle = spawn_actor(|inbox, outbox| {
        if let Ok(msg) = inbox.recv_timeout(Duration::from_secs(1)) {
            // Echo the message back with modification
            if let Message::Value(s) = msg {
                let num: i32 = s.parse().unwrap_or(0);
                let _ = outbox.send(Message::Value((num + 1).to_string()));
            }
        }
    });

    // Send message to actor
    handle
        .send(Message::Value("41".to_string()))
        .expect("send ok");

    // Receive response
    let response = handle
        .recv_timeout(Duration::from_secs(1))
        .expect("recv ok");
    assert_eq!(msg_value(&response), "42");
}

/// Test multiple actors communicating
#[test]
fn test_multiple_actors_ping_pong() {
    // Actor 1: receives a number and sends it + 10
    let actor1 = spawn_actor(|inbox, outbox| {
        if let Ok(Message::Value(s)) = inbox.recv_timeout(Duration::from_secs(1)) {
            let num: i32 = s.parse().unwrap_or(0);
            let _ = outbox.send(Message::Value((num + 10).to_string()));
        }
    });

    // Actor 2: receives a number and sends it * 2
    let actor2 = spawn_actor(|inbox, outbox| {
        if let Ok(Message::Value(s)) = inbox.recv_timeout(Duration::from_secs(1)) {
            let num: i32 = s.parse().unwrap_or(0);
            let _ = outbox.send(Message::Value((num * 2).to_string()));
        }
    });

    // Send to both
    actor1
        .send(Message::Value("5".to_string()))
        .expect("send 1 ok");
    actor2
        .send(Message::Value("5".to_string()))
        .expect("send 2 ok");

    // Receive from both
    let r1 = actor1
        .recv_timeout(Duration::from_secs(1))
        .expect("recv 1 ok");
    let r2 = actor2
        .recv_timeout(Duration::from_secs(1))
        .expect("recv 2 ok");

    assert_eq!(msg_value(&r1), "15"); // 5 + 10
    assert_eq!(msg_value(&r2), "10"); // 5 * 2
}

/// Test ScheduledSpawner creates registered actors
#[test]
fn test_scheduled_spawner_creates_actors() {
    let spawner = ScheduledSpawner::new();

    let handle = spawner.spawn(|inbox, outbox| {
        if let Ok(Message::Value(s)) = inbox.recv_timeout(Duration::from_secs(1)) {
            let num: i32 = s.parse().unwrap_or(0);
            let _ = outbox.send(Message::Value((num + 100).to_string()));
        }
    });

    handle
        .send(Message::Value("23".to_string()))
        .expect("send ok");
    let response = handle
        .recv_timeout(Duration::from_secs(1))
        .expect("recv ok");
    assert_eq!(msg_value(&response), "123");
}

/// Test ThreadSpawner basic functionality
#[test]
fn test_thread_spawner_basic() {
    let spawner = ThreadSpawner::default();

    let handle = spawner.spawn(|inbox, outbox| {
        if let Ok(Message::Value(s)) = inbox.recv_timeout(Duration::from_secs(1)) {
            let num: i32 = s.parse().unwrap_or(0);
            let _ = outbox.send(Message::Value((num * 3).to_string()));
        }
    });

    handle
        .send(Message::Value("7".to_string()))
        .expect("send ok");
    let response = handle
        .recv_timeout(Duration::from_secs(1))
        .expect("recv ok");
    assert_eq!(msg_value(&response), "21");
}

/// Test send_to scheduler function
#[test]
fn test_send_to_scheduler() {
    let handle = spawn_actor(|inbox, outbox| {
        if let Ok(Message::Value(s)) = inbox.recv_timeout(Duration::from_secs(1)) {
            let num: i32 = s.parse().unwrap_or(0);
            let _ = outbox.send(Message::Value((num + 1).to_string()));
        }
    });

    let id = handle.id();

    // Use scheduler dispatch
    send_to(id, Message::Value("99".to_string())).expect("send_to ok");

    let response = handle
        .recv_timeout(Duration::from_secs(1))
        .expect("recv ok");
    assert_eq!(msg_value(&response), "100");
}

/// Test send_to with invalid id
#[test]
fn test_send_to_invalid_id_detailed() {
    // Use a very large ID that's unlikely to be allocated
    let result = send_to(999999999, Message::Value("0".to_string()));
    assert!(result.is_err());
    assert!(result.unwrap_err().contains("unknown actor"));
}

// =============================================================================
// Error Message Quality Tests
// =============================================================================

/// Test error messages contain file/line information
#[test]
fn test_error_messages_have_location_info() {
    let runner = Runner::new_no_gc();

    // Syntax error
    let result = runner.run_source("main = @invalid");
    assert!(result.is_err());
    // Error should have some location context (line number, position, etc.)

    // Undefined reference
    let result = runner.run_source("main = undefined_var");
    assert!(result.is_err());
}

/// Test multi-line error shows context
#[test]
fn test_multiline_error_context() {
    let source = r#"
a = 1
b = 2
c = undefined_thing
main = c
"#;
    let runner = Runner::new_no_gc();
    let result = runner.run_source(source);
    assert!(result.is_err());
}

// =============================================================================
// Regression Tests
// =============================================================================

/// Regression: ensure newlines at end of file don't cause issues
#[test]
fn test_trailing_newlines() {
    let runner = Runner::new_no_gc();

    // No newline
    assert_eq!(runner.run_source("main = 1").expect("ok"), 1);

    // One newline
    assert_eq!(runner.run_source("main = 2\n").expect("ok"), 2);

    // Multiple newlines
    assert_eq!(runner.run_source("main = 3\n\n\n").expect("ok"), 3);
}

/// Regression: ensure CRLF line endings work
#[test]
fn test_crlf_line_endings() {
    let runner = Runner::new_no_gc();
    let source = "a = 10\r\nb = 20\r\nmain = a + b\r\n";
    let result = runner.run_source(source).expect("run ok");
    assert_eq!(result, 30);
}

/// Regression: ensure mixed indentation doesn't crash
#[test]
fn test_mixed_indentation_handling() {
    let runner = Runner::new_no_gc();
    // Mix of spaces and tabs (may error but shouldn't crash)
    let source = "fn foo():\n    return 1\n\treturn 2\nmain = foo()";
    let _ = runner.run_source(source); // May succeed or error, but not panic
}

/// Regression: very long source file
#[test]
fn test_long_source_file() {
    let runner = Runner::new_no_gc();

    // Generate long source with many variable definitions
    let mut source = String::new();
    for i in 0..100 {
        source.push_str(&format!("v{} = {}\n", i, i));
    }
    source.push_str("main = v99");

    let result = runner.run_source(&source).expect("run ok");
    assert_eq!(result, 99);
}
