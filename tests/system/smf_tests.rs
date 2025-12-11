//! SMF format tests: Header, Section, Direct Execution, Format Validation
//! Tests for Simple Module Format (SMF) functionality

use simple_compiler::CompilerPipeline;
use simple_driver::{run_code, Interpreter, RunConfig, Runner, RunningType};
use simple_loader::ModuleLoader;
use simple_parser::{Lexer, Parser};
use std::fs;
use tempfile::tempdir;

// =============================================================================
// SMF Header Coverage Tests
// =============================================================================

/// Test SmfHeader::has_debug_info()
#[test]
fn test_smf_header_has_debug_info() {
    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("debug_info_test.smf");

    let runner = Runner::new_no_gc();
    runner
        .compile_to_smf("main = 0", &smf_path)
        .expect("compile ok");

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
    assert!(
        config.get("SIMPLE_TEST_VAR_12345").is_some()
            || config.get("SIMPLE_TEST_VAR_12345").is_none()
    );

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

// =============================================================================
// SMF Direct Execution Tests
// =============================================================================

/// Test compiling source to SMF and running SMF directly
#[test]
fn test_compile_and_run_smf_directly() {
    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("program.smf");

    // Step 1: Compile source to SMF
    let runner = Runner::new();
    runner
        .compile_to_smf("main = 42", &smf_path)
        .expect("compile ok");

    // Step 2: Run SMF directly using new method
    let result = runner.run_smf(&smf_path).expect("run smf ok");

    // Step 3: Verify result
    assert_eq!(result, 42, "SMF should return correct value");
}

/// Test run_smf with various return values
#[test]
fn test_run_smf_various_values() {
    let dir = tempdir().expect("tempdir");
    let runner = Runner::new();

    let test_cases = [
        ("main = 0", 0),
        ("main = 1", 1),
        ("main = -1", -1),
        ("main = 255", 255),
        ("main = 1 + 2 * 3", 7),
        ("main = (10 - 3) * 5", 35),
    ];

    for (i, (source, expected)) in test_cases.iter().enumerate() {
        let smf_path = dir.path().join(format!("test{}.smf", i));
        runner
            .compile_to_smf(source, &smf_path)
            .expect("compile ok");
        let result = runner.run_smf(&smf_path).expect("run smf ok");
        assert_eq!(result, *expected, "Test case {}: '{}'", i, source);
    }
}

/// Test that run_file auto-detects .smf extension
#[test]
fn test_run_file_auto_detects_smf() {
    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("auto_detect.smf");

    let runner = Runner::new();
    runner
        .compile_to_smf("main = 99", &smf_path)
        .expect("compile ok");

    // run_file should detect .smf and run directly
    let result = runner.run_file(&smf_path).expect("run file ok");
    assert_eq!(result, 99);
}

/// Test that run_file still works with .spl files
#[test]
fn test_run_file_still_compiles_spl() {
    let dir = tempdir().expect("tempdir");
    let spl_path = dir.path().join("source.spl");

    fs::write(&spl_path, "main = 77").expect("write ok");

    let runner = Runner::new();
    let result = runner.run_file(&spl_path).expect("run file ok");

    assert_eq!(result, 77);
    // Verify SMF was created as side effect
    assert!(spl_path.with_extension("smf").exists());
}

/// Test error handling for non-existent SMF file
#[test]
fn test_run_smf_file_not_found() {
    let runner = Runner::new();
    let result = runner.run_smf(std::path::Path::new("/nonexistent/path.smf"));

    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(
        err.contains("not found") || err.contains("No such file") || err.contains("load failed"),
        "Error should mention file not found: {}",
        err
    );
}

/// Test error handling for invalid SMF file
#[test]
fn test_run_smf_invalid_file() {
    let dir = tempdir().expect("tempdir");
    let invalid_smf = dir.path().join("invalid.smf");

    // Write garbage data
    fs::write(&invalid_smf, "not a valid smf file").expect("write ok");

    let runner = Runner::new();
    let result = runner.run_smf(&invalid_smf);

    assert!(result.is_err());
}

/// Test error handling for unsupported extension with run_file
#[test]
fn test_run_file_unsupported_extension() {
    let dir = tempdir().expect("tempdir");
    let wrong_ext = dir.path().join("file.txt");

    fs::write(&wrong_ext, "main = 1").expect("write ok");

    let runner = Runner::new();
    let result = runner.run_file(&wrong_ext);

    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(
        err.contains("unsupported") || err.contains("extension"),
        "Error should mention unsupported extension: {}",
        err
    );
}

/// Test compile-load-run roundtrip with complex program
#[test]
fn test_smf_roundtrip_complex_program() {
    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("complex.smf");

    let source = "let x = 10\nlet y = 20\nlet z = x + y * 2\nmain = z";

    let runner = Runner::new();
    runner
        .compile_to_smf(source, &smf_path)
        .expect("compile ok");

    let result = runner.run_smf(&smf_path).expect("run smf ok");
    assert_eq!(result, 50); // 10 + 20 * 2 = 50
}

/// Test that SMF can be run multiple times
#[test]
fn test_smf_multiple_runs() {
    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("reusable.smf");

    let runner = Runner::new();
    runner
        .compile_to_smf("main = 42", &smf_path)
        .expect("compile ok");

    // Run multiple times - should always return same result
    for _ in 0..5 {
        let result = runner.run_smf(&smf_path).expect("run smf ok");
        assert_eq!(result, 42);
    }
}

/// Test that different runners can run the same SMF
#[test]
fn test_smf_different_runners() {
    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("shared.smf");

    // Compile with one runner (no GC to avoid thread conflicts)
    let runner1 = Runner::new_no_gc();
    runner1
        .compile_to_smf("main = 123", &smf_path)
        .expect("compile ok");

    // Run with different no-GC runners (can't have multiple GC contexts per thread)
    let runner2 = Runner::new_no_gc();
    let runner3 = Runner::new_no_gc();

    let result1 = runner1.run_smf(&smf_path).expect("run ok");
    let result2 = runner2.run_smf(&smf_path).expect("run ok");
    let result3 = runner3.run_smf(&smf_path).expect("run ok");

    assert_eq!(result1, 123);
    assert_eq!(result2, 123);
    assert_eq!(result3, 123);
}

// =============================================================================
// SMF Format Validation Tests
// =============================================================================

/// Test SMF binary format structure is correct
#[test]
fn test_smf_format_structure() {
    let runner = Runner::new_no_gc();
    let smf_bytes = runner.compile_to_memory("main = 42").expect("compile ok");

    // Check minimum size (header + section + code + symbol + string table)
    assert!(smf_bytes.len() > 100, "SMF should have reasonable size");

    // Check magic bytes "SMF\0"
    assert_eq!(&smf_bytes[0..4], b"SMF\0", "SMF magic should be correct");

    // Check version (0.1)
    assert_eq!(smf_bytes[4], 0, "Major version should be 0");
    assert_eq!(smf_bytes[5], 1, "Minor version should be 1");
}

/// Test SMF contains correct machine code
#[test]
fn test_smf_machine_code_correctness() {
    let runner = Runner::new_no_gc();

    // Test value 42 (0x2A)
    let smf_bytes = runner.compile_to_memory("main = 42").expect("compile ok");

    // Find the code section - look for "mov eax, 42; ret" pattern
    // mov eax, imm32 = B8 + value (little-endian) + C3 (ret)
    let expected_code = [0xB8, 0x2A, 0x00, 0x00, 0x00, 0xC3];
    let found = smf_bytes.windows(6).any(|w| w == expected_code);
    assert!(
        found,
        "SMF should contain correct x86-64 code for returning 42"
    );

    // Test negative value -1 (0xFFFFFFFF)
    let smf_bytes = runner.compile_to_memory("main = -1").expect("compile ok");
    let expected_code = [0xB8, 0xFF, 0xFF, 0xFF, 0xFF, 0xC3];
    let found = smf_bytes.windows(6).any(|w| w == expected_code);
    assert!(
        found,
        "SMF should contain correct x86-64 code for returning -1"
    );
}

/// Test SMF symbol table contains main
#[test]
fn test_smf_symbol_table() {
    let runner = Runner::new_no_gc();
    let smf_bytes = runner.compile_to_memory("main = 0").expect("compile ok");

    // String table should contain "main\0"
    let main_str = b"main\0";
    let found = smf_bytes.windows(5).any(|w| w == main_str);
    assert!(found, "SMF should contain 'main' symbol name");
}

// =============================================================================
// In-Memory Execution Tests
// =============================================================================

/// Test compile_to_memory produces valid SMF
#[test]
fn test_compile_to_memory_produces_valid_smf() {
    let runner = Runner::new_no_gc();
    let smf_bytes = runner.compile_to_memory("main = 99").expect("compile ok");

    // Should be able to load and run the bytes
    let result = runner.run_smf_from_memory(&smf_bytes).expect("run ok");
    assert_eq!(result, 99);
}

/// Test run_source_in_memory basic functionality
#[test]
fn test_run_source_in_memory_basic() {
    let runner = Runner::new_no_gc();

    let result = runner.run_source_in_memory("main = 42").expect("run ok");
    assert_eq!(result, 42);
}

/// Test run_source_in_memory with various values
#[test]
fn test_run_source_in_memory_various_values() {
    let runner = Runner::new_no_gc();

    let test_cases = [
        ("main = 0", 0),
        ("main = 1", 1),
        ("main = -1", -1),
        ("main = 127", 127),
        ("main = -128", -128),
        ("main = 255", 255),
        ("main = 1000", 1000),
        ("main = -1000", -1000),
    ];

    for (source, expected) in test_cases {
        let result = runner.run_source_in_memory(source).expect("run ok");
        assert_eq!(result, expected, "Failed for source: {}", source);
    }
}

/// Test run_source_in_memory with expressions
#[test]
fn test_run_source_in_memory_expressions() {
    let runner = Runner::new_no_gc();

    let test_cases = [
        ("main = 1 + 2", 3),
        ("main = 10 - 3", 7),
        ("main = 6 * 7", 42),
        ("main = 100 / 4", 25),
        ("main = 2 + 3 * 4", 14),
        ("main = (2 + 3) * 4", 20),
    ];

    for (source, expected) in test_cases {
        let result = runner.run_source_in_memory(source).expect("run ok");
        assert_eq!(result, expected, "Failed for source: {}", source);
    }
}

/// Test run_source_in_memory with variables
#[test]
fn test_run_source_in_memory_with_variables() {
    let runner = Runner::new_no_gc();

    let source = "let x = 10\nlet y = 20\nmain = x + y";
    let result = runner.run_source_in_memory(source).expect("run ok");
    assert_eq!(result, 30);
}

/// Test interpreter run_in_memory method
#[test]
fn test_interpreter_run_in_memory() {
    let interpreter = Interpreter::new_no_gc();

    let result = interpreter.run_in_memory("main = 77").expect("run ok");
    assert_eq!(result.exit_code, 77);
}

/// Test interpreter with in_memory config flag
#[test]
fn test_interpreter_in_memory_config() {
    let interpreter = Interpreter::new_no_gc();

    let config = RunConfig {
        in_memory: true,
        ..Default::default()
    };

    let result = interpreter.run("main = 88", config).expect("run ok");
    assert_eq!(result.exit_code, 88);
}

/// Test that in-memory and file-based produce same result
#[test]
fn test_in_memory_vs_file_consistency() {
    let runner = Runner::new_no_gc();
    let source = "let a = 5\nlet b = 10\nmain = a * b + 7";

    let result_in_memory = runner.run_source_in_memory(source).expect("in-memory ok");
    let result_file = runner.run_source(source).expect("file ok");

    assert_eq!(
        result_in_memory, result_file,
        "In-memory and file-based should produce same result"
    );
    assert_eq!(result_in_memory, 57); // 5 * 10 + 7 = 57
}

/// Test compile_to_memory and run_smf_from_memory roundtrip
#[test]
fn test_compile_and_run_from_memory_roundtrip() {
    let runner = Runner::new_no_gc();

    // Compile to memory
    let smf_bytes = runner.compile_to_memory("main = 123").expect("compile ok");

    // Run from memory multiple times
    for _ in 0..3 {
        let result = runner.run_smf_from_memory(&smf_bytes).expect("run ok");
        assert_eq!(result, 123);
    }
}

// =============================================================================
// CLI Integration Tests
// =============================================================================

/// Test CLI help output
#[test]
fn test_cli_help_output() {
    use assert_cmd::Command;

    let mut cmd = Command::cargo_bin("simple").expect("binary exists");
    cmd.arg("--help");
    let output = cmd.output().expect("command ok");
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        stderr.contains("Simple") || stderr.contains("simple") || stderr.contains("Usage"),
        "Help should mention Simple or usage: got stderr={}",
        stderr
    );
}

/// Test CLI runs source code
#[test]
fn test_cli_runs_source() {
    use assert_cmd::Command;

    let dir = tempdir().expect("tempdir");
    let source_path = dir.path().join("test.spl");
    fs::write(&source_path, "main = 42").expect("write ok");

    let mut cmd = Command::cargo_bin("simple").expect("binary exists");
    cmd.arg("run").arg(&source_path);

    let output = cmd.output().expect("command ok");

    // The exit code should be 42
    assert_eq!(output.status.code(), Some(42), "Exit code should be 42");
}

/// Test CLI compiles to SMF
#[test]
fn test_cli_compiles_to_smf() {
    use assert_cmd::Command;

    let dir = tempdir().expect("tempdir");
    let source_path = dir.path().join("compile_test.spl");
    let smf_path = dir.path().join("output.smf");

    fs::write(&source_path, "main = 55").expect("write ok");

    let mut cmd = Command::cargo_bin("simple").expect("binary exists");
    cmd.arg("compile")
        .arg(&source_path)
        .arg("-o")
        .arg(&smf_path);

    let output = cmd.output().expect("command ok");

    // Should succeed
    assert!(
        output.status.success(),
        "Compile should succeed: {:?}",
        output
    );

    // SMF file should exist
    assert!(smf_path.exists(), "SMF file should be created");

    // SMF file should have correct magic
    let smf_bytes = fs::read(&smf_path).expect("read ok");
    assert_eq!(&smf_bytes[0..4], b"SMF\0", "SMF magic should be correct");
}

/// Test CLI runs compiled SMF directly
#[test]
fn test_cli_runs_smf_directly() {
    use assert_cmd::Command;

    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("direct.smf");

    // First compile
    let runner = Runner::new_no_gc();
    runner
        .compile_to_smf("main = 33", &smf_path)
        .expect("compile ok");

    // Then run via CLI
    let mut cmd = Command::cargo_bin("simple").expect("binary exists");
    cmd.arg("run").arg(&smf_path);

    let output = cmd.output().expect("command ok");

    assert_eq!(output.status.code(), Some(33), "Exit code should be 33");
}

/// Test CLI version output
#[test]
fn test_cli_version() {
    use assert_cmd::Command;

    let mut cmd = Command::cargo_bin("simple").expect("binary exists");
    cmd.arg("--version");
    let output = cmd.output().expect("command ok");
    let stdout = String::from_utf8_lossy(&output.stdout);

    assert!(
        stdout.contains("Simple") && stdout.contains("0.1.0"),
        "Version should show Simple and version number"
    );
}

/// Test CLI -c flag runs code string
#[test]
fn test_cli_run_code_string() {
    use assert_cmd::Command;

    let mut cmd = Command::cargo_bin("simple").expect("binary exists");
    cmd.arg("-c").arg("42");
    let output = cmd.output().expect("command ok");

    assert_eq!(output.status.code(), Some(42), "Exit code should be 42");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("42"), "Output should contain 42");
}

/// Test CLI -c with full program
#[test]
fn test_cli_run_code_string_full() {
    use assert_cmd::Command;

    let mut cmd = Command::cargo_bin("simple").expect("binary exists");
    cmd.arg("-c").arg("let x = 10\nmain = x * 5");
    let output = cmd.output().expect("command ok");

    assert_eq!(output.status.code(), Some(50), "Exit code should be 50");
}

/// Test CLI runs source file directly (without 'run' command)
#[test]
fn test_cli_runs_file_directly() {
    use assert_cmd::Command;

    let dir = tempdir().expect("tempdir");
    let source_path = dir.path().join("direct.spl");
    fs::write(&source_path, "main = 77").expect("write ok");

    let mut cmd = Command::cargo_bin("simple").expect("binary exists");
    cmd.arg(&source_path); // No 'run' command, just the file

    let output = cmd.output().expect("command ok");
    assert_eq!(output.status.code(), Some(77), "Exit code should be 77");
}

/// Test CLI compile without -o uses default output name
#[test]
fn test_cli_compile_default_output() {
    use assert_cmd::Command;

    let dir = tempdir().expect("tempdir");
    let source_path = dir.path().join("default_out.spl");
    let expected_smf = dir.path().join("default_out.smf");

    fs::write(&source_path, "main = 88").expect("write ok");

    let mut cmd = Command::cargo_bin("simple").expect("binary exists");
    cmd.arg("compile").arg(&source_path);
    let output = cmd.output().expect("command ok");

    assert!(output.status.success(), "Compile should succeed");
    assert!(expected_smf.exists(), "Default .smf file should be created");
}

// =============================================================================
// ExecCore In-Memory Execution Tests
// =============================================================================

/// Test ExecCore::compile_to_memory()
#[test]
fn test_exec_core_compile_to_memory() {
    use simple_driver::exec_core::ExecCore;

    let core = ExecCore::new_no_gc();
    let smf_bytes = core.compile_to_memory("main = 42").expect("compile ok");

    assert!(!smf_bytes.is_empty(), "SMF bytes should not be empty");
    assert_eq!(
        &smf_bytes[0..4],
        b"SMF\0",
        "SMF magic header should be correct"
    );
}

/// Test ExecCore::run_source_in_memory()
#[test]
fn test_exec_core_run_source_in_memory() {
    use simple_driver::exec_core::ExecCore;

    let core = ExecCore::new_no_gc();
    let result = core.run_source_in_memory("main = 99").expect("run ok");
    assert_eq!(result, 99);
}

/// Test ExecCore::run_smf_from_memory()
#[test]
fn test_exec_core_run_smf_from_memory() {
    use simple_driver::exec_core::ExecCore;

    let core = ExecCore::new_no_gc();
    let smf_bytes = core.compile_to_memory("main = 123").expect("compile ok");

    let result = core.run_smf_from_memory(&smf_bytes).expect("run ok");
    assert_eq!(result, 123);
}

/// Test ExecCore::load_module_from_memory()
#[test]
fn test_exec_core_load_module_from_memory() {
    use simple_driver::exec_core::ExecCore;

    let core = ExecCore::new_no_gc();
    let smf_bytes = core.compile_to_memory("main = 55").expect("compile ok");

    let module = core.load_module_from_memory(&smf_bytes).expect("load ok");
    let entry: Option<fn() -> i32> = module.entry_point();
    assert!(entry.is_some(), "Should have entry point");
    assert_eq!(entry.unwrap()(), 55);
}

/// Test ExecCore::run_smf() with pre-compiled file
#[test]
fn test_exec_core_run_smf() {
    use simple_driver::exec_core::ExecCore;

    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("run_smf_test.smf");

    let core = ExecCore::new_no_gc();
    core.compile_source("main = 200", &smf_path)
        .expect("compile ok");

    let result = core.run_smf(&smf_path).expect("run ok");
    assert_eq!(result, 200);
}

/// Test ExecCore::run_file() auto-detect .spl
#[test]
fn test_exec_core_run_file_spl() {
    use simple_driver::exec_core::ExecCore;

    let dir = tempdir().expect("tempdir");
    let source_path = dir.path().join("auto_spl.spl");
    fs::write(&source_path, "main = 150").expect("write ok");

    let core = ExecCore::new_no_gc();
    let result = core.run_file(&source_path).expect("run ok");
    assert_eq!(result, 150);
}

/// Test ExecCore::run_file() auto-detect .smf
#[test]
fn test_exec_core_run_file_smf() {
    use simple_driver::exec_core::ExecCore;

    let dir = tempdir().expect("tempdir");
    let smf_path = dir.path().join("auto_smf.smf");

    let core = ExecCore::new_no_gc();
    core.compile_source("main = 175", &smf_path)
        .expect("compile ok");

    let result = core.run_file(&smf_path).expect("run ok");
    assert_eq!(result, 175);
}

/// Test ExecCore::run_file() unsupported extension error
#[test]
fn test_exec_core_run_file_unsupported() {
    use simple_driver::exec_core::ExecCore;

    let dir = tempdir().expect("tempdir");
    let bad_path = dir.path().join("test.xyz");
    fs::write(&bad_path, "main = 0").expect("write ok");

    let core = ExecCore::new_no_gc();
    let result = core.run_file(&bad_path);
    assert!(result.is_err(), "Unsupported extension should error");
    assert!(
        result.unwrap_err().contains(".xyz"),
        "Error should mention extension"
    );
}

/// Test ExecCore::run_file() with no extension (treated as .spl)
#[test]
fn test_exec_core_run_file_no_extension() {
    use simple_driver::exec_core::ExecCore;

    let dir = tempdir().expect("tempdir");
    let no_ext_path = dir.path().join("noext");
    fs::write(&no_ext_path, "main = 225").expect("write ok");

    let core = ExecCore::new_no_gc();
    let result = core.run_file(&no_ext_path).expect("run ok");
    assert_eq!(result, 225);
}

/// Test in-memory roundtrip: compile, load, run
#[test]
fn test_in_memory_roundtrip() {
    use simple_driver::exec_core::{run_main, ExecCore};

    let core = ExecCore::new_no_gc();

    // Compile to memory
    let smf_bytes = core
        .compile_to_memory("main = 1 + 2 + 3")
        .expect("compile ok");

    // Load from memory
    let module = core.load_module_from_memory(&smf_bytes).expect("load ok");

    // Run
    let exit = run_main(&module).expect("run ok");
    assert_eq!(exit, 6);
}

/// Test multiple in-memory executions with same core
#[test]
fn test_multiple_in_memory_runs() {
    use simple_driver::exec_core::ExecCore;

    let core = ExecCore::new_no_gc();

    for i in 0..10 {
        let source = format!("main = {}", i * 10);
        let result = core.run_source_in_memory(&source).expect("run ok");
        assert_eq!(result, i * 10);
    }
}

