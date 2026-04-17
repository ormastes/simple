//! Test file execution logic.
//!
//! Handles running individual test files and parsing their output.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

use crate::runner::Runner;
use super::types::{IndividualTestResult, TestFileResult, TestExecutionMode};
use super::build_cache::BuildCache;
use super::artifact::{ExecutionArtifacts, write_test_artifacts};
#[path = "scenario_artifacts.rs"]
mod scenario_artifacts;

use simple_compiler::i18n::clear_registry as clear_i18n_state;
use simple_compiler::interpreter::{
    clear_bdd_state, clear_class_instantiation_state, clear_effects_state, clear_interpreter_state, clear_io_state,
    clear_macro_state, clear_module_cache, clear_module_cache_selective, clear_net_state, clear_collection_registries,
    clear_ast_ffi_registries, clear_env_ffi_registry, clear_error_ffi_registry, clear_span_ffi_registry,
};
use simple_compiler::runtime_profile::profiler::clear_global_profiler;
use simple_compiler::layout_recorder::clear_recording;
use simple_runtime::value::clear_all_runtime_registries;
use simple_compiler::interpreter_ffi::clear_interpreter_state as clear_interp_ffi_state;
use simple_compiler::interpreter_ffi::clear_expr_registry;
use simple_compiler::hir::clear_hir_thread_arena;
use simple_compiler::mir::clear_mir_thread_arena;
use simple_compiler::codegen::clear_thread_buffer_pool;
use simple_compiler::interpreter::clear_pinned_strings;
use simple_compiler::interpreter::clear_concurrency_registries;
use simple_compiler::codegen::clear_cranelift_registries;
use simple_compiler::interpreter_ffi::clear_compiled_functions;
use simple_compiler::{start_watchdog, stop_watchdog};
use simple_compiler::import_loader::collect_imported_module_paths;
use simple_common::fault_detection::{reset_timeout, set_stack_overflow_detection_enabled, reset_recursion_depth};
use simple_native_loader::default_runtime_provider;
use simple_runtime::loader::registry::ModuleRegistry;
use simple_runtime::value::{
    rt_capture_stderr_start, rt_capture_stderr_stop, rt_capture_stdout_start, rt_capture_stdout_stop, rt_set_args_vec,
};
use scenario_artifacts::write_scenario_manifest;
use crate::exec_core::run_main;

/// Default per-test timeout in seconds (overridable via SIMPLE_TEST_TIMEOUT env var).
fn per_test_timeout_secs(path: &Path) -> u64 {
    if let Ok(raw) = std::env::var("SIMPLE_TEST_TIMEOUT") {
        if let Ok(parsed) = raw.parse::<u64>() {
            return parsed;
        }
    }
    if path.components().any(|c| c.as_os_str() == "system") {
        return 120;
    }
    60
}

/// Get current process RSS in bytes. Returns 0 on failure.
fn get_rss_bytes() -> u64 {
    #[cfg(target_os = "linux")]
    {
        if let Ok(contents) = std::fs::read_to_string("/proc/self/statm") {
            // statm fields: size resident shared text lib data dt (in pages)
            if let Some(resident_pages) = contents.split_whitespace().nth(1) {
                if let Ok(pages) = resident_pages.parse::<u64>() {
                    return pages * 4096; // page size
                }
            }
        }
    }
    0
}

/// Memory threshold in bytes above which we abort the test run (default: 4 GB).
/// Override with SIMPLE_TEST_MEMORY_LIMIT_MB env var. Set to 0 to disable.
fn memory_limit_bytes() -> u64 {
    std::env::var("SIMPLE_TEST_MEMORY_LIMIT_MB")
        .ok()
        .and_then(|v| v.parse::<u64>().ok())
        .unwrap_or(4096)
        * 1024
        * 1024
}

/// Parse test output to extract pass/fail counts
pub fn parse_test_output(output: &str) -> (usize, usize) {
    // Look for patterns like "N examples, M failures"
    // Sum all occurrences (each describe block outputs one)
    let mut total_passed = 0;
    let mut total_failed = 0;

    for line in output.lines() {
        // Pattern: "X examples, Y failures"
        if line.contains("examples") && line.contains("failure") {
            // Strip ANSI escape codes first (they contain numbers like \x1b[32m)
            let clean_line = strip_ansi_codes(line);

            // Extract numbers from cleaned line
            let parts: Vec<&str> = clean_line.split(|c: char| !c.is_numeric()).collect();
            let numbers: Vec<usize> = parts.iter().filter_map(|p| p.parse::<usize>().ok()).collect();

            if numbers.len() >= 2 {
                let total = numbers[0];
                let failed = numbers[1];
                let passed = total.saturating_sub(failed);
                total_passed += passed;
                total_failed += failed;
            }
        }
    }

    (total_passed, total_failed)
}

/// Parse individual test results from BDD output (✓/✗/○ lines)
pub fn parse_individual_results(output: &str) -> Vec<IndividualTestResult> {
    let mut results = Vec::new();
    let mut current_group = Vec::<String>::new();

    for line in output.lines() {
        let clean = strip_ansi_codes(line);
        let trimmed = clean.trim();

        if let Some(stripped) = trimmed.strip_prefix("✓ ") {
            let name = stripped.to_string();
            results.push(IndividualTestResult {
                name,
                group: current_group.join(" > "),
                passed: true,
                skipped: false,
            });
        } else if trimmed.starts_with("✗ ") {
            let name = trimmed[5..].to_string(); // "✗ " is 5 bytes
            results.push(IndividualTestResult {
                name,
                group: current_group.join(" > "),
                passed: false,
                skipped: false,
            });
        } else if trimmed.starts_with("○ ") {
            let name = trimmed[5..].trim_end_matches(" (skipped)").to_string(); // "○ " is 5 bytes
            results.push(IndividualTestResult {
                name,
                group: current_group.join(" > "),
                passed: true,
                skipped: true,
            });
        } else if !trimmed.is_empty()
            && !trimmed.contains("examples")
            && !trimmed.contains("failure")
            && !trimmed.starts_with("running")
            && !trimmed.starts_with("[")
        {
            // This is likely a describe/context group header
            // Use indentation to determine nesting level
            let indent_level = (clean.len() - clean.trim_start().len()) / 2;
            current_group.truncate(indent_level);
            if current_group.len() == indent_level {
                current_group.push(trimmed.to_string());
            }
        }
    }

    results
}

/// Strip ANSI escape codes from a string
fn strip_ansi_codes(s: &str) -> String {
    let mut result = String::with_capacity(s.len());
    let mut chars = s.chars().peekable();

    while let Some(c) = chars.next() {
        if c == '\x1b' {
            // Skip escape sequence: ESC [ ... m
            if chars.peek() == Some(&'[') {
                chars.next(); // consume '['
                              // Skip until 'm' or end
                while let Some(&ch) = chars.peek() {
                    chars.next();
                    if ch == 'm' {
                        break;
                    }
                }
            }
        } else {
            result.push(c);
        }
    }

    result
}

pub(crate) fn artifact_dir_for_test(path: &Path) -> PathBuf {
    // Strip absolute prefix (relative to CWD) so that PathBuf::join doesn't
    // discard "target/test-artifacts/" when given an absolute path.
    let path = if path.is_absolute() {
        std::env::current_dir()
            .ok()
            .and_then(|cwd| path.strip_prefix(&cwd).ok().map(|p| p.to_path_buf()))
            .unwrap_or_else(|| path.to_path_buf())
    } else {
        path.to_path_buf()
    };

    // Note: .replace("test/", "") is greedy — it also strips "test/" from
    // substrings (e.g. "contest/" → "con"). Pre-existing behavior, not changed.
    let relative = path
        .to_string_lossy()
        .replace("simple/std_lib/test/", "")
        .replace("test/", "")
        .replace("_spec.spl", "")
        .replace("_test.spl", "")
        .replace(".spl", "");
    PathBuf::from("build/test-artifacts").join(relative)
}

pub(crate) fn write_artifact_bundle(
    path: &Path,
    passed: usize,
    failed: usize,
    skipped: usize,
    ignored: usize,
    duration_ms: u64,
    error: Option<&str>,
    output: Option<&str>,
) {
    let dir = artifact_dir_for_test(path);
    if fs::create_dir_all(&dir).is_err() {
        return;
    }

    let mut summary = String::new();
    summary.push_str(&format!("spec: {}\n", path.display()));
    summary.push_str(&format!("passed: {}\n", passed));
    summary.push_str(&format!("failed: {}\n", failed));
    summary.push_str(&format!("skipped: {}\n", skipped));
    summary.push_str(&format!("ignored: {}\n", ignored));
    summary.push_str(&format!("duration_ms: {}\n", duration_ms));
    if let Some(err) = error {
        summary.push_str(&format!("error: {}\n", err));
    }
    let _ = fs::write(dir.join("summary.txt"), summary);

    if let Some(output) = output {
        let _ = fs::write(dir.join("output.log"), output);
    }
}

/// Run a single test file with options (wrapper for compatibility)
pub fn run_test_file_with_options(path: &Path, options: &super::types::TestOptions) -> TestFileResult {
    if options.safe_mode {
        run_test_file_safe_mode(path, options)
    } else {
        run_test_file(path, options)
    }
}

/// Run a single test file with a fresh Runner to prevent memory leaks.
///
/// Creates a new Runner per test so that the GC allocator, SmfLoader, and all
/// internal compiler state are dropped after each test. Combined with explicit
/// cleanup of thread-local registries, this prevents both inter-test accumulation
/// and intra-test leaks from persisting across test files.
pub fn run_test_file(path: &Path, options: &super::types::TestOptions) -> TestFileResult {
    let start = Instant::now();

    // Check RSS BEFORE starting the test. If memory is already above limit,
    // refuse to start another test to prevent OOM.
    let rss_before = get_rss_bytes();
    let mem_limit = memory_limit_bytes();
    if mem_limit > 0 && rss_before > mem_limit {
        eprintln!(
            "[ABORT] RSS {}MB already exceeds limit {}MB before starting {} — stopping test run",
            rss_before / (1024 * 1024),
            mem_limit / (1024 * 1024),
            path.display(),
        );
        return TestFileResult {
            path: path.to_path_buf(),
            passed: 0,
            failed: 1,
            skipped: 0,
            ignored: 0,
            duration_ms: 0,
            error: Some(format!(
                "MEMORY LIMIT ABORT: RSS {}MB exceeds {}MB limit before test start",
                rss_before / (1024 * 1024),
                mem_limit / (1024 * 1024),
            )),
            individual_results: vec![],
        };
    }

    // Enable stack overflow detection for tests even in release builds.
    // This catches infinite recursion before it overflows the OS stack.
    set_stack_overflow_detection_enabled(true);
    reset_recursion_depth();

    // Clear essential interpreter state to prevent leaks between tests.
    // Use selective module cache clear to preserve parsed stdlib modules
    // (std.spec, std.io, etc.) across tests — avoids re-parsing on every test.
    clear_interpreter_state();
    clear_bdd_state();
    clear_module_cache_selective();
    clear_class_instantiation_state();
    clear_macro_state();
    clear_effects_state();
    clear_io_state();
    clear_net_state();
    clear_all_runtime_registries();
    clear_collection_registries();
    clear_env_ffi_registry();
    clear_error_ffi_registry();
    clear_interp_ffi_state();
    clear_expr_registry();
    clear_thread_buffer_pool();
    clear_pinned_strings();
    clear_concurrency_registries();

    // Skip non-essential clears for interpreter-mode tests:
    // - clear_hir_thread_arena: HIR not used in interpreter path
    // - clear_mir_thread_arena: MIR not used in interpreter path
    // - clear_cranelift_registries: Cranelift not used in interpreter
    // - clear_compiled_functions: no compilation in interpreter
    // - clear_i18n_state: i18n state is idempotent across tests
    // - clear_ast_ffi_registries: AST FFI is internal, rarely leaks
    // - clear_span_ffi_registry: span tracking has negligible state
    // - clear_global_profiler: profiling disabled during tests
    // - clear_recording: recording disabled during tests

    // Force the system allocator to return freed memory to the OS.
    // Only do this every 50 tests to avoid per-test overhead (~1ms each).
    static TEST_COUNT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let count = TEST_COUNT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    #[cfg(target_os = "linux")]
    if count % 50 == 0 {
        unsafe {
            libc::malloc_trim(0);
        }
    }

    // Create a fresh Runner per test so ExecCore/GcAllocator/SmfLoader don't accumulate.
    let runner = create_test_runner(options);

    // Start per-test watchdog timer so infinite loops trigger TimeoutExceeded.
    let timeout_secs = per_test_timeout_secs(path);
    start_watchdog(timeout_secs);

    // catch_unwind catches panics (including stack overflows on some platforms)
    // so that a single crashing test doesn't abort the whole test suite.
    // Use run_file_interpreted() instead of run_file() because the default JIT
    // (Cranelift) crashes on some patterns (large functions with many var mutations
    // + string interpolation). The `run` command also uses interpreted mode for .spl files.
    let run_result: Result<i32, String> =
        match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| runner.run_file_interpreted(path))) {
            Ok(inner) => inner,
            Err(panic_info) => {
                let msg = if let Some(s) = panic_info.downcast_ref::<String>() {
                    s.clone()
                } else if let Some(s) = panic_info.downcast_ref::<&str>() {
                    s.to_string()
                } else {
                    "test panicked (possible stack overflow)".to_string()
                };
                Err(msg)
            }
        };

    // Stop watchdog and reset the timeout flag for the next test.
    stop_watchdog();
    reset_timeout();

    // Check RSS after the test. If memory grew beyond the limit, report the
    // test as an OOM failure. This prevents a single leaky test from bringing
    // down the whole test run.
    let rss_after = get_rss_bytes();
    let mem_limit = memory_limit_bytes();
    if rss_after > mem_limit {
        let duration_ms = start.elapsed().as_millis() as u64;
        eprintln!(
            "[WARN] RSS after test {} is {}MB (limit {}MB) — aborting test run",
            path.display(),
            rss_after / (1024 * 1024),
            mem_limit / (1024 * 1024),
        );
        return TestFileResult {
            path: path.to_path_buf(),
            passed: 0,
            failed: 1,
            skipped: 0,
            ignored: 0,
            duration_ms,
            error: Some(format!(
                "MEMORY LIMIT: RSS {}MB exceeds {}MB limit",
                rss_after / (1024 * 1024),
                mem_limit / (1024 * 1024),
            )),
            individual_results: vec![],
        };
    }

    match run_result {
        Ok(exit_code) => {
            let duration_ms = start.elapsed().as_millis() as u64;

            // Collect individual test results from the BDD framework
            let bdd_results = simple_compiler::interpreter::get_test_results();
            let individual_results: Vec<IndividualTestResult> = bdd_results
                .iter()
                .map(|(group, name, passed, skipped)| IndividualTestResult {
                    name: name.clone(),
                    group: group.clone(),
                    passed: *passed,
                    skipped: *skipped,
                })
                .collect();

            // Derive counts from individual results if available, otherwise fall back to exit code
            let (passed, failed, skipped) = if !individual_results.is_empty() {
                let p = individual_results.iter().filter(|r| r.passed && !r.skipped).count();
                let f = individual_results.iter().filter(|r| !r.passed).count();
                let s = individual_results.iter().filter(|r| r.skipped).count();
                (p, f, s)
            } else if exit_code == 0 {
                (1, 0, 0)
            } else {
                (0, 1, 0)
            };

            TestFileResult {
                path: path.to_path_buf(),
                passed,
                failed,
                skipped,
                ignored: 0,
                duration_ms,
                error: None,
                individual_results,
            }
        }
        Err(e) => {
            let duration_ms = start.elapsed().as_millis() as u64;
            let error_msg = e.to_string();

            // Detect timeout errors and provide a clear message.
            let is_timeout = error_msg.contains("timeout") || error_msg.contains("Timeout");
            let error_display = if is_timeout {
                format!("TIMEOUT after {}s: {}", timeout_secs, error_msg)
            } else {
                error_msg
            };

            TestFileResult {
                path: path.to_path_buf(),
                passed: 0,
                failed: 1,
                skipped: 0,
                ignored: 0,
                duration_ms,
                error: Some(error_display),
                individual_results: vec![],
            }
        }
    }
}

/// Run a single test file in a separate process with timeout (safe mode)
// TODO(bootstrap): For system tests, use simple_new (bin/wrappers/simple_new) to test
//                  the full Simple CLI stack once the self-hosting compiler is ready.
pub fn run_test_file_safe_mode(path: &Path, options: &super::types::TestOptions) -> TestFileResult {
    let start = Instant::now();

    // Find the simple binary path
    // TODO(bootstrap): Use simple_new for system tests (test/system/*) to verify full CLI
    let simple_binary = find_simple_binary();

    // Prepare environment variables
    let mut env_vars = Vec::new();

    // Check and propagate test mode environment variables
    if let Ok(mode) = std::env::var("SIMPLE_TEST_MODE") {
        env_vars.push(("SIMPLE_TEST_MODE", mode));
    }
    if let Ok(filter) = std::env::var("SIMPLE_TEST_FILTER") {
        env_vars.push(("SIMPLE_TEST_FILTER", filter));
    }
    if let Ok(show_tags) = std::env::var("SIMPLE_TEST_SHOW_TAGS") {
        env_vars.push(("SIMPLE_TEST_SHOW_TAGS", show_tags));
    }

    // Build command - run through test runner, not as direct script execution
    let mut cmd = Command::new(&simple_binary);
    cmd.args(build_safe_mode_child_args(path, options))
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());

    // Set environment variables
    for (key, val) in &env_vars {
        cmd.env(key, val);
    }

    // Spawn the process
    let child = match cmd.spawn() {
        Ok(child) => child,
        Err(e) => {
            return TestFileResult {
                path: path.to_path_buf(),
                passed: 0,
                failed: 1,
                skipped: 0,
                ignored: 0,
                duration_ms: start.elapsed().as_millis() as u64,
                error: Some(format!("Failed to spawn process: {}", e)),
                individual_results: vec![],
            };
        }
    };

    // Wait for process with timeout
    let timeout_duration = Duration::from_secs(options.safe_mode_timeout);
    let wait_result = wait_with_timeout(child, timeout_duration);

    let duration_ms = start.elapsed().as_millis() as u64;

    match wait_result {
        Ok((exit_code, stdout, stderr)) => {
            // Combine stdout and stderr for output parsing
            let combined_output = format!("{}\n{}", stdout, stderr);

            // Parse individual test results from BDD output
            let individual_results = parse_individual_results(&combined_output);

            // Derive counts from individual results if available
            let (passed, failed, skipped) = if !individual_results.is_empty() {
                let p = individual_results.iter().filter(|r| r.passed && !r.skipped).count();
                let f = individual_results.iter().filter(|r| !r.passed).count();
                let s = individual_results.iter().filter(|r| r.skipped).count();
                (p, f, s)
            } else {
                // Fall back to summary line parsing
                let (p, f) = parse_test_output(&combined_output);
                if p == 0 && f == 0 {
                    if exit_code == 0 {
                        (1, 0, 0)
                    } else {
                        (0, 1, 0)
                    }
                } else {
                    (p, f, 0)
                }
            };

            let result = TestFileResult {
                path: path.to_path_buf(),
                passed,
                failed,
                skipped,
                ignored: 0,
                duration_ms,
                error: if exit_code != 0 && failed == 0 {
                    Some(format!("Process exited with code {}", exit_code))
                } else {
                    None
                },
                individual_results,
            };
            emit_scenario_artifacts(path, &result);
            emit_test_artifacts(
                path,
                &result,
                ExecutionArtifacts {
                    stdout: Some(&stdout),
                    stderr: Some(&stderr),
                    combined: Some(&combined_output),
                    log_note: None,
                },
            );
            result
        }
        Err(e) => {
            let result = TestFileResult {
                path: path.to_path_buf(),
                passed: 0,
                failed: 1,
                skipped: 0,
                ignored: 0,
                duration_ms,
                error: Some(e),
                individual_results: vec![],
            };
            emit_scenario_artifacts(path, &result);
            emit_test_artifacts(path, &result, ExecutionArtifacts::none());
            result
        }
    }
}

fn build_safe_mode_child_args(path: &Path, options: &super::types::TestOptions) -> Vec<String> {
    let mut args = vec!["test".to_string(), path.display().to_string()];

    if let Some(mode) = options.execution_mode.cli_value() {
        args.push(format!("--mode={}", mode));
    }

    if options.gc_log {
        args.push("--gc-log".to_string());
    }
    if options.gc_off {
        args.push("--gc=off".to_string());
    }
    if options.only_slow {
        args.push("--only-slow".to_string());
    }
    if options.only_skipped {
        args.push("--only-skipped".to_string());
    }
    if options.show_tags {
        args.push("--show-tags".to_string());
    }
    if options.fail_fast {
        args.push("--fail-fast".to_string());
    }
    if let Some(tag) = &options.tag {
        args.push("--tag".to_string());
        args.push(tag.clone());
    }
    if let Some(seed) = options.seed {
        args.push("--seed".to_string());
        args.push(seed.to_string());
    }

    args
}

fn emit_test_artifacts(path: &Path, result: &TestFileResult, artifacts: ExecutionArtifacts<'_>) {
    if let Err(e) = write_test_artifacts(path, result, artifacts) {
        eprintln!("[WARN] Failed to write test artifacts for {}: {}", path.display(), e);
    }
}

fn emit_scenario_artifacts(path: &Path, result: &TestFileResult) {
    if result.individual_results.is_empty() {
        return;
    }

    if let Err(e) = write_scenario_manifest(path, &result.individual_results) {
        eprintln!(
            "[WARN] Failed to write scenario artifact manifest for {}: {}",
            path.display(),
            e
        );
    }
}

fn preprocess_sspec_for_smf(path: &Path) -> Result<PathBuf, String> {
    let path_str = path.to_string_lossy();
    if !path_str.ends_with("_spec.spl") {
        return Ok(path.to_path_buf());
    }

    let content = fs::read_to_string(path).map_err(|e| format!("Failed to read {}: {}", path.display(), e))?;

    let mut import_parts = Vec::<String>::new();
    let mut top_level_parts = Vec::<String>::new();
    let mut body_parts = Vec::<String>::new();
    let mut in_docstring = false;
    let mut in_top_fn = false;
    let mut top_fn_indent = 0usize;

    // Hoisting state: when we encounter a nested `class`/`impl`/`enum`/`type`
    // at indent > 0 inside what would otherwise be body content, we lift the
    // entire definition (dedented to column 0) up to module scope. This
    // works around the HIR's rule that classes/enums/types cannot appear as
    // statements in a function body.
    let mut in_hoisted_def = false;
    let mut hoist_indent = 0usize;
    let mut hoisted_buf: Vec<String> = Vec::new();
    // Names already hoisted (to detect collisions between two specs that
    // define the same class name in different `it` blocks). On collision we
    // skip hoisting the second occurrence and emit a warning comment.
    let mut hoisted_names: std::collections::HashSet<String> = std::collections::HashSet::new();

    fn extract_def_name(trimmed: &str) -> Option<String> {
        // "class Foo", "class Foo<T>", "class Foo(", "enum Bar:" etc.
        // Also "impl Foo" / "impl Trait for Foo" — for impl we use the
        // whole signature as the key so two `impl Trait for Foo` don't
        // false-positive collide with two distinct `impl Foo` blocks; the
        // detector is best-effort.
        let rest = trimmed
            .split_once(' ')
            .map(|(_, r)| r)
            .unwrap_or(trimmed);
        let name: String = rest
            .chars()
            .take_while(|c| c.is_alphanumeric() || *c == '_')
            .collect();
        if name.is_empty() { None } else { Some(name) }
    }
    fn is_hoistable_keyword(trimmed: &str) -> bool {
        trimmed.starts_with("class ")
            || trimmed.starts_with("impl ")
            || trimmed.starts_with("enum ")
            || trimmed.starts_with("type ")
    }

    let flush_hoisted =
        |buf: &mut Vec<String>, top: &mut Vec<String>, indent: usize| {
            if buf.is_empty() {
                return;
            }
            for raw in buf.drain(..) {
                if raw.trim().is_empty() {
                    top.push(String::new());
                    continue;
                }
                // Strip up to `indent` leading spaces so the hoisted block
                // sits at column 0 at module scope.
                let mut stripped = 0usize;
                let bytes = raw.as_bytes();
                while stripped < indent && stripped < bytes.len() && bytes[stripped] == b' ' {
                    stripped += 1;
                }
                top.push(raw[stripped..].to_string());
            }
            top.push(String::new());
        };

    for line in content.lines() {
        let trimmed = line.trim();

        if trimmed.starts_with("\"\"\"") {
            in_docstring = !in_docstring;
            if in_top_fn {
                top_level_parts.push(line.to_string());
            } else if in_hoisted_def {
                hoisted_buf.push(line.to_string());
            } else {
                body_parts.push(format!("    {}", line));
            }
            continue;
        }

        if in_docstring {
            if in_top_fn {
                top_level_parts.push(line.to_string());
            } else if in_hoisted_def {
                hoisted_buf.push(line.to_string());
            } else {
                body_parts.push(format!("    {}", line));
            }
            continue;
        }

        if trimmed.starts_with("import ") || trimmed.starts_with("use ") {
            import_parts.push(line.to_string());
            continue;
        }

        // Check if this line starts a new top-level def at indent 0.
        // Includes fn/async fn/static fn AND class/impl/enum/trait/type/val/let/mod
        // so their (indented) bodies are preserved at module scope rather than
        // swept into `fn main()`.
        let line_indent = line.len().saturating_sub(trimmed.len());
        let starts_top_level = line_indent == 0
            && (trimmed.starts_with("fn ")
                || trimmed.starts_with("async fn ")
                || trimmed.starts_with("static fn ")
                || trimmed.starts_with("class ")
                || trimmed.starts_with("impl ")
                || trimmed.starts_with("enum ")
                || trimmed.starts_with("trait ")
                || trimmed.starts_with("type ")
                || trimmed.starts_with("val ")
                || trimmed.starts_with("let ")
                || trimmed.starts_with("mod "));

        if in_top_fn {
            if trimmed.is_empty() {
                top_level_parts.push(String::new());
                continue;
            }
            let current_indent = line.len().saturating_sub(trimmed.len());
            if current_indent > top_fn_indent {
                top_level_parts.push(line.to_string());
                continue;
            }
            in_top_fn = false;
            // Fall through so this line gets classified for itself.
        }

        // If we are currently accumulating a hoisted nested def, keep
        // consuming lines until indentation drops back to <= hoist_indent
        // (and is non-empty). Blank lines are kept inside the hoisted block.
        if in_hoisted_def {
            if trimmed.is_empty() {
                hoisted_buf.push(line.to_string());
                continue;
            }
            let cur = line.len().saturating_sub(trimmed.len());
            if cur > hoist_indent {
                hoisted_buf.push(line.to_string());
                continue;
            }
            // End of nested def — flush and fall through to classify the
            // current line normally.
            flush_hoisted(&mut hoisted_buf, &mut top_level_parts, hoist_indent);
            in_hoisted_def = false;
        }

        if starts_top_level {
            in_top_fn = true;
            top_fn_indent = 0;
            top_level_parts.push(line.to_string());
            continue;
        }

        // Detect a nested hoistable definition: `class `/`impl `/`enum `/`type `
        // at indent > 0. If the name was already hoisted, leave the block
        // in the body (prefixed with a warning comment) — this will still
        // fail compile, but matches option (b) in the spec.
        if line_indent > 0 && is_hoistable_keyword(trimmed) {
            let name = extract_def_name(trimmed).unwrap_or_default();
            let key = format!("{}::{}", trimmed.split_whitespace().next().unwrap_or(""), name);
            if !name.is_empty() && hoisted_names.insert(key) {
                in_hoisted_def = true;
                hoist_indent = line_indent;
                hoisted_buf.clear();
                hoisted_buf.push(line.to_string());
                // Leave a placeholder comment in the body so the reader can
                // still see where the class was defined originally.
                body_parts.push(format!(
                    "    # (hoisted nested def `{}` to module scope)",
                    trimmed
                ));
                continue;
            } else {
                body_parts.push(format!(
                    "    # WARNING: duplicate nested def `{}` not hoisted (name collision)",
                    trimmed
                ));
                // Fall through and keep line in body as-is.
            }
        }

        if trimmed.is_empty() {
            body_parts.push(String::new());
        } else {
            body_parts.push(format!("    {}", line));
        }
    }

    // Flush any trailing hoisted block (file ends inside a nested def).
    if in_hoisted_def {
        flush_hoisted(&mut hoisted_buf, &mut top_level_parts, hoist_indent);
    }

    // Specs usually rely on the `describe`/`it`/`context`/`skip`/`expect` DSL
    // being implicitly in scope (interpreter mode makes them builtins). For
    // compile modes the symbols must be imported explicitly, so inject
    // `use std.spec` unless the user already imported it.
    let needs_spec_import = !import_parts
        .iter()
        .any(|line| line.trim_start().starts_with("use std.spec"));
    if needs_spec_import {
        import_parts.insert(0, "use std.spec".to_string());
    }

    let wrapped = format!(
        "#![allow(sspec_empty_examples)]\n#![allow(sspec_boolean_wrapper_assertions)]\n@allow(sspec_empty_examples)\n@allow(sspec_boolean_wrapper_assertions)\n{}\n\n{}\nfn main():\n{}",
        import_parts.join("\n"),
        top_level_parts.join("\n"),
        body_parts.join("\n")
    );
    let file_name = path
        .file_name()
        .and_then(|name| name.to_str())
        .unwrap_or("wrapped_spec.spl");
    let tmp_path = path
        .parent()
        .unwrap_or_else(|| Path::new("."))
        .join(format!(".sspec_wrapped_entry_{}", file_name));
    fs::write(&tmp_path, wrapped).map_err(|e| format!("Failed to write {}: {}", tmp_path.display(), e))?;
    Ok(tmp_path)
}

fn existing_dependency_smf_path(dep_source: &Path) -> Option<PathBuf> {
    let _ = dep_source;
    None
}

/// Find the simple binary path.
///
/// Prefers the current executable so child subprocesses use the same binary
/// as the parent (ensuring consistent behavior and fixes).
fn find_simple_binary() -> PathBuf {
    // Prefer the current executable — ensures child uses the same binary as parent
    if let Ok(exe) = std::env::current_exe() {
        if exe.exists() {
            return exe;
        }
    }

    // Fallback: try common locations, preferring local bin/simple and
    // platform-specific release layouts before the flat legacy path.
    let candidates = simple_binary_candidates();

    for candidate in candidates {
        if candidate.exists() {
            return candidate;
        }
    }

    PathBuf::from("./target/debug/simple")
}

fn simple_binary_candidates() -> Vec<PathBuf> {
    let mut candidates = repo_rust_binary_candidates();
    candidates.push(PathBuf::from("./bin/simple"));

    candidates.extend(platform_release_binary_candidates());
    candidates.push(PathBuf::from("./bin/wrappers/simple"));
    candidates.extend(local_rust_binary_candidates());
    candidates.push(PathBuf::from("simple"));
    candidates
}

fn repo_rust_binary_candidates() -> Vec<PathBuf> {
    if cfg!(target_os = "windows") {
        vec![
            PathBuf::from("./src/compiler_rust/target/release/simple.exe"),
            PathBuf::from("./src/compiler_rust/target/bootstrap/simple.exe"),
        ]
    } else {
        vec![
            PathBuf::from("./src/compiler_rust/target/release/simple"),
            PathBuf::from("./src/compiler_rust/target/bootstrap/simple"),
        ]
    }
}

fn local_rust_binary_candidates() -> Vec<PathBuf> {
    if cfg!(target_os = "windows") {
        vec![
            PathBuf::from("./target/bootstrap/simple.exe"),
            PathBuf::from("./target/release/simple.exe"),
            PathBuf::from("./target/debug/simple.exe"),
        ]
    } else {
        vec![
            PathBuf::from("./target/bootstrap/simple"),
            PathBuf::from("./target/release/simple"),
            PathBuf::from("./target/debug/simple"),
        ]
    }
}

fn platform_release_binary_candidates() -> Vec<PathBuf> {
    let mut candidates = Vec::new();

    if cfg!(target_os = "windows") {
        if cfg!(target_arch = "x86_64") {
            candidates.push(PathBuf::from("./bin/release/x86_64-pc-windows-msvc/simple.exe"));
            candidates.push(PathBuf::from("./bin/release/x86_64-pc-windows-gnu/simple.exe"));
        }
        if cfg!(target_arch = "aarch64") {
            candidates.push(PathBuf::from("./bin/release/aarch64-pc-windows-msvc/simple.exe"));
            candidates.push(PathBuf::from("./bin/release/aarch64-pc-windows-gnu/simple.exe"));
        }
    } else if cfg!(target_os = "macos") {
        if cfg!(target_arch = "aarch64") {
            candidates.push(PathBuf::from("./bin/release/aarch64-apple-darwin-macho/simple"));
            candidates.push(PathBuf::from("./bin/release/macos-arm64/simple"));
            candidates.push(PathBuf::from("./bin/release/darwin-aarch64/simple"));
        }
        if cfg!(target_arch = "x86_64") {
            candidates.push(PathBuf::from("./bin/release/macos-x86_64/simple"));
            candidates.push(PathBuf::from("./bin/release/darwin-x86_64/simple"));
        }
    } else if cfg!(target_os = "linux") {
        if cfg!(target_arch = "x86_64") {
            candidates.push(PathBuf::from("./bin/release/linux-x86_64/simple"));
            candidates.push(PathBuf::from("./bin/release/x86_64-unknown-linux-gnu/simple"));
        }
        if cfg!(target_arch = "aarch64") {
            candidates.push(PathBuf::from("./bin/release/linux-aarch64/simple"));
            candidates.push(PathBuf::from("./bin/release/aarch64-unknown-linux-gnu/simple"));
        }
    }

    candidates
}

/// Wait for a process with timeout
///
/// Spawns a thread to wait for the child process and uses a channel with timeout.
/// The thread is properly joined on success, and on timeout the process is killed
/// (which will cause the thread to exit when the child terminates).
fn wait_with_timeout(mut child: std::process::Child, timeout: Duration) -> Result<(i32, String, String), String> {
    use std::thread;
    use std::sync::mpsc;

    let (tx, rx) = mpsc::channel();
    let child_id = child.id();

    // Spawn a thread to wait for the child
    // Thread lifecycle:
    // - On success: joined below after receiving result
    // - On timeout: child is killed, thread will exit when wait_with_output returns
    let handle = thread::spawn(move || {
        let output = child.wait_with_output();
        let _ = tx.send(output);
    });

    // Wait for the result with timeout
    match rx.recv_timeout(timeout) {
        Ok(Ok(output)) => {
            // Clean up the thread - it should exit quickly since we have the output
            let _ = handle.join();
            let exit_code = output.status.code().unwrap_or(-1);
            let stdout = String::from_utf8_lossy(&output.stdout).to_string();
            let stderr = String::from_utf8_lossy(&output.stderr).to_string();
            Ok((exit_code, stdout, stderr))
        }
        Ok(Err(e)) => {
            // Process failed - thread should exit, try to join
            let _ = handle.join();
            Err(format!("Process failed: {}", e))
        }
        Err(_) => {
            // Timeout - kill the process
            // The thread will exit when the killed child's wait_with_output returns
            #[cfg(unix)]
            {
                use std::process::Command as StdCommand;
                let _ = StdCommand::new("kill").arg("-9").arg(child_id.to_string()).status();
            }

            #[cfg(windows)]
            {
                use std::process::Command as StdCommand;
                let _ = StdCommand::new("taskkill")
                    .args(&["/F", "/PID", &child_id.to_string()])
                    .status();
            }

            // Wait briefly for thread to notice the killed process and exit
            // Don't block forever - if the thread doesn't exit quickly, let it go
            let start = std::time::Instant::now();
            while !handle.is_finished() && start.elapsed() < Duration::from_millis(500) {
                thread::sleep(Duration::from_millis(10));
            }
            if handle.is_finished() {
                let _ = handle.join();
            }

            Err(format!("Test timed out after {} seconds", timeout.as_secs()))
        }
    }
}

/// Run a single test file in SMF loader mode.
///
/// This is a real SMF path: preprocess spec files into an executable wrapper,
/// compile that source to a cached `.smf` artifact through the CLI, then
/// execute the resulting artifact directly.
pub fn run_test_file_smf_mode(path: &Path, cache: &BuildCache, options: &super::types::TestOptions) -> TestFileResult {
    let start = Instant::now();
    let source_path = match preprocess_sspec_for_smf(path) {
        Ok(path) => path,
        Err(err) => {
            return TestFileResult {
                path: path.to_path_buf(),
                passed: 0,
                failed: 1,
                skipped: 0,
                ignored: 0,
                duration_ms: start.elapsed().as_millis() as u64,
                error: Some(err),
                individual_results: vec![],
            };
        }
    };

    let smf_path = match cache.smf_artifact_path(&source_path) {
        Ok(path) => path,
        Err(err) => {
            return TestFileResult {
                path: path.to_path_buf(),
                passed: 0,
                failed: 1,
                skipped: 0,
                ignored: 0,
                duration_ms: start.elapsed().as_millis() as u64,
                error: Some(err),
                individual_results: vec![],
            };
        }
    };

    let dependency_sources = match collect_imported_module_paths(&source_path) {
        Ok(paths) => paths,
        Err(err) => {
            return TestFileResult {
                path: path.to_path_buf(),
                passed: 0,
                failed: 1,
                skipped: 0,
                ignored: 0,
                duration_ms: start.elapsed().as_millis() as u64,
                error: Some(format!("Failed to resolve SMF dependencies: {}", err)),
                individual_results: vec![],
            };
        }
    };

    let compile_runner = create_test_runner(options);
    let compile_options = crate::CompileOptions::default();
    let mut dependency_artifacts = Vec::new();

    for dep_source in &dependency_sources {
        if let Some(existing_smf) = existing_dependency_smf_path(dep_source) {
            dependency_artifacts.push(existing_smf);
            continue;
        }
        let dep_smf = match cache.smf_artifact_path(dep_source) {
            Ok(path) => path,
            Err(err) => {
                return TestFileResult {
                    path: path.to_path_buf(),
                    passed: 0,
                    failed: 1,
                    skipped: 0,
                    ignored: 0,
                    duration_ms: start.elapsed().as_millis() as u64,
                    error: Some(err),
                    individual_results: vec![],
                };
            }
        };
        if cache.needs_rebuild(dep_source, "smf") {
            if let Err(err) = compile_runner.compile_file_to_smf_with_options(dep_source, &dep_smf, &compile_options) {
                return TestFileResult {
                    path: path.to_path_buf(),
                    passed: 0,
                    failed: 1,
                    skipped: 0,
                    ignored: 0,
                    duration_ms: start.elapsed().as_millis() as u64,
                    error: Some(format!(
                        "Failed to compile dependency {} to SMF: {}",
                        dep_source.display(),
                        err
                    )),
                    individual_results: vec![],
                };
            }
        }
        dependency_artifacts.push(dep_smf);
    }

    if cache.needs_rebuild(&source_path, "smf") {
        if let Err(err) = compile_runner.compile_file_to_smf_with_options(&source_path, &smf_path, &compile_options) {
            return TestFileResult {
                path: path.to_path_buf(),
                passed: 0,
                failed: 1,
                skipped: 0,
                ignored: 0,
                duration_ms: start.elapsed().as_millis() as u64,
                error: Some(format!("Failed to compile {} to SMF: {}", source_path.display(), err)),
                individual_results: vec![],
            };
        }
    }

    rt_capture_stdout_start();
    rt_capture_stderr_start();
    rt_set_args_vec(&[]);

    let provider = default_runtime_provider();
    let registry = ModuleRegistry::new();
    let run_result: Result<i32, String> = (|| {
        for dep in &dependency_artifacts {
            registry
                .load_with_fallback(dep, |name| provider.get_symbol(name).map(|ptr| ptr as usize))
                .map_err(|e| format!("SMF dependency load failed ({}): {}", dep.display(), e))?;
        }
        let module = registry
            .load_with_fallback(&smf_path, |name| provider.get_symbol(name).map(|ptr| ptr as usize))
            .map_err(|e| format!("SMF load failed ({}): {}", smf_path.display(), e))?;
        run_main(&module)
    })();
    let captured_stdout = rt_capture_stdout_stop();
    let captured_stderr = rt_capture_stderr_stop();
    let wait_result: Result<(i32, String, String), String> =
        run_result.map(|exit_code| (exit_code, captured_stdout, captured_stderr));
    let duration_ms = start.elapsed().as_millis() as u64;

    match wait_result {
        Ok((exit_code, stdout, stderr)) => {
            let combined_output = format!("{}\n{}", stdout, stderr);
            let individual_results = parse_individual_results(&combined_output);
            let (passed, failed, skipped) = if !individual_results.is_empty() {
                let p = individual_results.iter().filter(|r| r.passed && !r.skipped).count();
                let f = individual_results.iter().filter(|r| !r.passed).count();
                let s = individual_results.iter().filter(|r| r.skipped).count();
                (p, f, s)
            } else {
                let (p, f) = parse_test_output(&combined_output);
                if p == 0 && f == 0 {
                    if exit_code == 0 {
                        (1, 0, 0)
                    } else {
                        (0, 1, 0)
                    }
                } else {
                    (p, f, 0)
                }
            };

            let result = TestFileResult {
                path: path.to_path_buf(),
                passed,
                failed,
                skipped,
                ignored: 0,
                duration_ms,
                error: if exit_code != 0 && failed == 0 {
                    Some(format!("Process exited with code {}", exit_code))
                } else {
                    None
                },
                individual_results,
            };
            emit_scenario_artifacts(path, &result);
            emit_test_artifacts(
                path,
                &result,
                ExecutionArtifacts {
                    stdout: Some(&stdout),
                    stderr: Some(&stderr),
                    combined: Some(&combined_output),
                    log_note: Some("Executed via SMF artifact"),
                },
            );
            result
        }
        Err(e) => {
            let result = TestFileResult {
                path: path.to_path_buf(),
                passed: 0,
                failed: 1,
                skipped: 0,
                ignored: 0,
                duration_ms,
                error: Some(e),
                individual_results: vec![],
            };
            emit_scenario_artifacts(path, &result);
            emit_test_artifacts(path, &result, ExecutionArtifacts::none());
            result
        }
    }
}

/// Run a single test file in native binary mode.
///
/// Preprocesses `*_spec.spl` into a wrapped `fn main()` source, compiles to
/// a cached native ELF, and runs the ELF as a subprocess. `it` block bodies
/// actually execute (unlike interpreter-in-subprocess safe mode).
pub fn run_test_file_native_mode(
    path: &Path,
    cache: &BuildCache,
    options: &super::types::TestOptions,
) -> TestFileResult {
    let start = Instant::now();

    let source_path = match preprocess_sspec_for_smf(path) {
        Ok(p) => p,
        Err(err) => {
            return TestFileResult {
                path: path.to_path_buf(),
                passed: 0,
                failed: 1,
                skipped: 0,
                ignored: 0,
                duration_ms: start.elapsed().as_millis() as u64,
                error: Some(err),
                individual_results: vec![],
            };
        }
    };

    let elf_path = match cache.compile_test_to_native(&source_path) {
        Ok(p) => p,
        Err(err) => {
            let duration_ms = start.elapsed().as_millis() as u64;
            return TestFileResult {
                path: path.to_path_buf(),
                passed: 0,
                failed: 1,
                skipped: 0,
                ignored: 0,
                duration_ms,
                error: Some(format!(
                    "Failed to compile {} to native ELF: {}",
                    source_path.display(),
                    err
                )),
                individual_results: vec![],
            };
        }
    };

    let mut cmd = Command::new(&elf_path);
    cmd.stdout(Stdio::piped()).stderr(Stdio::piped());

    let child = match cmd.spawn() {
        Ok(c) => c,
        Err(e) => {
            return TestFileResult {
                path: path.to_path_buf(),
                passed: 0,
                failed: 1,
                skipped: 0,
                ignored: 0,
                duration_ms: start.elapsed().as_millis() as u64,
                error: Some(format!(
                    "Failed to spawn native test ELF {}: {}",
                    elf_path.display(),
                    e
                )),
                individual_results: vec![],
            };
        }
    };

    let timeout_duration = Duration::from_secs(options.safe_mode_timeout);
    let wait_result = wait_with_timeout(child, timeout_duration);
    let duration_ms = start.elapsed().as_millis() as u64;

    match wait_result {
        Ok((exit_code, stdout, stderr)) => {
            let combined_output = format!("{}\n{}", stdout, stderr);
            let individual_results = parse_individual_results(&combined_output);
            let (passed, failed, skipped) = if !individual_results.is_empty() {
                let p = individual_results.iter().filter(|r| r.passed && !r.skipped).count();
                let f = individual_results.iter().filter(|r| !r.passed).count();
                let s = individual_results.iter().filter(|r| r.skipped).count();
                (p, f, s)
            } else {
                let (p, f) = parse_test_output(&combined_output);
                if p == 0 && f == 0 {
                    if exit_code == 0 {
                        (1, 0, 0)
                    } else {
                        (0, 1, 0)
                    }
                } else {
                    (p, f, 0)
                }
            };

            let result = TestFileResult {
                path: path.to_path_buf(),
                passed,
                failed,
                skipped,
                ignored: 0,
                duration_ms,
                error: if exit_code != 0 && failed == 0 {
                    Some(format!("Process exited with code {}", exit_code))
                } else {
                    None
                },
                individual_results,
            };
            emit_scenario_artifacts(path, &result);
            emit_test_artifacts(
                path,
                &result,
                ExecutionArtifacts {
                    stdout: Some(&stdout),
                    stderr: Some(&stderr),
                    combined: Some(&combined_output),
                    log_note: Some("Executed via native ELF"),
                },
            );
            result
        }
        Err(e) => {
            let result = TestFileResult {
                path: path.to_path_buf(),
                passed: 0,
                failed: 1,
                skipped: 0,
                ignored: 0,
                duration_ms,
                error: Some(e),
                individual_results: vec![],
            };
            emit_scenario_artifacts(path, &result);
            emit_test_artifacts(path, &result, ExecutionArtifacts::none());
            result
        }
    }
}

/// Create a Runner for test execution with appropriate GC settings.
fn create_test_runner(options: &super::types::TestOptions) -> Runner {
    if options.gc_off {
        Runner::new_no_gc()
    } else if options.gc_log {
        Runner::new_with_gc_logging()
    } else {
        Runner::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::path::PathBuf;
    use std::sync::{Mutex, OnceLock};

    use tempfile::tempdir;

    fn cwd_lock() -> &'static Mutex<()> {
        static LOCK: OnceLock<Mutex<()>> = OnceLock::new();
        LOCK.get_or_init(|| Mutex::new(()))
    }

    struct CurrentDirGuard {
        previous: PathBuf,
    }

    impl Drop for CurrentDirGuard {
        fn drop(&mut self) {
            let _ = std::env::set_current_dir(&self.previous);
        }
    }

    fn with_temp_cwd() -> (tempfile::TempDir, CurrentDirGuard) {
        let tempdir = tempdir().expect("tempdir");
        let previous = std::env::current_dir().expect("current dir");
        std::env::set_current_dir(tempdir.path()).expect("set current dir");
        (tempdir, CurrentDirGuard { previous })
    }

    #[test]
    fn test_parse_test_output_basic() {
        let output = "5 examples, 2 failures";
        let (passed, failed) = parse_test_output(output);
        assert_eq!(passed, 3);
        assert_eq!(failed, 2);
    }

    #[test]
    fn test_parse_test_output_all_pass() {
        let output = "10 examples, 0 failures";
        let (passed, failed) = parse_test_output(output);
        assert_eq!(passed, 10);
        assert_eq!(failed, 0);
    }

    #[test]
    fn test_parse_test_output_no_match() {
        let output = "random text";
        let (passed, failed) = parse_test_output(output);
        assert_eq!(passed, 0);
        assert_eq!(failed, 0);
    }

    #[test]
    fn test_parse_test_output_multiple_blocks() {
        // Multiple describe blocks each output "X examples, Y failures"
        let output = "3 examples, 0 failures\n4 examples, 1 failures\n3 examples, 0 failures";
        let (passed, failed) = parse_test_output(output);
        assert_eq!(passed, 9); // 3 + 3 + 3
        assert_eq!(failed, 1);
    }

    #[test]
    fn test_parse_test_output_with_ansi_codes() {
        // Output with ANSI color codes (green for success)
        let output = "\x1b[32m2 examples, 0 failures\x1b[0m";
        let (passed, failed) = parse_test_output(output);
        assert_eq!(passed, 2);
        assert_eq!(failed, 0);
    }

    #[test]
    fn test_strip_ansi_codes() {
        assert_eq!(strip_ansi_codes("\x1b[32mhello\x1b[0m"), "hello");
        assert_eq!(strip_ansi_codes("no codes"), "no codes");
        assert_eq!(strip_ansi_codes("\x1b[1;31mred\x1b[0m"), "red");
    }

    #[test]
    fn test_build_safe_mode_child_args_forwards_composite_mode() {
        let options = super::super::types::TestOptions {
            execution_mode: TestExecutionMode::Composite("interpreter(remote(baremetal(riscv32)))".to_string()),
            ..Default::default()
        };

        let args = build_safe_mode_child_args(Path::new("test/example_spec.spl"), &options);

        assert!(args
            .iter()
            .any(|arg| arg == "--mode=interpreter(remote(baremetal(riscv32)))"));
    }

    #[test]
    fn test_write_artifact_bundle_writes_summary_and_output_log() {
        let _guard = cwd_lock().lock().expect("lock cwd");
        let (_tempdir, _cwd_guard) = with_temp_cwd();

        let spec_path = Path::new("test/unit/app/tooling/test_runner_simple_spec.spl");
        write_artifact_bundle(spec_path, 3, 1, 2, 0, 42, Some("boom"), Some("combined runner output"));

        let artifact_dir = artifact_dir_for_test(spec_path);
        let summary = fs::read_to_string(artifact_dir.join("summary.txt")).expect("summary");
        let output = fs::read_to_string(artifact_dir.join("output.log")).expect("output");

        assert!(summary.contains("spec: test/unit/app/tooling/test_runner_simple_spec.spl"));
        assert!(summary.contains("passed: 3"));
        assert!(summary.contains("failed: 1"));
        assert!(summary.contains("skipped: 2"));
        assert!(summary.contains("duration_ms: 42"));
        assert!(summary.contains("error: boom"));
        assert!(summary.contains("Individual Results:"));
        assert_eq!(output, "combined runner output");
    }
}
