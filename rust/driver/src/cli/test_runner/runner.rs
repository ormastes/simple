//! Main test runner implementation.
//!
//! Orchestrates test discovery, execution, and reporting.

use std::fs;
use std::path::PathBuf;
use std::time::Instant;

use simple_compiler::{init_coverage, is_coverage_enabled};

use crate::runner::Runner;
use super::test_discovery::{discover_tests_with_skip, is_skip_test_file, matches_tag};
use super::types::{
    TestFileResult, TestExecutionMode, TestLevel, TestOptions, TestRunResult, OutputFormat, DebugLevel, debug_log,
};
use super::build_cache::BuildCache;
use super::execution::run_test_file;
use super::doctest::{run_doctests, run_md_doctests};
use super::parallel::run_tests_parallel;
use super::diagrams::generate_test_diagrams;
use super::discovery::print_discovery_summary;
use super::coverage::save_coverage_data;
use super::feature_db::update_feature_database;
use super::test_db_update::{update_test_database, update_rust_test_database};
use super::static_registry::StaticTestRegistry;
use super::rust_tests;

/// Load resource throttle configuration from simple.test.toml
fn load_resource_throttle_config(options: &mut TestOptions) {
    // Find simple.test.toml in current directory or project root
    let config_paths = [
        PathBuf::from("simple.test.toml"),
        PathBuf::from("../simple.test.toml"),
        PathBuf::from("../../simple.test.toml"),
    ];

    for path in &config_paths {
        if let Ok(content) = fs::read_to_string(path) {
            parse_resource_throttle_config(&content, options);
            debug_log!(DebugLevel::Detailed, "Config", "Loaded config from: {}", path.display());
            return;
        }
    }

    debug_log!(DebugLevel::Trace, "Config", "No simple.test.toml found, using defaults");
}

/// Parse resource throttle configuration from TOML content
fn parse_resource_throttle_config(content: &str, options: &mut TestOptions) {
    // Simple TOML parsing for cpu_throttle section (handles both CPU and memory thresholds)
    let mut in_cpu_throttle = false;

    for line in content.lines() {
        let line = line.trim();

        if line == "[test.cpu_throttle]" {
            in_cpu_throttle = true;
            continue;
        }

        if line.starts_with('[') {
            in_cpu_throttle = false;
            continue;
        }

        if !in_cpu_throttle {
            continue;
        }

        // Parse key = value pairs
        if let Some((key, value)) = line.split_once('=') {
            let key = key.trim();
            let value = value.trim().trim_matches(|c| c == '"' || c == '\'');

            match key {
                // Note: "enabled" in config does NOT auto-enable parallel mode.
                // Parallel execution always requires explicit --parallel or -p CLI flag.
                // Config file only overrides thresholds and other settings.
                "enabled" => {
                    // Intentionally ignored - parallel must be enabled via CLI
                }
                "threshold" => {
                    if let Ok(v) = value.parse::<u8>() {
                        // Only apply if user didn't override on CLI (still default)
                        if options.cpu_threshold == 70 {
                            options.cpu_threshold = v;
                        }
                    }
                }
                "memory_threshold" => {
                    if let Ok(v) = value.parse::<u8>() {
                        // Only apply if user didn't override on CLI (still default)
                        if options.memory_threshold == 70 {
                            options.memory_threshold = v;
                        }
                    }
                }
                "throttled_threads" => {
                    if let Ok(v) = value.parse::<usize>() {
                        if options.throttled_threads == 1 {
                            options.throttled_threads = v;
                        }
                    }
                }
                "check_interval" => {
                    if let Ok(v) = value.parse::<u64>() {
                        if options.cpu_check_interval == 5 {
                            options.cpu_check_interval = v;
                        }
                    }
                }
                _ => {}
            }
        }
    }
}

/// Run tests with the given options
pub fn run_tests(options: TestOptions) -> TestRunResult {
    // Make options mutable to apply config file settings
    let mut options = options;

    // Handle run management commands (--list-runs, --cleanup-runs, --prune-runs)
    if options.list_runs || options.cleanup_runs || options.prune_runs.is_some() {
        return handle_run_management(&options);
    }

    // Load configuration from simple.test.toml (applies defaults if not overridden by CLI)
    if options.parallel {
        load_resource_throttle_config(&mut options);
    }

    let quiet = matches!(options.format, OutputFormat::Json);
    let list_mode = options.list || options.list_ignored;

    // Discover test files first (needed for both static and runtime modes)
    let test_path = determine_test_path(&options);
    let test_files = discover_and_filter_tests(&test_path, &options);

    // Handle --list-skip-features: show features from .skip files
    if options.list_skip_features {
        return run_list_skip_features(&test_files, options.skip_features_planned_only, quiet);
    }

    // FAST PATH: Use static analysis for list mode (no DSL execution)
    if list_mode {
        return run_list_mode_static(&test_files, &options, quiet);
    }

    // CRITICAL: Set environment variables BEFORE creating runner/interpreter
    // This ensures the Simple spec framework sees them when it loads
    std::env::remove_var("SIMPLE_TEST_MODE");

    if options.only_slow {
        std::env::set_var("SIMPLE_TEST_FILTER", "slow");
    } else if options.only_skipped {
        std::env::set_var("SIMPLE_TEST_FILTER", "skipped");
    } else {
        std::env::remove_var("SIMPLE_TEST_FILTER");
    }

    if options.show_tags {
        std::env::set_var("SIMPLE_TEST_SHOW_TAGS", "1");
    } else {
        std::env::remove_var("SIMPLE_TEST_SHOW_TAGS");
    }

    // Initialize for test execution
    initialize_diagrams(&options, quiet);
    initialize_profiling(&options, quiet);
    initialize_coverage(quiet);

    // Skip runner creation in safe mode (each subprocess creates its own)
    let runner = if !options.safe_mode {
        Some(create_runner(&options))
    } else {
        None
    };

    // Print discovery summary
    print_discovery_summary(&test_files, &options, quiet);

    // Start test run tracking
    let db_path = PathBuf::from("doc/test/test_db.sdn");
    let test_run = match crate::test_db::start_test_run(&db_path) {
        Ok(run) => {
            if !quiet {
                debug_log!(DebugLevel::Basic, "Runner", "Started test run: {}", run.run_id);
            }
            Some(run)
        }
        Err(e) => {
            if !quiet {
                eprintln!("Note: Test run tracking disabled ({})", e);
            }
            None
        }
    };

    // Create build cache for SMF/native modes
    let build_cache = if options.execution_mode != TestExecutionMode::Interpreter {
        Some(BuildCache::new(options.force_rebuild))
    } else {
        None
    };

    if options.execution_mode != TestExecutionMode::Interpreter && !quiet {
        println!("Execution mode: {}", options.execution_mode.name());
    }

    // Execute tests
    // Default: Sequential (single-threaded) execution
    // Parallel: Only when --parallel or -p flag is explicitly passed
    let (mut results, mut total_passed, mut total_failed, mut total_skipped, mut total_ignored) =
        if options.parallel && options.safe_mode {
            // Parallel execution (optional, requires --parallel flag)
            debug_log!(DebugLevel::Basic, "Runner", "Using parallel execution mode");
            run_tests_parallel(&test_files, &options, quiet)
        } else {
            // Sequential execution (default - single-threaded)
            execute_test_files(runner.as_ref(), &test_files, &options, build_cache.as_ref(), quiet)
        };

    // Determine if all tests were run (no filters applied)
    let all_tests_run =
        options.path.is_none() && options.tag.is_none() && options.level == TestLevel::All && !list_mode;

    // Skip database updates in list mode
    if !list_mode {
        // Update feature database
        update_feature_database(&test_files, &mut results, &mut total_failed);

        // Update test database
        if let Err(e) = update_test_database(&test_files, &results, all_tests_run) {
            if !quiet {
                eprintln!("Warning: Failed to update test database: {}", e);
            }
        }

        // Run Rust tests if enabled
        if options.rust_tests {
            let cwd = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
            if !quiet {
                if options.rust_ignored_only {
                    println!("\nTracking ignored Rust tests...");
                } else {
                    println!("\nRunning Rust tests...");
                }
            }

            let rust_results = if options.rust_ignored_only {
                // Just list ignored tests for database tracking
                let ignored = rust_tests::list_ignored_rust_tests(&cwd);
                if !quiet {
                    println!("Found {} ignored Rust tests", ignored.len());
                }
                rust_tests::rust_tests_to_file_results(&ignored)
            } else {
                // Run all Rust tests
                let mut test_results = rust_tests::run_rust_tests(&cwd, false);
                let doc_results = rust_tests::run_rust_doctests(&cwd);
                test_results.extend(doc_results);
                test_results
            };

            // Update Rust test database
            if let Err(e) = update_rust_test_database(&rust_results) {
                if !quiet {
                    eprintln!("Warning: Failed to update Rust test database: {}", e);
                }
            }
        }

        // Run doctests
        run_all_doctests(&options, &mut results, &mut total_passed, &mut total_failed, quiet);
    }

    let start = Instant::now();
    let result = TestRunResult {
        files: results,
        total_passed,
        total_failed,
        total_skipped,
        total_ignored,
        total_duration_ms: start.elapsed().as_millis() as u64,
    };

    // Post-processing (skip in list mode)
    if !list_mode {
        generate_diagrams_if_enabled(&options, &result, quiet);
        finalize_profiling(&options, quiet);
        save_coverage_data(quiet);
    }

    // Complete test run tracking
    if let Some(run) = test_run {
        // Count crashed/timed out tests from results
        let crashed_count = result
            .files
            .iter()
            .filter(|f| {
                f.error
                    .as_ref()
                    .map(|e| e.contains("crash") || e.contains("signal"))
                    .unwrap_or(false)
            })
            .count();
        let timed_out_count = result
            .files
            .iter()
            .filter(|f| f.error.as_ref().map(|e| e.contains("timed out")).unwrap_or(false))
            .count();

        if let Err(e) = crate::test_db::complete_test_run(
            &db_path,
            &run.run_id,
            result.files.len(),
            result.total_passed,
            result.total_failed,
            crashed_count,
            timed_out_count,
        ) {
            debug_log!(DebugLevel::Detailed, "Runner", "Failed to complete test run: {}", e);
        } else {
            debug_log!(DebugLevel::Basic, "Runner", "Completed test run: {}", run.run_id);
        }
    }

    // Prompt for qualification of unqualified ignored tests
    if !list_mode && !quiet {
        prompt_for_ignored_qualifications();
    }

    result
}

/// Initialize diagram recording if enabled
fn initialize_diagrams(options: &TestOptions, quiet: bool) {
    let diagrams_enabled = options.seq_diagram || options.class_diagram || options.arch_diagram || options.diagram_all;
    if diagrams_enabled {
        simple_runtime::value::diagram_ffi::enable_diagrams();
        simple_runtime::value::diagram_ffi::clear_diagram_data();
        if !quiet {
            println!("Call flow diagram recording enabled");
        }
    }
}

/// Initialize runtime profiling if enabled
fn initialize_profiling(options: &TestOptions, quiet: bool) {
    if !options.profile {
        return;
    }

    use simple_compiler::runtime_profile::{ProfileConfig, ProfileMode};

    let mode = match options.profile_mode.as_deref() {
        Some("statistics") | Some("stats") => ProfileMode::Statistics,
        Some("sequence") | Some("seq") => ProfileMode::Sequence,
        Some("combined") | None => ProfileMode::Combined,
        Some(other) => {
            eprintln!("Warning: Unknown profile mode '{}', using combined", other);
            ProfileMode::Combined
        }
    };

    // Initialize the global profiler with the chosen mode
    // Note: global_profiler() is initialized with default config on first access;
    // we start it here which activates profiling
    let _config = ProfileConfig::default().with_mode(mode);
    // The global profiler uses default config; start it to activate
    simple_compiler::runtime_profile::start_profiling();

    // Enable runtime FFI profiling for Cranelift-compiled code
    simple_runtime::value::profiler_ffi::enable_profiling();

    // Register callbacks so runtime FFI can delegate to compiler profiler
    simple_runtime::value::profiler_ffi::register_profiler_callbacks(
        |name| {
            simple_compiler::runtime_profile::record_full_call(
                name,
                None,
                vec![],
                simple_compiler::runtime_profile::CallType::Direct,
            );
        },
        || {
            simple_compiler::runtime_profile::record_full_return(None);
        },
    );

    if !quiet {
        println!("Runtime profiling enabled (mode: {:?})", mode);
    }
}

/// Initialize coverage tracking if enabled
fn initialize_coverage(quiet: bool) {
    if is_coverage_enabled() {
        init_coverage();
        if !quiet {
            println!("Coverage tracking enabled");
        }
    }
}

/// Create test runner with appropriate GC settings
fn create_runner(options: &TestOptions) -> Runner {
    if options.gc_off {
        Runner::new_no_gc()
    } else if options.gc_log {
        Runner::new_with_gc_logging()
    } else {
        Runner::new()
    }
}

/// Prompt the user to qualify any unqualified ignored tests from this run.
/// Disabled by setting SIMPLE_QUALIFY_INTERACTIVE=0.
fn prompt_for_ignored_qualifications() {
    // Check if interactive qualification is disabled
    if std::env::var("SIMPLE_QUALIFY_INTERACTIVE").as_deref() == Ok("0") {
        return;
    }

    // Get ignored tests from BDD framework
    let ignored_tests = simple_compiler::interpreter::get_ignored_tests();
    if ignored_tests.is_empty() {
        return;
    }

    // Load test database to find unqualified ones
    let db_path = PathBuf::from("doc/test/test_db.sdn");
    let db = match crate::test_db::load_test_db(&db_path) {
        Ok(db) => db,
        Err(_) => return,
    };

    // Find which ignored tests lack qualification
    let unqualified: Vec<&String> = ignored_tests
        .iter()
        .filter(|name| {
            db.records
                .values()
                .any(|r| &r.test_name == *name && crate::test_db::needs_qualification(r))
        })
        .collect();

    if unqualified.is_empty() {
        return;
    }

    println!();
    println!("\x1b[33m⚠ {} ignored test(s) lack qualification:\x1b[0m", unqualified.len());
    for (i, name) in unqualified.iter().enumerate() {
        println!("  {}. {}", i + 1, name);
    }
    println!();
    print!("Qualify now? [y/N] ");
    std::io::Write::flush(&mut std::io::stdout()).ok();

    let mut input = String::new();
    if std::io::stdin().read_line(&mut input).is_err() {
        return;
    }

    if !input.trim().eq_ignore_ascii_case("y") {
        return;
    }

    // Ask for reason
    print!("Reason for ignoring: ");
    std::io::Write::flush(&mut std::io::stdout()).ok();

    let mut reason = String::new();
    if std::io::stdin().read_line(&mut reason).is_err() || reason.trim().is_empty() {
        println!("No reason provided, skipping qualification.");
        return;
    }

    // Collect test IDs to qualify
    let test_ids: Vec<String> = unqualified
        .iter()
        .filter_map(|name| {
            db.records
                .values()
                .find(|r| &r.test_name == *name && crate::test_db::needs_qualification(r))
                .map(|r| r.test_id.clone())
        })
        .collect();

    if test_ids.is_empty() {
        return;
    }

    // Use existing qualify_ignore infrastructure
    use crate::cli::qualify_ignore::{QualifyIgnoreArgs, handle_qualify_ignore};
    let args = QualifyIgnoreArgs {
        test_ids,
        reason: Some(reason.trim().to_string()),
        db_path: Some(db_path),
        ..Default::default()
    };

    match handle_qualify_ignore(args) {
        Ok(()) => println!("\x1b[32m✓ Tests qualified successfully.\x1b[0m"),
        Err(e) => println!("\x1b[31m✗ Qualification failed: {}\x1b[0m", e),
    }
}

/// Determine test path from options or common defaults
fn determine_test_path(options: &TestOptions) -> PathBuf {
    options.path.clone().unwrap_or_else(|| {
        let cwd = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
        // Try common test directories
        for dir in &["test", "tests", "spec", "src/std/test", "simple/std_lib/test"] {
            let p = cwd.join(dir);
            if p.is_dir() {
                return p;
            }
        }
        cwd.join("test")
    })
}

/// Discover and filter test files
fn discover_and_filter_tests(test_path: &PathBuf, options: &TestOptions) -> Vec<PathBuf> {
    debug_log!(
        DebugLevel::Basic,
        "Discovery",
        "Finding tests in: {}",
        test_path.display()
    );

    // Include .skip files when --only-skipped is set
    let mut test_files = discover_tests_with_skip(test_path, options.level, options.only_skipped);

    // When --only-skipped, filter to only .skip files
    if options.only_skipped {
        test_files.retain(|path| is_skip_test_file(path));
    }

    debug_log!(DebugLevel::Basic, "Discovery", "Found {} test files", test_files.len());

    // Apply tag filter
    if let Some(ref tag) = options.tag {
        let before_count = test_files.len();
        test_files.retain(|path| matches_tag(path, &options.tag));
        debug_log!(
            DebugLevel::Detailed,
            "Discovery",
            "Tag filter '{}': {} -> {} files",
            tag,
            before_count,
            test_files.len()
        );
    }

    // Apply seed for shuffling
    if let Some(seed) = options.seed {
        shuffle_tests(&mut test_files, seed);
        debug_log!(DebugLevel::Detailed, "Discovery", "Shuffled tests with seed: {}", seed);
    }

    debug_log!(DebugLevel::Basic, "Discovery", "Final test count: {}", test_files.len());

    test_files
}

/// Shuffle tests deterministically based on seed
fn shuffle_tests(test_files: &mut Vec<PathBuf>, seed: u64) {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    test_files.sort_by(|a, b| {
        let mut hasher_a = DefaultHasher::new();
        seed.hash(&mut hasher_a);
        a.hash(&mut hasher_a);
        let hash_a = hasher_a.finish();

        let mut hasher_b = DefaultHasher::new();
        seed.hash(&mut hasher_b);
        b.hash(&mut hasher_b);
        let hash_b = hasher_b.finish();

        hash_a.cmp(&hash_b)
    });
}

/// Execute test files and collect results
fn execute_test_files(
    runner: Option<&Runner>,
    test_files: &[PathBuf],
    options: &TestOptions,
    build_cache: Option<&BuildCache>,
    quiet: bool,
) -> (Vec<TestFileResult>, usize, usize, usize, usize) {
    debug_log!(
        DebugLevel::Basic,
        "Execution",
        "Executing {} test files",
        test_files.len()
    );

    let mut results = Vec::new();
    let mut total_passed = 0;
    let mut total_failed = 0;
    let mut total_skipped = 0;
    let mut total_ignored = 0;

    // Performance warning for listing with filters (scans many files)
    let list_mode = options.list || options.list_ignored;
    if list_mode && test_files.len() > 100 && (options.only_slow || options.only_skipped) {
        if !quiet {
            eprintln!("⚠️  Warning: Listing tests with filters scans all files (slow for large test suites)");
            eprintln!("   Tip: Limit scope with path argument, e.g.:");
            eprintln!("        simple test test/lib/std/unit/ --only-skipped --list");
            eprintln!("   Or use test database: cat doc/test/test_db.sdn | grep skip\n");
        }
    }

    for (idx, path) in test_files.iter().enumerate() {
        if !quiet && !options.list && !options.list_ignored {
            println!("Running: {}", path.display());
        }

        // In safe mode, always show progress
        if options.safe_mode && !quiet {
            println!("[{}/{}] {}", idx + 1, test_files.len(), path.display());
        }

        debug_log!(
            DebugLevel::Detailed,
            "Execution",
            "Test {}/{}: {}",
            idx + 1,
            test_files.len(),
            path.display()
        );

        let result = match options.execution_mode {
            TestExecutionMode::Smf => {
                // SMF mode doesn't support SSpec DSL compilation
                // Fall back to safe mode (subprocess with "test" command)
                eprintln!("[INFO] SMF mode for tests not supported, using safe mode");
                super::execution::run_test_file_safe_mode(path, options)
            }
            TestExecutionMode::Native => {
                if let Some(cache) = build_cache {
                    super::execution::run_test_file_native_mode(path, cache, options)
                } else {
                    TestFileResult {
                        path: path.to_path_buf(),
                        passed: 0,
                        failed: 1,
                        skipped: 0,
                        ignored: 0,
                        duration_ms: 0,
                        error: Some("Build cache not initialized for native mode".to_string()),
                    }
                }
            }
            TestExecutionMode::Interpreter => {
                if options.safe_mode {
                    // Safe mode - run in separate process
                    super::execution::run_test_file_safe_mode(path, options)
                } else if let Some(runner) = runner {
                    // Normal mode - run in same process
                    super::execution::run_test_file(runner, path)
                } else {
                    TestFileResult {
                        path: path.to_path_buf(),
                        passed: 0,
                        failed: 1,
                        skipped: 0,
                        ignored: 0,
                        duration_ms: 0,
                        error: Some("No runner available (internal error)".to_string()),
                    }
                }
            }
        };
        total_passed += result.passed;
        total_failed += result.failed;
        total_skipped += result.skipped;
        total_ignored += result.ignored;

        debug_log!(
            DebugLevel::Trace,
            "Execution",
            "  Running totals: passed={}, failed={}, skipped={}, ignored={}",
            total_passed,
            total_failed,
            total_skipped,
            total_ignored
        );

        if !options.list && !options.list_ignored {
            print_result(&result, quiet);
        }

        let failed = result.failed > 0 || result.error.is_some();
        results.push(result);

        // Stop on first failure if fail-fast
        if options.fail_fast && failed {
            debug_log!(
                DebugLevel::Detailed,
                "Execution",
                "Stopping on first failure (fail-fast mode)"
            );
            break;
        }
    }

    debug_log!(
        DebugLevel::Basic,
        "Collection",
        "Aggregated results: passed={}, failed={}, skipped={}, ignored={}",
        total_passed,
        total_failed,
        total_skipped,
        total_ignored
    );

    (results, total_passed, total_failed, total_skipped, total_ignored)
}

/// Print individual test result
fn print_result(result: &TestFileResult, quiet: bool) {
    if quiet {
        return;
    }

    let status = if result.failed > 0 || result.error.is_some() {
        "\x1b[31mFAILED\x1b[0m"
    } else {
        "\x1b[32mPASSED\x1b[0m"
    };

    println!("  {} ({}ms)", status, result.duration_ms);

    if let Some(ref err) = result.error {
        eprintln!("  Error: {}", err);
    }
}

/// Run all enabled doctest types
fn run_all_doctests(
    options: &TestOptions,
    results: &mut Vec<TestFileResult>,
    total_passed: &mut usize,
    total_failed: &mut usize,
    quiet: bool,
) {
    if options.doctest_src || options.doctest_doc {
        let doctest_results = run_doctests(options, quiet);
        for result in doctest_results {
            *total_passed += result.passed;
            *total_failed += result.failed;
            results.push(result);
        }
    }

    if options.doctest_md {
        let md_results = run_md_doctests(options, quiet);
        for result in md_results {
            *total_passed += result.passed;
            *total_failed += result.failed;
            results.push(result);
        }
    }
}

/// Generate diagrams if enabled
fn generate_diagrams_if_enabled(options: &TestOptions, result: &TestRunResult, quiet: bool) {
    if options.seq_diagram || options.class_diagram || options.arch_diagram || options.diagram_all {
        if let Some(diagram_paths) = generate_test_diagrams(options, &result.files, quiet) {
            if !quiet {
                println!("───────────────────────────────────────────────────────────────");
                println!("Generated Diagrams");
                println!("───────────────────────────────────────────────────────────────");
                for path in &diagram_paths {
                    println!("  {}", path.display());
                }
                println!("───────────────────────────────────────────────────────────────");
            }
        }
    }
}

/// Finalize profiling: stop, collect metrics, and print summary
fn finalize_profiling(options: &TestOptions, quiet: bool) {
    if !options.profile {
        return;
    }

    simple_compiler::runtime_profile::stop_profiling();
    simple_runtime::value::profiler_ffi::disable_profiling();

    let metrics = simple_compiler::runtime_profile::collect_global_metrics();

    if !quiet {
        println!("───────────────────────────────────────────────────────────────");
        println!("Runtime Profile Summary");
        println!("───────────────────────────────────────────────────────────────");
        println!("  Duration:         {:.3}s", metrics.duration.as_secs_f64());
        println!("  Total calls:      {}", metrics.total_calls);
        println!("  Unique functions:  {}", metrics.unique_functions);
        println!("  Hot functions:     {}", metrics.hot_functions);
        println!("  Cold functions:    {}", metrics.cold_functions);
        println!("  Startup functions: {}", metrics.startup_functions);

        // Print top 10 hottest functions
        if !metrics.function_stats.is_empty() {
            println!();
            println!("  Top functions by call count:");
            for (i, stat) in metrics.function_stats.iter().take(10).enumerate() {
                println!("    {}. {} ({} calls, phase: {:?})",
                    i + 1, stat.name, stat.call_count, stat.inferred_phase);
            }
        }
        println!("───────────────────────────────────────────────────────────────");
    }
}

/// Run list mode using static analysis (fast path).
///
/// This uses the static test registry to list tests without executing
/// any DSL code. Target performance: ~1 second for 1000+ tests.
fn run_list_mode_static(test_files: &[PathBuf], options: &TestOptions, quiet: bool) -> TestRunResult {
    let start = Instant::now();

    debug_log!(
        DebugLevel::Basic,
        "ListMode",
        "Using static analysis for {} test files",
        test_files.len()
    );

    // Build static registry from test files
    let registry = match StaticTestRegistry::from_files(test_files) {
        Ok(r) => r,
        Err(e) => {
            if !quiet {
                eprintln!("Warning: Static analysis failed: {}", e);
                eprintln!("Falling back to runtime discovery...");
            }
            // Return empty result on failure - caller can fall back to runtime
            return TestRunResult {
                files: Vec::new(),
                total_passed: 0,
                total_failed: 0,
                total_skipped: 0,
                total_ignored: 0,
                total_duration_ms: start.elapsed().as_millis() as u64,
            };
        }
    };

    // Print list output
    if !quiet {
        let output = registry.format_list(
            options.show_tags,
            options.only_slow,
            options.only_skipped,
            options.list_ignored,
        );
        print!("{}", output);
    }

    // Return result with counts from static analysis
    let _total_tests = if options.only_slow {
        registry.slow_count()
    } else if options.only_skipped {
        registry.skipped_count()
    } else if options.list_ignored {
        registry.ignored_count()
    } else {
        registry.total_count()
    };

    TestRunResult {
        files: Vec::new(), // No file results in list mode
        total_passed: 0,
        total_failed: 0,
        total_skipped: registry.skipped_count(),
        total_ignored: registry.ignored_count(),
        total_duration_ms: start.elapsed().as_millis() as u64,
    }
}

// ============================================================================
// Skip Features Listing
// ============================================================================

/// Feature metadata extracted from a .skip file
#[derive(Debug, Clone)]
struct SkipFeatureInfo {
    file_path: PathBuf,
    title: String,
    feature_ids: String,
    category: String,
    status: String,
}

/// Extract feature metadata from a .skip file's docstring
fn extract_skip_feature_info(path: &PathBuf) -> Option<SkipFeatureInfo> {
    let content = fs::read_to_string(path).ok()?;

    // Find the docstring (starts with """)
    let doc_start = content.find("\"\"\"")?;
    let doc_end = content[doc_start + 3..].find("\"\"\"")? + doc_start + 3;
    let docstring = &content[doc_start + 3..doc_end];

    let mut title = String::new();
    let mut feature_ids = String::new();
    let mut category = String::new();
    let mut status = String::new();

    for line in docstring.lines() {
        let trimmed = line.trim();

        // Title is the first # heading
        if title.is_empty() && trimmed.starts_with("# ") {
            title = trimmed[2..].trim().to_string();
        }

        // Extract metadata fields
        if trimmed.starts_with("**Feature ID") {
            if let Some(val) = trimmed.split(":**").nth(1) {
                feature_ids = val.trim().to_string();
            }
        } else if trimmed.starts_with("**Category:**") {
            if let Some(val) = trimmed.split(":**").nth(1) {
                category = val.trim().to_string();
            }
        } else if trimmed.starts_with("**Status:**") {
            if let Some(val) = trimmed.split(":**").nth(1) {
                status = val.trim().to_string();
            }
        }
    }

    // Use filename as fallback title
    if title.is_empty() {
        title = path
            .file_stem()
            .and_then(|s| s.to_str())
            .map(|s| s.replace("_spec.spl", "").replace('_', " "))
            .unwrap_or_else(|| "Unknown".to_string());
    }

    Some(SkipFeatureInfo {
        file_path: path.clone(),
        title,
        feature_ids,
        category,
        status,
    })
}

/// List features from .skip test files
fn run_list_skip_features(test_files: &[PathBuf], planned_only: bool, quiet: bool) -> TestRunResult {
    let start = Instant::now();

    // Extract feature info from each file
    let mut features: Vec<SkipFeatureInfo> = test_files
        .iter()
        .filter_map(|path| extract_skip_feature_info(path))
        .collect();

    // Filter to planned-only if requested
    if planned_only {
        features.retain(|f| {
            let status_lower = f.status.to_lowercase();
            status_lower.contains("planned") || status_lower.contains("tbd") || status_lower == "unknown"
        });
    }

    let title = if planned_only {
        format!("Planned Features ({} of {} files)", features.len(), test_files.len())
    } else {
        format!("Skipped Features ({} files)", test_files.len())
    };

    if !quiet {
        println!();
        println!("{}", title);
        println!("═══════════════════════════════════════════════════════════════");
        println!();
    }

    // Group by category
    features.sort_by(|a, b| a.category.cmp(&b.category).then_with(|| a.title.cmp(&b.title)));

    if !quiet {
        let mut current_category: Option<String> = None;
        let mut category_count = 0;

        for feature in &features {
            // Print category header when it changes
            let should_print_header = match &current_category {
                None => true,
                Some(cat) => cat != &feature.category,
            };

            if should_print_header {
                if current_category.is_some() {
                    println!();
                }
                let cat_name = if feature.category.is_empty() {
                    "Uncategorized"
                } else {
                    &feature.category
                };
                println!("Category: {}", cat_name);
                current_category = Some(feature.category.clone());
                category_count += 1;
            }

            // Print feature info
            let status_display = if feature.status.is_empty() {
                "Unknown".to_string()
            } else {
                feature.status.clone()
            };

            let ids_display = if feature.feature_ids.is_empty() {
                "-".to_string()
            } else {
                feature.feature_ids.clone()
            };

            println!(
                "  {:24} {:40} [{}]",
                ids_display,
                truncate_str(&feature.title, 40),
                status_display
            );
        }

        // Summary
        println!();
        println!("───────────────────────────────────────────────────────────────");
        println!(
            "Summary: {} files across {} categories",
            features.len(),
            category_count.max(1)
        );
        println!();
    }

    TestRunResult {
        files: Vec::new(),
        total_passed: 0,
        total_failed: 0,
        total_skipped: test_files.len(),
        total_ignored: 0,
        total_duration_ms: start.elapsed().as_millis() as u64,
    }
}

/// Truncate string to max length with ellipsis
fn truncate_str(s: &str, max_len: usize) -> String {
    if s.len() <= max_len {
        s.to_string()
    } else {
        format!("{}...", &s[..max_len - 3])
    }
}

// ============================================================================
// Run Management
// ============================================================================

use crate::test_db::{TestRunRecord, TestRunStatus, cleanup_stale_runs, list_runs, prune_old_runs};

/// Handle run management commands (--list-runs, --cleanup-runs, --prune-runs)
fn handle_run_management(options: &TestOptions) -> TestRunResult {
    let db_path = PathBuf::from("doc/test/test_db.sdn");
    let quiet = matches!(options.format, OutputFormat::Json);

    // Cleanup stale runs first (if requested or before listing)
    if options.cleanup_runs {
        match cleanup_stale_runs(&db_path, 2) {
            // 2 hours = stale
            Ok(cleaned) => {
                if !quiet {
                    if cleaned.is_empty() {
                        println!("No stale runs found.");
                    } else {
                        println!("Cleaned {} stale run(s):", cleaned.len());
                        for run_id in &cleaned {
                            println!("  - {}", run_id);
                        }
                    }
                }
            }
            Err(e) => {
                if !quiet {
                    eprintln!("Error cleaning up runs: {}", e);
                }
            }
        }
    }

    // Prune old runs (if requested)
    if let Some(keep_count) = options.prune_runs {
        match prune_old_runs(&db_path, keep_count) {
            Ok(deleted) => {
                if !quiet {
                    if deleted == 0 {
                        println!("No runs to prune (keeping {})", keep_count);
                    } else {
                        println!("Pruned {} old run(s) (keeping {})", deleted, keep_count);
                    }
                }
            }
            Err(e) => {
                if !quiet {
                    eprintln!("Error pruning runs: {}", e);
                }
            }
        }
    }

    // List runs (if requested)
    if options.list_runs {
        let status_filter = options.runs_status_filter.as_ref().map(|s| TestRunStatus::from_str(s));

        match list_runs(&db_path, status_filter) {
            Ok(runs) => {
                if !quiet {
                    if runs.is_empty() {
                        println!("No test runs found.");
                    } else {
                        println!("Test Runs ({} total):\n", runs.len());
                        println!(
                            "{:<30} {:<10} {:<20} {:<8} {:>6} {:>6} {:>6}",
                            "Run ID", "Status", "Start Time", "PID", "Tests", "Pass", "Fail"
                        );
                        println!("{}", "-".repeat(100));

                        for run in &runs {
                            // Parse and format start time
                            let start_time = if let Ok(dt) = chrono::DateTime::parse_from_rfc3339(&run.start_time) {
                                dt.format("%Y-%m-%d %H:%M:%S").to_string()
                            } else {
                                run.start_time.clone()
                            };

                            println!(
                                "{:<30} {:<10} {:<20} {:<8} {:>6} {:>6} {:>6}",
                                run.run_id,
                                run.status.to_string(),
                                start_time,
                                run.pid,
                                run.test_count,
                                run.passed,
                                run.failed
                            );
                        }

                        // Summary
                        let running = runs.iter().filter(|r| r.status == TestRunStatus::Running).count();
                        let completed = runs.iter().filter(|r| r.status == TestRunStatus::Completed).count();
                        let crashed = runs.iter().filter(|r| r.status == TestRunStatus::Crashed).count();

                        println!(
                            "\nSummary: {} running, {} completed, {} crashed",
                            running, completed, crashed
                        );
                    }
                }
            }
            Err(e) => {
                if !quiet {
                    eprintln!("Error listing runs: {}", e);
                }
            }
        }
    }

    // Return empty result for run management commands
    TestRunResult {
        files: Vec::new(),
        total_passed: 0,
        total_failed: 0,
        total_skipped: 0,
        total_ignored: 0,
        total_duration_ms: 0,
    }
}
