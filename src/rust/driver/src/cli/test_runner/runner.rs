//! Main test runner implementation.
//!
//! Orchestrates test discovery, execution, and reporting.

use std::fs;
use std::path::PathBuf;
use std::time::Instant;

use simple_compiler::{init_coverage, is_coverage_enabled};

use crate::runner::Runner;
use super::test_discovery::{discover_tests, matches_tag};
use super::types::{TestFileResult, TestLevel, TestOptions, TestRunResult, OutputFormat, DebugLevel, debug_log};
use super::execution::run_test_file;
use super::doctest::{run_doctests, run_md_doctests};
use super::parallel::run_tests_parallel;
use super::diagrams::generate_test_diagrams;
use super::discovery::print_discovery_summary;
use super::coverage::save_coverage_data;
use super::feature_db::update_feature_database;
use super::test_db_update::update_test_database;
use super::static_registry::StaticTestRegistry;

/// Load CPU throttle configuration from simple.test.toml
fn load_cpu_throttle_config(options: &mut TestOptions) {
    // Find simple.test.toml in current directory or project root
    let config_paths = [
        PathBuf::from("simple.test.toml"),
        PathBuf::from("../simple.test.toml"),
        PathBuf::from("../../simple.test.toml"),
    ];

    for path in &config_paths {
        if let Ok(content) = fs::read_to_string(path) {
            parse_cpu_throttle_config(&content, options);
            debug_log!(DebugLevel::Detailed, "Config", "Loaded config from: {}", path.display());
            return;
        }
    }

    debug_log!(DebugLevel::Trace, "Config", "No simple.test.toml found, using defaults");
}

/// Parse CPU throttle configuration from TOML content
fn parse_cpu_throttle_config(content: &str, options: &mut TestOptions) {
    // Simple TOML parsing for cpu_throttle section
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
                "enabled" => {
                    if value == "true" && !options.parallel {
                        // Enable parallel if config says so and not explicitly disabled
                        // Only applies if user didn't specify --parallel on CLI
                    }
                }
                "threshold" => {
                    if let Ok(v) = value.parse::<u8>() {
                        // Only apply if user didn't override on CLI (still default)
                        if options.cpu_threshold == 70 {
                            options.cpu_threshold = v;
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

    // Load configuration from simple.test.toml (applies defaults if not overridden by CLI)
    if options.parallel {
        load_cpu_throttle_config(&mut options);
    }

    let quiet = matches!(options.format, OutputFormat::Json);
    let list_mode = options.list || options.list_ignored;

    // Discover test files first (needed for both static and runtime modes)
    let test_path = determine_test_path(&options);
    let test_files = discover_and_filter_tests(&test_path, &options);

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
    initialize_coverage(quiet);

    // Skip runner creation in safe mode (each subprocess creates its own)
    let runner = if !options.safe_mode {
        Some(create_runner(&options))
    } else {
        None
    };

    // Print discovery summary
    print_discovery_summary(&test_files, &options, quiet);

    // Execute tests
    let (mut results, mut total_passed, mut total_failed, mut total_skipped, mut total_ignored) =
        if options.parallel && options.safe_mode {
            // Parallel execution with CPU-aware thread management
            debug_log!(DebugLevel::Basic, "Runner", "Using parallel execution mode");
            run_tests_parallel(&test_files, &options, quiet)
        } else {
            // Sequential execution (default)
            execute_test_files(runner.as_ref(), &test_files, &options, quiet)
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
        save_coverage_data(quiet);
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

/// Determine test path from options or common defaults
fn determine_test_path(options: &TestOptions) -> PathBuf {
    options.path.clone().unwrap_or_else(|| {
        let cwd = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
        // Try common test directories
        for dir in &["test", "tests", "spec", "simple/std_lib/test"] {
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

    let mut test_files = discover_tests(test_path, options.level);

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

        let result = if options.safe_mode {
            // Safe mode - run in separate process
            super::execution::run_test_file_safe_mode(path, options)
        } else if let Some(runner) = runner {
            // Normal mode - run in same process
            super::execution::run_test_file(runner, path)
        } else {
            // No runner available - this shouldn't happen
            TestFileResult {
                path: path.to_path_buf(),
                passed: 0,
                failed: 1,
                skipped: 0,
                ignored: 0,
                duration_ms: 0,
                error: Some("No runner available (internal error)".to_string()),
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

/// Run list mode using static analysis (fast path).
///
/// This uses the static test registry to list tests without executing
/// any DSL code. Target performance: ~1 second for 1000+ tests.
fn run_list_mode_static(
    test_files: &[PathBuf],
    options: &TestOptions,
    quiet: bool,
) -> TestRunResult {
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
