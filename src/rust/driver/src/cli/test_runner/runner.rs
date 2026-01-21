//! Main test runner implementation.
//!
//! Orchestrates test discovery, execution, and reporting.

use std::path::PathBuf;
use std::time::Instant;

use simple_compiler::{init_coverage, is_coverage_enabled};

use crate::runner::Runner;
use super::test_discovery::{discover_tests, matches_tag};
use super::types::{TestFileResult, TestLevel, TestOptions, TestRunResult, OutputFormat};
use super::execution::run_test_file;
use super::doctest::{run_doctests, run_md_doctests};
use super::diagrams::generate_test_diagrams;
use super::discovery::print_discovery_summary;
use super::coverage::save_coverage_data;
use super::feature_db::update_feature_database;
use super::test_db_update::update_test_database;

/// Run tests with the given options
pub fn run_tests(options: TestOptions) -> TestRunResult {
    let quiet = matches!(options.format, OutputFormat::Json);

    // Initialize subsystems
    initialize_diagrams(&options, quiet);
    initialize_coverage(quiet);

    let runner = create_runner(&options);
    let test_path = determine_test_path(&options);
    let test_files = discover_and_filter_tests(&test_path, &options);

    // Print discovery summary
    print_discovery_summary(&test_files, &options, quiet);

    // Execute tests
    let (mut results, mut total_passed, mut total_failed) = execute_test_files(&runner, &test_files, &options, quiet);

    // Determine if all tests were run (no filters applied)
    let all_tests_run = options.path.is_none() && options.tag.is_none() && options.level == TestLevel::All;

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

    let start = Instant::now();
    let result = TestRunResult {
        files: results,
        total_passed,
        total_failed,
        total_duration_ms: start.elapsed().as_millis() as u64,
    };

    // Post-processing
    generate_diagrams_if_enabled(&options, &result, quiet);
    save_coverage_data(quiet);

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
    let mut test_files = discover_tests(test_path, options.level);

    // Apply tag filter
    if options.tag.is_some() {
        test_files.retain(|path| matches_tag(path, &options.tag));
    }

    // Apply seed for shuffling
    if let Some(seed) = options.seed {
        shuffle_tests(&mut test_files, seed);
    }

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
    runner: &Runner,
    test_files: &[PathBuf],
    options: &TestOptions,
    quiet: bool,
) -> (Vec<TestFileResult>, usize, usize) {
    let mut results = Vec::new();
    let mut total_passed = 0;
    let mut total_failed = 0;

    for path in test_files {
        if !quiet {
            println!("Running: {}", path.display());
        }

        let result = run_test_file(runner, path);
        total_passed += result.passed;
        total_failed += result.failed;

        print_result(&result, quiet);

        let failed = result.failed > 0 || result.error.is_some();
        results.push(result);

        // Stop on first failure if fail-fast
        if options.fail_fast && failed {
            break;
        }
    }

    (results, total_passed, total_failed)
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
