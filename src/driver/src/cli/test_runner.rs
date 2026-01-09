//! Test runner CLI command for Simple language.
//!
//! Provides a unified test runner that discovers and executes tests
//! in the BDD spec format (*_spec.spl, *_test.spl).

use std::path::{Path, PathBuf};
use std::time::Instant;

use simple_compiler::{
    get_coverage_output_path, get_global_coverage, init_coverage, is_coverage_enabled,
    save_global_coverage,
};
use simple_driver::runner::Runner;

use super::test_discovery::{discover_tests, is_test_file, matches_tag};
pub use super::test_output::print_summary;

/// Test level filter
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TestLevel {
    All,
    Unit,
    Integration,
    System,
}

/// Output format for test results
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum OutputFormat {
    /// Default text format with colors
    #[default]
    Text,
    /// JSON format for machine-readable output
    Json,
    /// Nested documentation format (like RSpec)
    Doc,
}

/// Options for the test runner
#[derive(Debug, Clone)]
pub struct TestOptions {
    /// Test path (file or directory)
    pub path: Option<PathBuf>,
    /// Test level filter
    pub level: TestLevel,
    /// Tag filter
    pub tag: Option<String>,
    /// Stop on first failure
    pub fail_fast: bool,
    /// Random seed for shuffle
    pub seed: Option<u64>,
    /// Enable GC logging
    pub gc_log: bool,
    /// Disable GC
    pub gc_off: bool,
    /// Output format
    pub format: OutputFormat,
    /// Watch mode - auto-rerun on file changes
    pub watch: bool,
}

impl Default for TestOptions {
    fn default() -> Self {
        Self {
            path: None,
            level: TestLevel::All,
            tag: None,
            fail_fast: false,
            seed: None,
            gc_log: false,
            gc_off: false,
            format: OutputFormat::Text,
            watch: false,
        }
    }
}

/// Test result for a single file
#[derive(Debug)]
pub struct TestFileResult {
    pub path: PathBuf,
    pub passed: usize,
    pub failed: usize,
    pub duration_ms: u64,
    pub error: Option<String>,
}

/// Overall test run result
#[derive(Debug)]
pub struct TestRunResult {
    pub files: Vec<TestFileResult>,
    pub total_passed: usize,
    pub total_failed: usize,
    pub total_duration_ms: u64,
}

impl TestRunResult {
    pub fn success(&self) -> bool {
        self.total_failed == 0
    }
}

/// Parse test output to extract pass/fail counts
fn parse_test_output(output: &str) -> (usize, usize) {
    // Look for patterns like "N examples, M failures"
    let mut passed = 0;
    let mut failed = 0;

    for line in output.lines() {
        // Pattern: "X examples, Y failures"
        if line.contains("examples") && line.contains("failure") {
            // Extract numbers
            let parts: Vec<&str> = line.split(|c: char| !c.is_numeric()).collect();
            let numbers: Vec<usize> = parts
                .iter()
                .filter_map(|p| p.parse::<usize>().ok())
                .collect();

            if numbers.len() >= 2 {
                let total = numbers[0];
                failed = numbers[1];
                passed = total.saturating_sub(failed);
            }
        }
    }

    (passed, failed)
}

/// Run a single test file
fn run_test_file(runner: &Runner, path: &Path) -> TestFileResult {
    let start = Instant::now();

    match runner.run_file(path) {
        Ok(exit_code) => {
            let duration_ms = start.elapsed().as_millis() as u64;

            // Capture output (we need to re-run with output capture)
            // For now, use exit code to determine pass/fail
            let (passed, failed) = if exit_code == 0 {
                (1, 0) // At least one test passed
            } else {
                (0, 1) // At least one test failed
            };

            TestFileResult {
                path: path.to_path_buf(),
                passed,
                failed,
                duration_ms,
                error: None,
            }
        }
        Err(e) => {
            let duration_ms = start.elapsed().as_millis() as u64;
            let error_msg: String = e.to_string();
            TestFileResult {
                path: path.to_path_buf(),
                passed: 0,
                failed: 1,
                duration_ms,
                error: Some(error_msg),
            }
        }
    }
}

/// Run tests with the given options
pub fn run_tests(options: TestOptions) -> TestRunResult {
    let quiet = matches!(options.format, OutputFormat::Json);

    // Initialize coverage if enabled
    if is_coverage_enabled() {
        init_coverage();
        if !quiet {
            println!("Coverage tracking enabled");
        }
    }

    let runner = if options.gc_off {
        Runner::new_no_gc()
    } else if options.gc_log {
        Runner::new_with_gc_logging()
    } else {
        Runner::new()
    };

    // Determine test path
    let test_path = options.path.clone().unwrap_or_else(|| {
        let cwd = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
        // Try common test directories
        for dir in &["test", "tests", "spec", "simple/std_lib/test"] {
            let p = cwd.join(dir);
            if p.is_dir() {
                return p;
            }
        }
        cwd.join("test")
    });

    // Discover test files
    let mut test_files = discover_tests(&test_path, options.level);

    // Apply tag filter
    if options.tag.is_some() {
        test_files.retain(|path| matches_tag(path, &options.tag));
    }

    // Apply seed for shuffling
    if let Some(seed) = options.seed {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        // Simple deterministic shuffle based on seed
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

    let start = Instant::now();
    let mut results = Vec::new();
    let mut total_passed = 0;
    let mut total_failed = 0;

    for path in &test_files {
        // Print file being tested (unless in quiet/JSON mode)
        if !quiet {
            println!("Running: {}", path.display());
        }

        let result = run_test_file(&runner, path);

        total_passed += result.passed;
        total_failed += result.failed;

        if !quiet {
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

        let failed = result.failed > 0 || result.error.is_some();
        results.push(result);

        // Stop on first failure if fail-fast
        if options.fail_fast && failed {
            break;
        }
    }

    let feature_db_path = PathBuf::from("doc/features/feature_db.sdn");
    let sspec_files: Vec<PathBuf> = test_files
        .iter()
        .filter(|path| {
            path.file_name()
                .and_then(|n| n.to_str())
                .map(|n| n.ends_with("_spec.spl"))
                .unwrap_or(false)
        })
        .cloned()
        .collect();

    let failed_specs: Vec<PathBuf> = results
        .iter()
        .filter(|result| result.failed > 0 || result.error.is_some())
        .map(|result| result.path.clone())
        .collect();

    if let Err(e) = simple_driver::feature_db::update_feature_db_from_sspec(
        &feature_db_path,
        &sspec_files,
        &failed_specs,
    )
    {
        total_failed += 1;
        results.push(TestFileResult {
            path: feature_db_path,
            passed: 0,
            failed: 1,
            duration_ms: 0,
            error: Some(format!("feature db update failed: {}", e)),
        });
    }

    let result = TestRunResult {
        files: results,
        total_passed,
        total_failed,
        total_duration_ms: start.elapsed().as_millis() as u64,
    };

    // Save coverage if enabled
    if is_coverage_enabled() {
        if let Err(e) = save_global_coverage() {
            if !quiet {
                eprintln!("Warning: Failed to save coverage data: {}", e);
            }
        } else if !quiet {
            let path = get_coverage_output_path();
            println!("Coverage data saved to: {}", path.display());

            // Print coverage stats
            if let Some(cov) = get_global_coverage() {
                let cov = cov.lock().unwrap();
                let stats = cov.stats();
                println!("  Lines executed: {}", stats.total_lines);
                println!("  Files covered: {}", stats.total_files);
                println!("  Functions called: {}", stats.total_functions);
                println!("  FFI calls: {}", stats.total_ffi_calls);
            }
        }
    }

    result
}

/// Parse test command arguments
pub fn parse_test_args(args: &[String]) -> TestOptions {
    let mut options = TestOptions::default();
    let mut i = 0;

    while i < args.len() {
        match args[i].as_str() {
            "--unit" => options.level = TestLevel::Unit,
            "--integration" => options.level = TestLevel::Integration,
            "--system" => options.level = TestLevel::System,
            "--fail-fast" => options.fail_fast = true,
            "--gc-log" => options.gc_log = true,
            "--gc=off" | "--gc=OFF" => options.gc_off = true,
            "--tag" => {
                i += 1;
                if i < args.len() {
                    options.tag = Some(args[i].clone());
                }
            }
            "--seed" => {
                i += 1;
                if i < args.len() {
                    options.seed = args[i].parse().ok();
                }
            }
            "--format" => {
                i += 1;
                if i < args.len() {
                    options.format = match args[i].as_str() {
                        "json" => OutputFormat::Json,
                        "doc" => OutputFormat::Doc,
                        _ => OutputFormat::Text,
                    };
                }
            }
            "--json" => options.format = OutputFormat::Json,
            "--doc" => options.format = OutputFormat::Doc,
            "--watch" => options.watch = true,
            arg if !arg.starts_with("-") && options.path.is_none() => {
                options.path = Some(PathBuf::from(arg));
            }
            _ => {}
        }
        i += 1;
    }

    options
}

/// Watch test directories and auto-regenerate documentation on changes
pub fn watch_tests(options: TestOptions) -> Result<(), String> {
    use notify::{Config, EventKind, RecommendedWatcher, RecursiveMode, Watcher};
    use std::sync::mpsc::channel;

    let quiet = matches!(options.format, OutputFormat::Json);
    let generate_docs = matches!(options.format, OutputFormat::Doc);

    // Determine test path
    let test_path = options.path.clone().unwrap_or_else(|| {
        let cwd = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
        for dir in &["test", "tests", "spec", "simple/std_lib/test"] {
            let p = cwd.join(dir);
            if p.is_dir() {
                return p;
            }
        }
        cwd.join("test")
    });

    if !quiet {
        println!("Simple Test Watcher");
        println!("Watching: {}", test_path.display());
        if generate_docs {
            println!("Documentation: Auto-generate on changes");
        }
        println!("Press Ctrl-C to stop.");
        println!();
    }

    // Initial test run
    if !quiet {
        println!("=== Initial Run ===");
    }
    let result = run_tests(options.clone());
    print_summary(&result, options.format);

    // Set up filesystem watch
    let (tx, rx) = channel();
    let mut watcher: RecommendedWatcher = RecommendedWatcher::new(tx, Config::default())
        .map_err(|e| format!("Failed to initialize watcher: {}", e))?;

    watcher
        .watch(&test_path, RecursiveMode::Recursive)
        .map_err(|e| format!("Failed to watch path: {}", e))?;

    if !quiet {
        println!();
        println!("Watching for changes...");
    }

    loop {
        match rx.recv() {
            Ok(Ok(event)) => {
                // Only respond to modify, create, and remove events
                if !matches!(
                    event.kind,
                    EventKind::Modify(_) | EventKind::Create(_) | EventKind::Remove(_)
                ) {
                    continue;
                }

                // Check if any changed file is a test file
                let has_test_changes = event.paths.iter().any(|p| {
                    p.extension()
                        .and_then(|e| e.to_str())
                        .map(|e| e == "spl")
                        .unwrap_or(false)
                        && is_test_file(p)
                });

                if !has_test_changes {
                    continue;
                }

                if !quiet {
                    println!();
                    println!("=== Change Detected ===");
                    for path in &event.paths {
                        if is_test_file(path) {
                            println!("Changed: {}", path.display());
                        }
                    }
                    println!();
                }

                // Re-run tests
                let start = Instant::now();
                let result = run_tests(options.clone());
                let duration = start.elapsed();

                if !quiet {
                    print_summary(&result, options.format);
                    println!();
                    println!(
                        "Completed in {:.2}s. Watching for changes...",
                        duration.as_secs_f64()
                    );
                }
            }
            Ok(Err(e)) => {
                if !quiet {
                    eprintln!("Watch error: {}", e);
                }
            }
            Err(_) => break,
        }
    }

    Ok(())
}

// Allow unused for parse_test_output - it's available for future use
#[allow(dead_code)]
fn _unused() {
    let _ = parse_test_output("");
}
