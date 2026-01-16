//! Test runner CLI command for Simple language.
//!
//! Provides a unified test runner that discovers and executes tests
//! in the BDD spec format (*_spec.spl, *_test.spl).

use std::path::{Path, PathBuf};
use std::time::Instant;

use simple_compiler::{
    get_coverage_output_path, get_global_coverage, init_coverage, is_coverage_enabled,
    runtime_profile::{
        generate_arch_from_events, generate_class_from_events, generate_sequence_from_events, global_profiler,
        DiagramOptions,
    },
    save_global_coverage,
};
use simple_driver::doctest::{discover_doctests, discover_md_doctests, run_examples, DoctestStatus};
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
    /// Run doctests from .spl files in src directory
    pub doctest_src: bool,
    /// Run doctests from .md files in doc directory
    pub doctest_doc: bool,
    /// Run doctests from .md files using README.md hierarchy
    pub doctest_md: bool,
    /// Source directory for doctest discovery (default: "src" or "simple/std_lib")
    pub doctest_src_dir: Option<PathBuf>,
    /// Doc directory for doctest discovery (default: "doc")
    pub doctest_doc_dir: Option<PathBuf>,
    /// Root directory for README.md-based doctest discovery
    pub doctest_md_dir: Option<PathBuf>,
    /// Generate sequence diagrams for tests
    pub seq_diagram: bool,
    /// Generate class diagrams from sequences
    pub class_diagram: bool,
    /// Generate architecture diagrams
    pub arch_diagram: bool,
    /// Generate all diagram types
    pub diagram_all: bool,
    /// Include filter for diagrams (comma-separated patterns)
    pub seq_include: Option<String>,
    /// Exclude filter for diagrams (comma-separated patterns)
    pub seq_exclude: Option<String>,
    /// Output directory for diagrams
    pub diagram_output: Option<PathBuf>,
    /// Capture GUI screenshots for @gui tagged tests
    pub capture_screenshots: bool,
    /// Force refresh all GUI screenshots (recapture even if exists)
    pub refresh_gui_images: bool,
    /// Output directory for GUI screenshots (default: doc/spec/image)
    pub screenshot_output: Option<PathBuf>,
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
            doctest_src: false,
            doctest_doc: false,
            doctest_md: false,
            doctest_src_dir: None,
            doctest_doc_dir: None,
            doctest_md_dir: None,
            seq_diagram: false,
            class_diagram: false,
            arch_diagram: false,
            diagram_all: false,
            seq_include: None,
            seq_exclude: None,
            diagram_output: None,
            capture_screenshots: false,
            refresh_gui_images: false,
            screenshot_output: None,
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
            let numbers: Vec<usize> = parts.iter().filter_map(|p| p.parse::<usize>().ok()).collect();

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

/// Run doctests from configured directories
fn run_doctests(options: &TestOptions, quiet: bool) -> Vec<TestFileResult> {
    let mut results = Vec::new();
    let cwd = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));

    // Collect doctest source directories
    let mut doctest_paths = Vec::new();

    if options.doctest_src {
        let src_dir = options.doctest_src_dir.clone().unwrap_or_else(|| {
            // Try common source directories
            for dir in &["src", "simple/std_lib", "lib"] {
                let p = cwd.join(dir);
                if p.is_dir() {
                    return p;
                }
            }
            cwd.join("src")
        });

        if src_dir.is_dir() {
            if !quiet {
                println!("Discovering doctests in: {}", src_dir.display());
            }
            doctest_paths.push(src_dir);
        }
    }

    if options.doctest_doc {
        let doc_dir = options.doctest_doc_dir.clone().unwrap_or_else(|| cwd.join("doc"));

        if doc_dir.is_dir() {
            if !quiet {
                println!("Discovering doctests in: {}", doc_dir.display());
            }
            doctest_paths.push(doc_dir);
        }
    }

    // Discover and run doctests
    for path in doctest_paths {
        match discover_doctests(&path) {
            Ok(examples) => {
                if examples.is_empty() {
                    continue;
                }

                if !quiet {
                    println!("Found {} doctest example(s) in {}", examples.len(), path.display());
                }

                let start = Instant::now();
                let doctest_results = run_examples(&examples);
                let duration_ms = start.elapsed().as_millis() as u64;

                // Group results by source file
                let mut file_results: std::collections::HashMap<PathBuf, (usize, usize, Vec<String>)> =
                    std::collections::HashMap::new();

                for result in doctest_results {
                    let entry = file_results
                        .entry(result.example.source.clone())
                        .or_insert((0, 0, Vec::new()));

                    match result.status {
                        DoctestStatus::Passed => entry.0 += 1,
                        DoctestStatus::Failed(msg) => {
                            entry.1 += 1;
                            let section = result
                                .example
                                .section_name
                                .as_ref()
                                .map(|s| format!(" [{}]", s))
                                .unwrap_or_default();
                            entry.2.push(format!(
                                "Line {}{}:\n  Expected: {:?}\n  Actual: {}\n  Error: {}",
                                result.example.start_line, section, result.example.expected, result.actual, msg
                            ));
                        }
                    }
                }

                for (source_path, (passed, failed, errors)) in file_results {
                    let error = if errors.is_empty() {
                        None
                    } else {
                        Some(errors.join("\n"))
                    };

                    if !quiet {
                        let status = if failed > 0 {
                            "\x1b[31mFAILED\x1b[0m"
                        } else {
                            "\x1b[32mPASSED\x1b[0m"
                        };
                        println!(
                            "  Doctest: {} {} ({} passed, {} failed)",
                            source_path.display(),
                            status,
                            passed,
                            failed
                        );
                    }

                    results.push(TestFileResult {
                        path: source_path,
                        passed,
                        failed,
                        duration_ms: duration_ms / (results.len() as u64 + 1).max(1),
                        error,
                    });
                }
            }
            Err(e) => {
                if !quiet {
                    eprintln!("Warning: Failed to discover doctests in {}: {}", path.display(), e);
                }
            }
        }
    }

    results
}

/// Run README.md-based doctests
fn run_md_doctests(options: &TestOptions, quiet: bool) -> Vec<TestFileResult> {
    let mut results = Vec::new();
    let cwd = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));

    let doc_dir = options.doctest_md_dir.clone().unwrap_or_else(|| cwd.join("doc"));

    if !doc_dir.is_dir() {
        if !quiet {
            eprintln!("Warning: Doc directory not found: {}", doc_dir.display());
        }
        return results;
    }

    if !quiet {
        println!("Discovering README.md doctests in: {}", doc_dir.display());
    }

    match discover_md_doctests(&doc_dir) {
        Ok(examples) => {
            if examples.is_empty() {
                if !quiet {
                    println!("  No doctests found in README.md hierarchy");
                }
                return results;
            }

            if !quiet {
                println!("Found {} doctest example(s) via README.md hierarchy", examples.len());
            }

            let start = Instant::now();
            let doctest_results = run_examples(&examples);
            let duration_ms = start.elapsed().as_millis() as u64;

            // Group results by source file
            let mut file_results: std::collections::HashMap<PathBuf, (usize, usize, Vec<String>)> =
                std::collections::HashMap::new();

            for result in doctest_results {
                let entry = file_results
                    .entry(result.example.source.clone())
                    .or_insert((0, 0, Vec::new()));

                match result.status {
                    DoctestStatus::Passed => entry.0 += 1,
                    DoctestStatus::Failed(msg) => {
                        entry.1 += 1;
                        let section = result
                            .example
                            .section_name
                            .as_ref()
                            .map(|s| format!(" [{}]", s))
                            .unwrap_or_default();
                        entry.2.push(format!(
                            "Line {}{}:\n  Expected: {:?}\n  Actual: {}\n  Error: {}",
                            result.example.start_line, section, result.example.expected, result.actual, msg
                        ));
                    }
                }
            }

            for (source_path, (passed, failed, errors)) in file_results {
                let error = if errors.is_empty() {
                    None
                } else {
                    Some(errors.join("\n"))
                };

                if !quiet {
                    let status = if failed > 0 {
                        "\x1b[31mFAILED\x1b[0m"
                    } else {
                        "\x1b[32mPASSED\x1b[0m"
                    };
                    println!(
                        "  MD Doctest: {} {} ({} passed, {} failed)",
                        source_path.display(),
                        status,
                        passed,
                        failed
                    );
                }

                results.push(TestFileResult {
                    path: source_path,
                    passed,
                    failed,
                    duration_ms: duration_ms / (results.len() as u64 + 1).max(1),
                    error,
                });
            }
        }
        Err(e) => {
            if !quiet {
                eprintln!("Warning: Failed to discover README.md doctests: {}", e);
            }
        }
    }

    results
}

/// Run tests with the given options
pub fn run_tests(options: TestOptions) -> TestRunResult {
    let quiet = matches!(options.format, OutputFormat::Json);

    // Enable diagram recording if any diagram option is enabled
    let diagrams_enabled = options.seq_diagram || options.class_diagram || options.arch_diagram || options.diagram_all;
    if diagrams_enabled {
        simple_runtime::value::diagram_ffi::enable_diagrams();
        simple_runtime::value::diagram_ffi::clear_diagram_data();
        if !quiet {
            println!("Call flow diagram recording enabled");
        }
    }

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

    // Print discovery summary
    if !quiet {
        let spec_count = test_files
            .iter()
            .filter(|p| {
                p.file_name()
                    .and_then(|n| n.to_str())
                    .map(|n| n.ends_with("_spec.spl"))
                    .unwrap_or(false)
            })
            .count();
        let test_count = test_files.len() - spec_count;

        println!("───────────────────────────────────────────────────────────────");
        println!("Test Discovery");
        println!("───────────────────────────────────────────────────────────────");
        println!("  Spec files (*_spec.spl):  {}", spec_count);
        println!("  Test files (*_test.spl):  {}", test_count);

        // Count doctests if enabled
        if options.doctest_src || options.doctest_doc {
            let cwd = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
            let src_dir = options
                .doctest_src_dir
                .clone()
                .unwrap_or_else(|| cwd.join("simple/std_lib/src"));
            let doc_dir = options.doctest_doc_dir.clone().unwrap_or_else(|| cwd.join("doc"));

            if options.doctest_src && src_dir.is_dir() {
                if let Ok(examples) = discover_doctests(&src_dir) {
                    println!("  Src doctests (.spl):      {}", examples.len());
                }
            }
            if options.doctest_doc && doc_dir.is_dir() {
                if let Ok(examples) = discover_doctests(&doc_dir) {
                    println!("  Doc doctests (.md):       {}", examples.len());
                }
            }
        }

        if options.doctest_md {
            let cwd = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
            let md_dir = options.doctest_md_dir.clone().unwrap_or_else(|| cwd.join("doc"));

            if md_dir.is_dir() {
                if let Ok(examples) = discover_md_doctests(&md_dir) {
                    println!("  MD doctests (README.md):  {}", examples.len());
                }
            }
        }
        println!("───────────────────────────────────────────────────────────────");
        println!();
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

    if let Err(e) =
        simple_driver::feature_db::update_feature_db_from_sspec(&feature_db_path, &sspec_files, &failed_specs)
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

    // Run doctests if enabled
    if options.doctest_src || options.doctest_doc {
        let doctest_results = run_doctests(&options, quiet);
        for result in doctest_results {
            total_passed += result.passed;
            total_failed += result.failed;
            results.push(result);
        }
    }

    // Run README.md-based doctests if enabled
    if options.doctest_md {
        let md_results = run_md_doctests(&options, quiet);
        for result in md_results {
            total_passed += result.passed;
            total_failed += result.failed;
            results.push(result);
        }
    }

    let result = TestRunResult {
        files: results,
        total_passed,
        total_failed,
        total_duration_ms: start.elapsed().as_millis() as u64,
    };

    // Generate diagrams if enabled
    if options.seq_diagram || options.class_diagram || options.arch_diagram || options.diagram_all {
        if let Some(diagram_paths) = generate_test_diagrams(&options, &result.files, quiet) {
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
            "--doctest" => {
                options.doctest_src = true;
                options.doctest_doc = true;
                options.doctest_md = true;
            }
            "--all" => {
                // Run everything including all doctests
                options.doctest_src = true;
                options.doctest_doc = true;
                options.doctest_md = true;
            }
            "--doctest-src" => options.doctest_src = true,
            "--doctest-doc" => options.doctest_doc = true,
            "--doctest-md" => options.doctest_md = true,
            "--doctest-src-dir" => {
                i += 1;
                if i < args.len() {
                    options.doctest_src_dir = Some(PathBuf::from(&args[i]));
                    options.doctest_src = true;
                }
            }
            "--doctest-doc-dir" => {
                i += 1;
                if i < args.len() {
                    options.doctest_doc_dir = Some(PathBuf::from(&args[i]));
                    options.doctest_doc = true;
                }
            }
            "--doctest-md-dir" => {
                i += 1;
                if i < args.len() {
                    options.doctest_md_dir = Some(PathBuf::from(&args[i]));
                    options.doctest_md = true;
                }
            }
            // Diagram generation options
            "--seq-diagram" => options.seq_diagram = true,
            "--class-diagram" => options.class_diagram = true,
            "--arch-diagram" => options.arch_diagram = true,
            "--diagram-all" => {
                options.diagram_all = true;
                options.seq_diagram = true;
                options.class_diagram = true;
                options.arch_diagram = true;
            }
            "--seq-include" => {
                i += 1;
                if i < args.len() {
                    options.seq_include = Some(args[i].clone());
                }
            }
            "--seq-exclude" => {
                i += 1;
                if i < args.len() {
                    options.seq_exclude = Some(args[i].clone());
                }
            }
            "--diagram-output" => {
                i += 1;
                if i < args.len() {
                    options.diagram_output = Some(PathBuf::from(&args[i]));
                }
            }
            // Screenshot capture options
            "--capture-screenshots" | "--screenshots" => options.capture_screenshots = true,
            "--refresh-gui-image" | "--refresh-screenshots" => {
                options.refresh_gui_images = true;
                options.capture_screenshots = true;
            }
            "--screenshot-output" => {
                i += 1;
                if i < args.len() {
                    options.screenshot_output = Some(PathBuf::from(&args[i]));
                    options.capture_screenshots = true;
                }
            }
            arg if !arg.starts_with("-") && options.path.is_none() => {
                options.path = Some(PathBuf::from(arg));
            }
            _ => {}
        }
        i += 1;
    }

    options
}

/// Generate diagrams from test execution using the global profiler and diagram_ffi
fn generate_test_diagrams(options: &TestOptions, _results: &[TestFileResult], quiet: bool) -> Option<Vec<PathBuf>> {
    use simple_runtime::value::diagram_ffi;
    use std::fs;

    // Get events from global profiler
    let profiler = global_profiler();
    let profiler_events = profiler.get_sequence_events();
    let profiler_architectural = profiler.get_architectural_entities();

    // Get events from diagram_ffi (interpreter tracing)
    let ffi_events = diagram_ffi::get_recorded_events();
    let ffi_architectural = diagram_ffi::get_architectural_entities();

    // Disable diagram recording
    diagram_ffi::disable_diagrams();

    // Check if we have any events from either source
    let has_profiler_events = !profiler_events.is_empty();
    let has_ffi_events = !ffi_events.is_empty();

    if !has_profiler_events && !has_ffi_events {
        if !quiet {
            println!("No sequence events recorded.");
            println!("Hint: Enable profiling with ProfileConfig::combined() or --diagram-all");
        }
        return None;
    }

    // Use FFI events if available, otherwise fall back to profiler events
    let (events, architectural) = if has_ffi_events {
        // Convert FFI events to profiler format
        use simple_compiler::runtime_profile::{CallType as ProfileCallType, SequenceEvent};
        use std::collections::HashSet;

        let converted_events: Vec<_> = ffi_events
            .iter()
            .enumerate()
            .map(|(idx, e)| SequenceEvent {
                sequence_num: idx as u64,
                timestamp_ns: e.timestamp_ns,
                caller: "Test".to_string(),
                callee: e.callee.clone(),
                caller_class: None,
                callee_class: e.callee_class.clone(),
                arguments: e.arguments.clone(),
                return_value: e.return_value.clone(),
                call_type: match e.call_type {
                    diagram_ffi::CallType::Function => ProfileCallType::Direct,
                    diagram_ffi::CallType::Method => ProfileCallType::Method,
                    diagram_ffi::CallType::Constructor => ProfileCallType::Constructor,
                    diagram_ffi::CallType::Return => ProfileCallType::Direct, // Return is tracked via is_return field
                },
                depth: 0,
                is_return: matches!(e.call_type, diagram_ffi::CallType::Return),
            })
            .collect();
        // Convert Vec to HashSet for architectural entities
        let arch_set: HashSet<String> = ffi_architectural.into_iter().collect();
        (converted_events, arch_set)
    } else {
        (profiler_events, profiler_architectural)
    };

    if !quiet && has_ffi_events {
        println!("Using {} events from interpreter call tracing", ffi_events.len());
    }

    // Setup output directory
    let output_dir = options
        .diagram_output
        .clone()
        .unwrap_or_else(|| PathBuf::from("target/diagrams"));

    if let Err(e) = fs::create_dir_all(&output_dir) {
        if !quiet {
            eprintln!("Failed to create diagram output directory: {}", e);
        }
        return None;
    }

    // Build diagram options
    let mut diagram_opts = DiagramOptions::new()
        .with_timing(true)
        .with_args(true)
        .with_returns(true);

    if let Some(ref include) = options.seq_include {
        for pattern in include.split(',') {
            diagram_opts = diagram_opts.with_include(pattern.trim());
        }
    }
    if let Some(ref exclude) = options.seq_exclude {
        for pattern in exclude.split(',') {
            diagram_opts = diagram_opts.with_exclude(pattern.trim());
        }
    }

    let mut paths = Vec::new();

    // Generate sequence diagram
    if options.seq_diagram || options.diagram_all {
        let content = generate_sequence_from_events(&events, &diagram_opts);
        let path = output_dir.join("test_sequence.md");
        if let Err(e) = fs::write(&path, &content) {
            if !quiet {
                eprintln!("Failed to write sequence diagram: {}", e);
            }
        } else {
            paths.push(path);
        }
    }

    // Generate class diagram
    if options.class_diagram || options.diagram_all {
        let content = generate_class_from_events(&events, &diagram_opts);
        let path = output_dir.join("test_class.md");
        if let Err(e) = fs::write(&path, &content) {
            if !quiet {
                eprintln!("Failed to write class diagram: {}", e);
            }
        } else {
            paths.push(path);
        }
    }

    // Generate architecture diagram
    if options.arch_diagram || options.diagram_all {
        let content = generate_arch_from_events(&events, &architectural, &diagram_opts);
        let path = output_dir.join("test_arch.md");
        if let Err(e) = fs::write(&path, &content) {
            if !quiet {
                eprintln!("Failed to write architecture diagram: {}", e);
            }
        } else {
            paths.push(path);
        }
    }

    if paths.is_empty() {
        None
    } else {
        Some(paths)
    }
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
    let mut watcher: RecommendedWatcher =
        RecommendedWatcher::new(tx, Config::default()).map_err(|e| format!("Failed to initialize watcher: {}", e))?;

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
                    println!("Completed in {:.2}s. Watching for changes...", duration.as_secs_f64());
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
