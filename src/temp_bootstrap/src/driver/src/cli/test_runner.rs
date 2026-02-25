//! Test runner CLI command for Simple language.
//!
//! Provides a unified test runner that discovers and executes tests
//! in the BDD spec format (*_spec.spl, *_test.spl).

use std::path::{Path, PathBuf};
use std::time::Instant;

use simple_driver::runner::Runner;

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

/// Discover test files in a directory
fn discover_tests(dir: &Path, level: TestLevel) -> Vec<PathBuf> {
    let mut tests = Vec::new();

    if !dir.is_dir() {
        if is_test_file(dir) {
            tests.push(dir.to_path_buf());
        }
        return tests;
    }

    // Walk directory recursively
    if let Ok(entries) = std::fs::read_dir(dir) {
        for entry in entries.filter_map(|e| e.ok()) {
            let path = entry.path();

            if path.is_dir() {
                let dir_name = path.file_name().and_then(|n| n.to_str()).unwrap_or("");

                // Filter by test level based on directory name
                let should_include = match level {
                    TestLevel::All => true,
                    TestLevel::Unit => dir_name == "unit" || !["integration", "system"].contains(&dir_name),
                    TestLevel::Integration => dir_name == "integration",
                    TestLevel::System => dir_name == "system",
                };

                if should_include {
                    tests.extend(discover_tests(&path, level));
                }
            } else if is_test_file(&path) {
                tests.push(path);
            }
        }
    }

    tests.sort();
    tests
}

/// Check if a file is a test file
fn is_test_file(path: &Path) -> bool {
    if let Some(name) = path.file_name().and_then(|n| n.to_str()) {
        let is_spl = name.ends_with(".spl");
        let is_test = name.ends_with("_spec.spl") || name.ends_with("_test.spl");
        is_spl && is_test
    } else {
        false
    }
}

/// Extract tags from a test file.
///
/// Tags can be specified in the file using:
/// - `#[tag("name")]` decorator
/// - `@tag name` comment
/// - `#tag: name` comment
///
/// Also checks if the tag is in the file name (e.g., `slow_spec.spl` matches tag "slow")
fn extract_tags(path: &Path) -> Vec<String> {
    let mut tags = Vec::new();

    // Check file name for tag patterns
    if let Some(name) = path.file_name().and_then(|n| n.to_str()) {
        // e.g., "slow_spec.spl" -> tag "slow", "integration_test.spl" -> tag "integration"
        let stem = name
            .trim_end_matches(".spl")
            .trim_end_matches("_spec")
            .trim_end_matches("_test");
        if !stem.is_empty() {
            // Split by underscore and take potential tag prefixes
            for part in stem.split('_') {
                if !part.is_empty() {
                    tags.push(part.to_lowercase());
                }
            }
        }
    }

    // Try to read file content for tag decorators/comments
    if let Ok(content) = std::fs::read_to_string(path) {
        // Look for #[tag("name")] pattern using simple string matching
        for line in content.lines() {
            let trimmed = line.trim();

            // Match #[tag("name")]
            if let Some(rest) = trimmed.strip_prefix("#[tag(\"") {
                if let Some(end) = rest.find("\")]") {
                    let tag = &rest[..end];
                    tags.push(tag.to_lowercase());
                }
            }

            // Match @tag name (in comments like # @tag slow)
            if let Some(idx) = trimmed.find("@tag ") {
                let after = &trimmed[idx + 5..];
                let tag: String = after.chars().take_while(|c| c.is_alphanumeric() || *c == '_').collect();
                if !tag.is_empty() {
                    tags.push(tag.to_lowercase());
                }
            }

            // Match #tag: name
            if let Some(rest) = trimmed.strip_prefix("#tag:") {
                let tag: String = rest.trim().chars().take_while(|c| c.is_alphanumeric() || *c == '_').collect();
                if !tag.is_empty() {
                    tags.push(tag.to_lowercase());
                }
            }
        }
    }

    // Deduplicate
    tags.sort();
    tags.dedup();
    tags
}

/// Check if a file matches the tag filter.
///
/// Returns true if:
/// - No tag filter is specified (tag is None)
/// - The file's tags contain the filter tag
fn matches_tag(path: &Path, tag_filter: &Option<String>) -> bool {
    match tag_filter {
        None => true,
        Some(filter) => {
            let filter_lower = filter.to_lowercase();
            let tags = extract_tags(path);
            tags.iter().any(|t| t == &filter_lower)
        }
    }
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

    TestRunResult {
        files: results,
        total_passed,
        total_failed,
        total_duration_ms: start.elapsed().as_millis() as u64,
    }
}

/// Print test summary (dispatches to format-specific output)
pub fn print_summary(result: &TestRunResult, format: OutputFormat) {
    match format {
        OutputFormat::Text => print_summary_text(result),
        OutputFormat::Json => print_summary_json(result),
        OutputFormat::Doc => print_summary_doc(result),
    }
}

/// Print text format summary
fn print_summary_text(result: &TestRunResult) {
    println!();
    println!("═══════════════════════════════════════════════════════════════");
    println!("Test Summary");
    println!("═══════════════════════════════════════════════════════════════");
    println!("Files: {}", result.files.len());

    if result.total_failed > 0 {
        println!("\x1b[32mPassed: {}\x1b[0m", result.total_passed);
        println!("\x1b[31mFailed: {}\x1b[0m", result.total_failed);
    } else {
        println!("\x1b[32mPassed: {}\x1b[0m", result.total_passed);
        println!("Failed: 0");
    }

    println!("Duration: {}ms", result.total_duration_ms);
    println!();

    if result.success() {
        println!("\x1b[32m✓ All tests passed!\x1b[0m");
    } else {
        println!("\x1b[31m✗ Some tests failed\x1b[0m");
        println!();
        println!("Failed files:");
        for file in &result.files {
            if file.failed > 0 || file.error.is_some() {
                println!("  - {}", file.path.display());
            }
        }
    }
}

/// Print JSON format summary (CLI-008)
fn print_summary_json(result: &TestRunResult) {
    // Build JSON manually to avoid serde dependency
    println!("{{");
    println!("  \"success\": {},", result.success());
    println!("  \"total_passed\": {},", result.total_passed);
    println!("  \"total_failed\": {},", result.total_failed);
    println!("  \"total_duration_ms\": {},", result.total_duration_ms);
    println!("  \"files\": [");

    for (i, file) in result.files.iter().enumerate() {
        let comma = if i < result.files.len() - 1 { "," } else { "" };
        let error_str = match &file.error {
            Some(e) => format!("\"{}\"", e.replace('\"', "\\\"").replace('\n', "\\n")),
            None => "null".to_string(),
        };
        println!("    {{");
        println!(
            "      \"path\": \"{}\",",
            file.path.display().to_string().replace('\\', "\\\\")
        );
        println!("      \"passed\": {},", file.passed);
        println!("      \"failed\": {},", file.failed);
        println!("      \"duration_ms\": {},", file.duration_ms);
        println!("      \"error\": {}", error_str);
        println!("    }}{}", comma);
    }

    println!("  ]");
    println!("}}");
}

/// Print doc format summary (CLI-009) - nested documentation style like RSpec
fn print_summary_doc(result: &TestRunResult) {
    println!();

    // Group by directory structure
    let mut current_dir = String::new();

    for file in &result.files {
        // Get directory path
        let path_str = file.path.display().to_string();
        let parts: Vec<&str> = path_str.split('/').collect();

        // Find the directory (everything except the file name)
        let dir = if parts.len() > 1 {
            parts[..parts.len() - 1].join("/")
        } else {
            String::new()
        };

        // Print directory header if changed
        if dir != current_dir {
            if !current_dir.is_empty() {
                println!();
            }
            println!("{}", dir);
            current_dir = dir;
        }

        // Get file name
        let file_name = parts.last().unwrap_or(&"");

        // Status indicator
        let status = if file.failed > 0 || file.error.is_some() {
            "\x1b[31m✗\x1b[0m"
        } else {
            "\x1b[32m✓\x1b[0m"
        };

        // Print file with indentation
        println!("  {} {} ({}ms)", status, file_name, file.duration_ms);

        // Print error if any
        if let Some(ref err) = file.error {
            for line in err.lines().take(3) {
                println!("      \x1b[31m{}\x1b[0m", line);
            }
        }
    }

    println!();
    println!("─────────────────────────────────────────────────────────────────");

    // Summary line
    if result.success() {
        println!(
            "\x1b[32m{} examples, 0 failures\x1b[0m ({}ms)",
            result.total_passed, result.total_duration_ms
        );
    } else {
        println!(
            "{} examples, \x1b[31m{} failures\x1b[0m ({}ms)",
            result.total_passed + result.total_failed,
            result.total_failed,
            result.total_duration_ms
        );
    }
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
            arg if !arg.starts_with("-") && options.path.is_none() => {
                options.path = Some(PathBuf::from(arg));
            }
            _ => {}
        }
        i += 1;
    }

    options
}
