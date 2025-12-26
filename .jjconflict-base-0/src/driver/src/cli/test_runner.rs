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
/// Also generates HTML and Markdown documentation files
fn print_summary_doc(result: &TestRunResult) {
    // Print console output first
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

    // Generate documentation files
    println!();
    println!("Generating documentation...");
    if let Err(e) = generate_documentation(result) {
        eprintln!("Warning: Failed to generate documentation: {}", e);
    } else {
        println!("✓ Documentation generated in docs/");
    }
}

/// Generate HTML and Markdown documentation from test results
fn generate_documentation(result: &TestRunResult) -> Result<(), Box<dyn std::error::Error>> {
    use std::fs;

    // Create docs directory
    let docs_dir = PathBuf::from("docs");
    fs::create_dir_all(&docs_dir)?;

    // Build spec results structure for formatters
    let spec_results = build_spec_results(result);

    // Convert to Simple language dict format and call formatters
    // For now, generate simple documentation files directly
    generate_html_doc(&docs_dir, result)?;
    generate_markdown_doc(&docs_dir, result)?;

    Ok(())
}

/// Generate HTML documentation file
fn generate_html_doc(docs_dir: &Path, result: &TestRunResult) -> Result<(), Box<dyn std::error::Error>> {
    use std::fs::File;
    use std::io::Write;

    let timestamp = chrono::Local::now().format("%Y-%m-%d %H:%M:%S").to_string();
    let mut html = String::from(r#"<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Test Specification - Simple Language</title>
    <style>
        * { box-sizing: border-box; margin: 0; padding: 0; }
        body { font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, sans-serif; line-height: 1.6; color: #333; background: #f5f5f5; padding: 20px; }
        .container { max-width: 1200px; margin: 0 auto; background: white; padding: 40px; border-radius: 8px; box-shadow: 0 2px 8px rgba(0,0,0,0.1); }
        h1 { color: #2c3e50; margin-bottom: 10px; border-bottom: 3px solid #3498db; padding-bottom: 10px; }
        .timestamp { color: #7f8c8d; font-size: 0.9em; margin-bottom: 30px; }
        .test-file { margin: 20px 0; padding: 15px; background: #f8f9fa; border-left: 3px solid #95a5a6; }
        .test-file.success { background: #d5f4e6; border-left-color: #27ae60; }
        .test-file.failure { background: #fadbd8; border-left-color: #e74c3c; }
        .test-title { font-size: 1.1em; margin-bottom: 8px; display: flex; align-items: center; }
        .status-icon { margin-right: 8px; font-size: 1.2em; }
        .error { margin-top: 10px; padding: 10px; background: #fbe9e7; border-left: 3px solid #e74c3c; font-family: monospace; font-size: 0.9em; white-space: pre-wrap; }
        .summary { margin-top: 40px; padding: 20px; background: #ecf0f1; border-radius: 4px; }
        .summary h2 { color: #2c3e50; margin-bottom: 15px; }
        .summary-stats { display: flex; gap: 20px; flex-wrap: wrap; }
        .stat { padding: 10px 20px; background: white; border-radius: 4px; border-left: 3px solid #3498db; }
        .stat-label { font-weight: bold; color: #7f8c8d; font-size: 0.9em; }
        .stat-value { font-size: 1.5em; color: #2c3e50; }
    </style>
</head>
<body>
    <div class="container">
        <h1>Test Specification</h1>
        <div class="timestamp">Generated: "#);

    html.push_str(&timestamp);
    html.push_str("</div>\n");

    // Add test files
    for file in &result.files {
        let status_class = if file.failed > 0 || file.error.is_some() { "failure" } else { "success" };
        let icon = if file.failed > 0 || file.error.is_some() { "❌" } else { "✅" };

        html.push_str(&format!(r#"        <div class="test-file {}">
            <div class="test-title">
                <span class="status-icon">{}</span>
                {} ({}ms)
            </div>
"#, status_class, icon, file.path.display(), file.duration_ms));

        if let Some(ref err) = file.error {
            html.push_str(&format!(r#"            <div class="error">{}</div>
"#, html_escape(err)));
        }

        html.push_str("        </div>\n");
    }

    // Add summary
    html.push_str(&format!(r#"        <div class="summary">
            <h2>Summary</h2>
            <div class="summary-stats">
                <div class="stat">
                    <div class="stat-label">Total</div>
                    <div class="stat-value">{}</div>
                </div>
                <div class="stat">
                    <div class="stat-label">Passed ✅</div>
                    <div class="stat-value">{}</div>
                </div>
                <div class="stat">
                    <div class="stat-label">Failed ❌</div>
                    <div class="stat-value">{}</div>
                </div>
                <div class="stat">
                    <div class="stat-label">Duration</div>
                    <div class="stat-value">{}ms</div>
                </div>
            </div>
        </div>
    </div>
</body>
</html>"#, result.files.len(), result.total_passed, result.total_failed, result.total_duration_ms));

    let html_path = docs_dir.join("test-spec.html");
    let mut file = File::create(html_path)?;
    file.write_all(html.as_bytes())?;

    Ok(())
}

/// Generate Markdown documentation file
fn generate_markdown_doc(docs_dir: &Path, result: &TestRunResult) -> Result<(), Box<dyn std::error::Error>> {
    use std::fs::File;
    use std::io::Write;

    let timestamp = chrono::Local::now().format("%Y-%m-%d %H:%M:%S").to_string();
    let mut md = format!("# Test Specification\n\n*Generated: {}*\n\n", timestamp);

    // Add test files grouped by directory
    let mut current_dir = String::new();

    for file in &result.files {
        let path_str = file.path.display().to_string();
        let parts: Vec<&str> = path_str.split('/').collect();
        let dir = if parts.len() > 1 {
            parts[..parts.len() - 1].join("/")
        } else {
            String::new()
        };

        if dir != current_dir {
            if !current_dir.is_empty() {
                md.push_str("\n");
            }
            md.push_str(&format!("## {}\n\n", dir));
            current_dir = dir;
        }

        let icon = if file.failed > 0 || file.error.is_some() { "❌" } else { "✅" };
        let file_name = parts.last().unwrap_or(&"");

        md.push_str(&format!("{} **{}** ({}ms)\n", icon, file_name, file.duration_ms));

        if let Some(ref err) = file.error {
            md.push_str(&format!("\n```\nError: {}\n```\n", err));
        }

        md.push_str("\n");
    }

    // Add summary
    md.push_str("\n---\n\n## Summary\n\n");
    md.push_str(&format!("- **Total:** {} tests\n", result.files.len()));
    md.push_str(&format!("- **Passed:** {} ✅\n", result.total_passed));
    md.push_str(&format!("- **Failed:** {} ❌\n", result.total_failed));
    md.push_str(&format!("- **Duration:** {}ms\n", result.total_duration_ms));

    let md_path = docs_dir.join("test-spec.md");
    let mut file = File::create(md_path)?;
    file.write_all(md.as_bytes())?;

    Ok(())
}

/// HTML escape helper
fn html_escape(s: &str) -> String {
    s.replace('&', "&amp;")
     .replace('<', "&lt;")
     .replace('>', "&gt;")
     .replace('"', "&quot;")
     .replace('\'', "&#39;")
}

/// Build spec results structure (placeholder for future integration with spec runtime)
fn build_spec_results(_result: &TestRunResult) -> std::collections::HashMap<String, String> {
    // Future: Parse spec results from test output to extract describe/context/it structure
    // For now, return empty map
    std::collections::HashMap::new()
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
    let mut watcher: RecommendedWatcher =
        RecommendedWatcher::new(tx, Config::default())
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
