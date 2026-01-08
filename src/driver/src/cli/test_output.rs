// Test output formatting and documentation generation
//
// This module handles:
// - Text/JSON/Doc format output
// - HTML documentation generation
// - Markdown documentation generation

use std::path::Path;

use super::test_runner::{OutputFormat, TestRunResult};

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
            Some(e) => format!("\"{}\"", e.as_str().replace('\"', "\\\"").replace('\n', "\\n")),
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
            for line in err.as_str().lines().take(3) {
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
pub fn generate_documentation(result: &TestRunResult) -> Result<(), Box<dyn std::error::Error>> {
    use std::fs;
    use std::path::PathBuf;

    // Create docs directory
    let docs_dir = PathBuf::from("docs");
    fs::create_dir_all(&docs_dir)?;

    // Build spec results structure for formatters
    let _spec_results = build_spec_results(result);

    // Convert to Simple language dict format and call formatters
    // For now, generate simple documentation files directly
    generate_html_doc(&docs_dir, result)?;
    generate_markdown_doc(&docs_dir, result)?;
    
    // Generate BDD-style documentation from sspec files
    generate_sspec_documentation(result, &docs_dir)?;

    Ok(())
}

/// Generate BDD documentation from sspec test files
fn generate_sspec_documentation(
    result: &TestRunResult,
    docs_dir: &std::path::Path,
) -> Result<(), Box<dyn std::error::Error>> {
    use super::sspec_docgen;
    use std::path::PathBuf;
    
    // Find all sspec files from test results
    let sspec_files: Vec<PathBuf> = result
        .files
        .iter()
        .map(|f| f.path.clone())
        .filter(|p| {
            p.file_name()
                .and_then(|n| n.to_str())
                .map(|n| n.ends_with("_spec.spl"))
                .unwrap_or(false)
        })
        .collect();
    
    if sspec_files.is_empty() {
        return Ok(());
    }
    
    // Generate documentation in docs/spec/
    let spec_dir = docs_dir.join("spec");
    sspec_docgen::generate_sspec_docs(&sspec_files, &spec_dir)?;
    
    Ok(())
}

/// Generate HTML documentation file
fn generate_html_doc(
    docs_dir: &Path,
    result: &TestRunResult,
) -> Result<(), Box<dyn std::error::Error>> {
    use std::fs::File;
    use std::io::Write;

    let timestamp = chrono::Local::now().format("%Y-%m-%d %H:%M:%S").to_string();
    let mut html = String::from(
        r#"<!DOCTYPE html>
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
        <div class="timestamp">Generated: "#,
    );

    html.push_str(&timestamp);
    html.push_str("</div>\n");

    // Add test files
    for file in &result.files {
        let status_class = if file.failed > 0 || file.error.is_some() {
            "failure"
        } else {
            "success"
        };
        let icon = if file.failed > 0 || file.error.is_some() {
            "❌"
        } else {
            "✅"
        };

        html.push_str(&format!(
            r#"        <div class="test-file {}">
            <div class="test-title">
                <span class="status-icon">{}</span>
                {} ({}ms)
            </div>
"#,
            status_class,
            icon,
            file.path.display(),
            file.duration_ms
        ));

        if let Some(ref err) = file.error {
            html.push_str(&format!(
                r#"            <div class="error">{}</div>
"#,
                html_escape(err)
            ));
        }

        html.push_str("        </div>\n");
    }

    // Add summary
    html.push_str(&format!(
        r#"        <div class="summary">
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
</html>"#,
        result.files.len(),
        result.total_passed,
        result.total_failed,
        result.total_duration_ms
    ));

    let html_path = docs_dir.join("test-spec.html");
    let mut file = File::create(html_path)?;
    file.write_all(html.as_bytes())?;

    Ok(())
}

/// Generate Markdown documentation file
fn generate_markdown_doc(
    docs_dir: &Path,
    result: &TestRunResult,
) -> Result<(), Box<dyn std::error::Error>> {
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

        let icon = if file.failed > 0 || file.error.is_some() {
            "❌"
        } else {
            "✅"
        };
        let file_name = parts.last().unwrap_or(&"");

        md.push_str(&format!(
            "{} **{}** ({}ms)\n",
            icon, file_name, file.duration_ms
        ));

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
