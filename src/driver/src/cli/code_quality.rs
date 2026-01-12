//! Code quality commands: lint and format.

use simple_common::diagnostic::Diagnostics;
use simple_compiler::{LintChecker, LintConfig};
use simple_parser::Parser;
use std::fs;
use std::path::PathBuf;
use walkdir::WalkDir;

/// Run the linter on a file or directory
pub fn run_lint(args: &[String]) -> i32 {
    // Parse arguments
    let path = args
        .get(1)
        .map(|s| PathBuf::from(s))
        .unwrap_or_else(|| PathBuf::from("."));
    let json_output = args.iter().any(|a| a == "--json");
    let fix = args.iter().any(|a| a == "--fix");

    if fix {
        eprintln!("error: --fix flag is not yet implemented");
        return 1;
    }

    // Check if path is directory
    if path.is_dir() {
        return lint_directory(&path, json_output);
    }

    // Lint single file
    lint_file(&path, json_output)
}

/// Lint all .spl files in a directory
pub fn lint_directory(dir: &PathBuf, json_output: bool) -> i32 {
    let mut all_errors = false;
    let mut total_errors = 0;
    let mut total_warnings = 0;
    let mut all_diags = Diagnostics::new();

    for entry in WalkDir::new(dir)
        .follow_links(true)
        .into_iter()
        .filter_map(|e| e.ok())
        .filter(|e| e.path().extension().and_then(|s| s.to_str()) == Some("spl"))
    {
        let path = entry.path();
        let result = lint_file_internal(path, false);

        if let Some((has_err, err_count, warn_count, diags)) = result {
            if has_err {
                all_errors = true;
            }
            total_errors += err_count;
            total_warnings += warn_count;

            if json_output {
                for diag in diags {
                    all_diags.push(diag);
                }
            }
        }
    }

    if json_output {
        match all_diags.to_json() {
            Ok(json) => println!("{}", json),
            Err(e) => {
                eprintln!("error: failed to serialize diagnostics: {}", e);
                return 1;
            }
        }
    } else {
        println!();
        println!(
            "Total: {} error(s), {} warning(s) across {} file(s)",
            total_errors,
            total_warnings,
            WalkDir::new(dir)
                .into_iter()
                .filter(|e| e
                    .as_ref()
                    .ok()
                    .and_then(|e| e.path().extension().and_then(|s| s.to_str()))
                    == Some("spl"))
                .count()
        );
    }

    if all_errors {
        1
    } else {
        0
    }
}

/// Lint a single file
pub fn lint_file(path: &PathBuf, json_output: bool) -> i32 {
    if let Some((has_errors, _, _, diags)) = lint_file_internal(path, json_output) {
        if json_output {
            // Single file JSON output
            let mut all_diags = Diagnostics::new();
            for diag in diags {
                all_diags.push(diag);
            }
            match all_diags.to_json() {
                Ok(json) => println!("{}", json),
                Err(e) => {
                    eprintln!("error: failed to serialize diagnostics: {}", e);
                    return 1;
                }
            }
        }
        if has_errors {
            1
        } else {
            0
        }
    } else {
        1
    }
}

/// Internal lint function that returns diagnostic information
pub fn lint_file_internal(
    path: &std::path::Path,
    json_output: bool,
) -> Option<(
    bool,
    usize,
    usize,
    Vec<simple_common::diagnostic::Diagnostic>,
)> {
    // Read file
    let source = match fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            if !json_output {
                eprintln!("error: cannot read {}: {}", path.display(), e);
            }
            return None;
        }
    };

    // Parse file
    let mut parser = Parser::new(&source);
    let module = match parser.parse() {
        Ok(m) => m,
        Err(e) => {
            if !json_output {
                eprintln!("error: parse failed in {}: {}", path.display(), e);
            }
            return None;
        }
    };

    // Create lint checker
    let config = LintConfig::default();
    let mut checker = LintChecker::with_config(config);

    // Run lint checks
    checker.check_module(&module.items);
    let diagnostics = checker.diagnostics();

    let error_count = diagnostics.iter().filter(|d| d.is_error()).count();
    let warning_count = diagnostics.len() - error_count;
    let has_errors = error_count > 0;

    // Convert to common diagnostics
    let common_diags: Vec<simple_common::diagnostic::Diagnostic> = diagnostics
        .iter()
        .map(|d| d.to_diagnostic(Some(path.display().to_string())))
        .collect();

    if json_output {
        // Return diagnostics for aggregation
    } else {
        // Human-readable output
        if diagnostics.is_empty() {
            println!("{}: OK", path.display());
        } else {
            for diagnostic in diagnostics {
                // Format: file:line:col: level: message
                let span = &diagnostic.span;
                let level_str = if diagnostic.is_error() {
                    "error"
                } else {
                    "warning"
                };
                println!(
                    "{}:{}:{}: {}: {} [{}]",
                    path.display(),
                    span.line,
                    span.column,
                    level_str,
                    diagnostic.message,
                    diagnostic.lint.as_str()
                );
                if let Some(suggestion) = &diagnostic.suggestion {
                    println!("  help: {}", suggestion);
                }
            }
        }
    }

    Some((has_errors, error_count, warning_count, common_diags))
}

/// Run the formatter on a file or directory
pub fn run_fmt(args: &[String]) -> i32 {
    // Parse arguments
    let path = args
        .get(1)
        .map(|s| PathBuf::from(s))
        .unwrap_or_else(|| PathBuf::from("."));
    let check_only = args.iter().any(|a| a == "--check");

    // Read file
    let source = match fs::read_to_string(&path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: cannot read {}: {}", path.display(), e);
            return 1;
        }
    };

    // TODO: [driver][P1] Implement actual formatting logic
    // For now, this is a placeholder that validates the file can be parsed
    let mut parser = Parser::new(&source);
    match parser.parse() {
        Ok(_) => {
            if check_only {
                println!("{}: formatted correctly", path.display());
                0
            } else {
                println!(
                    "{}: would format (formatter not yet implemented)",
                    path.display()
                );
                0
            }
        }
        Err(e) => {
            eprintln!("error: parse failed: {}", e);
            1
        }
    }
}
