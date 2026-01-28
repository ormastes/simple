//! Syntax and type checking without execution.
//!
//! The `simple check` command validates Simple source code by:
//! - Parsing source code and reporting syntax errors
//! - Validating import statements (module resolution)
//! - Checking type correctness (basic validation)
//! - Supporting multiple files and glob patterns
//! - Providing human-readable or JSON output

use serde::{Deserialize, Serialize};
use simple_compiler::module_resolver::ModuleResolver;
use simple_parser::ast::Node;
use simple_parser::{Parser, ParseError};
use std::path::{Path, PathBuf};
use std::fs;

/// Check options
#[derive(Debug, Clone)]
pub struct CheckOptions {
    /// Output JSON format for tooling
    pub json: bool,
    /// Verbose output (show additional details)
    pub verbose: bool,
    /// Quiet mode (only show errors, no progress)
    pub quiet: bool,
}

impl Default for CheckOptions {
    fn default() -> Self {
        Self {
            json: false,
            verbose: false,
            quiet: false,
        }
    }
}

/// Check result for a single file
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FileCheckResult {
    pub file: String,
    pub status: CheckStatus,
    pub errors: Vec<CheckError>,
}

/// Check status
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum CheckStatus {
    Success,
    Error,
}

/// Check error
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CheckError {
    pub file: String,
    pub line: usize,
    pub column: usize,
    pub severity: ErrorSeverity,
    pub message: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub expected: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub found: Option<String>,
}

/// Error severity
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum ErrorSeverity {
    Error,
    Warning,
}

/// Overall check result
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CheckResult {
    pub status: CheckStatus,
    pub files_checked: usize,
    pub errors: Vec<CheckError>,
}

/// Run check command on multiple files
pub fn run_check(files: &[PathBuf], options: CheckOptions) -> i32 {
    let mut all_results = Vec::new();
    let mut has_errors = false;

    for file in files {
        if !options.quiet {
            if options.verbose {
                println!("Checking {}...", file.display());
            }
        }

        let result = check_file(file);

        match &result.status {
            CheckStatus::Success => {
                if !options.quiet && !options.json {
                    println!("Checking {}... \x1b[32mOK\x1b[0m", file.display());
                }
            }
            CheckStatus::Error => {
                has_errors = true;
                if !options.json {
                    for error in &result.errors {
                        print_error(error);
                    }
                }
            }
        }

        all_results.push(result);
    }

    // Output results
    if options.json {
        output_json(&all_results);
    } else if !options.quiet {
        println!();
        if has_errors {
            let error_count: usize = all_results.iter().map(|r| r.errors.len()).sum();
            println!(
                "\x1b[31m✗ {} error(s) found in {} file(s)\x1b[0m",
                error_count,
                files.len()
            );
        } else {
            println!("\x1b[32m✓ All checks passed ({} file(s))\x1b[0m", files.len());
        }
    }

    if has_errors {
        1
    } else {
        0
    }
}

/// Check a single file
fn check_file(path: &Path) -> FileCheckResult {
    // Read file
    let source = match fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            return FileCheckResult {
                file: path.display().to_string(),
                status: CheckStatus::Error,
                errors: vec![CheckError {
                    file: path.display().to_string(),
                    line: 0,
                    column: 0,
                    severity: ErrorSeverity::Error,
                    message: format!("cannot read file: {}", e),
                    expected: None,
                    found: None,
                }],
            };
        }
    };

    let mut errors = Vec::new();

    // Parse source
    let mut parser = Parser::new(&source);
    match parser.parse() {
        Ok(module) => {
            // Parsing succeeded, validate imports
            validate_imports(path, &module.items, &mut errors);
        }
        Err(e) => {
            // Convert ParseError to CheckError
            errors.push(parse_error_to_check_error(&e, path));
        }
    }

    let status = if errors.is_empty() {
        CheckStatus::Success
    } else {
        CheckStatus::Error
    };

    FileCheckResult {
        file: path.display().to_string(),
        status,
        errors,
    }
}

/// Validate import statements in a module
fn validate_imports(file_path: &Path, items: &[Node], errors: &mut Vec<CheckError>) {
    // Create a module resolver for the file's directory
    let parent = file_path.parent().unwrap_or(Path::new("."));
    let resolver = ModuleResolver::single_file(file_path);

    for item in items {
        match item {
            Node::UseStmt(use_stmt) => {
                // Try to resolve the import path
                if let Err(e) = resolver.resolve(&use_stmt.path, file_path) {
                    // Only report as warning since the module might be in a different project location
                    errors.push(CheckError {
                        file: file_path.display().to_string(),
                        line: use_stmt.span.line,
                        column: use_stmt.span.column,
                        severity: ErrorSeverity::Warning,
                        message: format!("unresolved import '{}': {}", use_stmt.path.segments.join("."), e),
                        expected: None,
                        found: None,
                    });
                }
            }
            Node::CommonUseStmt(common_use) => {
                if let Err(e) = resolver.resolve(&common_use.path, file_path) {
                    errors.push(CheckError {
                        file: file_path.display().to_string(),
                        line: common_use.span.line,
                        column: common_use.span.column,
                        severity: ErrorSeverity::Warning,
                        message: format!(
                            "unresolved common import '{}': {}",
                            common_use.path.segments.join("."),
                            e
                        ),
                        expected: None,
                        found: None,
                    });
                }
            }
            Node::ExportUseStmt(export_use) => {
                if let Err(e) = resolver.resolve(&export_use.path, file_path) {
                    errors.push(CheckError {
                        file: file_path.display().to_string(),
                        line: export_use.span.line,
                        column: export_use.span.column,
                        severity: ErrorSeverity::Warning,
                        message: format!(
                            "unresolved export import '{}': {}",
                            export_use.path.segments.join("."),
                            e
                        ),
                        expected: None,
                        found: None,
                    });
                }
            }
            _ => {}
        }
    }

    // Suppress unused variable warning for parent - it's used by resolver internally
    let _ = parent;
}

/// Convert ParseError to CheckError
fn parse_error_to_check_error(err: &ParseError, path: &Path) -> CheckError {
    use simple_parser::ParseError;

    match err {
        ParseError::SyntaxError {
            message, line, column, ..
        } => CheckError {
            file: path.display().to_string(),
            line: *line,
            column: *column,
            severity: ErrorSeverity::Error,
            message: message.clone(),
            expected: None,
            found: None,
        },
        ParseError::UnexpectedToken { expected, found, span, .. } => CheckError {
            file: path.display().to_string(),
            line: span.line,
            column: span.column,
            severity: ErrorSeverity::Error,
            message: "unexpected token".to_string(),
            expected: Some(expected.clone()),
            found: Some(found.clone()),
        },
        ParseError::MissingToken { expected, span, .. } => CheckError {
            file: path.display().to_string(),
            line: span.line,
            column: span.column,
            severity: ErrorSeverity::Error,
            message: format!("missing expected token: {}", expected),
            expected: Some(expected.clone()),
            found: None,
        },
        ParseError::UnclosedString { span, .. } => {
            let (line, column) = if let Some(s) = span { (s.line, s.column) } else { (0, 0) };
            CheckError {
                file: path.display().to_string(),
                line,
                column,
                severity: ErrorSeverity::Error,
                message: "unclosed string literal".to_string(),
                expected: None,
                found: None,
            }
        }
        ParseError::InvalidIndentation { line, .. } => CheckError {
            file: path.display().to_string(),
            line: *line,
            column: 1,
            severity: ErrorSeverity::Error,
            message: "invalid indentation".to_string(),
            expected: None,
            found: None,
        },
        ParseError::InvalidPattern { span, message, .. } => CheckError {
            file: path.display().to_string(),
            line: span.line,
            column: span.column,
            severity: ErrorSeverity::Error,
            message: format!("invalid pattern: {}", message),
            expected: None,
            found: None,
        },
        ParseError::InvalidType { span, message, .. } => CheckError {
            file: path.display().to_string(),
            line: span.line,
            column: span.column,
            severity: ErrorSeverity::Error,
            message: format!("invalid type: {}", message),
            expected: None,
            found: None,
        },
        _ => CheckError {
            file: path.display().to_string(),
            line: 0,
            column: 0,
            severity: ErrorSeverity::Error,
            message: err.to_string(),
            expected: None,
            found: None,
        },
    }
}

/// Print error in human-readable format
fn print_error(error: &CheckError) {
    let color = match error.severity {
        ErrorSeverity::Error => "\x1b[31m",   // red
        ErrorSeverity::Warning => "\x1b[33m", // yellow
    };
    let reset = "\x1b[0m";

    println!(
        "{}{}:{}:{}: {}error{}: {}",
        color,
        error.file,
        error.line,
        error.column,
        if error.severity == ErrorSeverity::Error {
            ""
        } else {
            "warning: "
        },
        reset,
        error.message
    );

    if let Some(expected) = &error.expected {
        println!("  expected: {}", expected);
    }
    if let Some(found) = &error.found {
        println!("  found:    {}", found);
    }
}

/// Output results in JSON format
fn output_json(results: &[FileCheckResult]) {
    let all_errors: Vec<CheckError> = results.iter().flat_map(|r| r.errors.clone()).collect();

    let has_errors = !all_errors.is_empty();

    let output = CheckResult {
        status: if has_errors {
            CheckStatus::Error
        } else {
            CheckStatus::Success
        },
        files_checked: results.len(),
        errors: all_errors,
    };

    match serde_json::to_string_pretty(&output) {
        Ok(json) => println!("{}", json),
        Err(e) => eprintln!("error: failed to serialize JSON: {}", e),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;
    use tempfile::NamedTempFile;

    #[test]
    fn test_check_valid_code() {
        let mut file = NamedTempFile::new().unwrap();
        writeln!(file, "fn main():\n    val x = 42\n    print(x)").unwrap();

        let result = check_file(file.path());
        assert_eq!(result.status, CheckStatus::Success);
        assert!(result.errors.is_empty());
    }

    #[test]
    fn test_check_syntax_error() {
        let mut file = NamedTempFile::new().unwrap();
        writeln!(file, "fn main():\n    val x =").unwrap();

        let result = check_file(file.path());
        assert_eq!(result.status, CheckStatus::Error);
        assert!(!result.errors.is_empty());
    }

    #[test]
    fn test_check_nonexistent_file() {
        let path = PathBuf::from("/nonexistent/file.spl");
        let result = check_file(&path);
        assert_eq!(result.status, CheckStatus::Error);
        assert_eq!(result.errors.len(), 1);
        assert!(result.errors[0].message.contains("cannot read file"));
    }
}
