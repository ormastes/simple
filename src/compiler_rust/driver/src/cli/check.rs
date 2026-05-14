//! Syntax and type checking without execution.
//!
//! The `simple check` command validates Simple source code by:
//! - Parsing source code and reporting syntax errors
//! - Validating import statements (module resolution)
//! - Checking type correctness (basic validation)
//! - Supporting multiple files and glob patterns
//! - Providing human-readable or JSON output

use serde::{Deserialize, Serialize};
use simple_common::target::Target;
use simple_compiler::module_resolver::ModuleResolver;
use simple_compiler::{LintChecker, LintConfig, LintLevel, LintName};
use simple_parser::ast::{ImportTarget, Node};
use simple_parser::{Parser, ParseError};
use std::fs;
use std::path::{Path, PathBuf};

mod noalloc;
mod type_annotations;
#[cfg(test)]
mod tests;

/// Check options
#[derive(Debug, Clone, Default)]
pub struct CheckOptions {
    /// Output JSON format for tooling
    pub json: bool,
    /// Verbose output (show additional details)
    pub verbose: bool,
    /// Quiet mode (only show errors, no progress)
    pub quiet: bool,
    /// Additional source roots for module resolution
    pub source_roots: Vec<PathBuf>,
    /// Promote runtime-family boundary crossings to hard errors.
    pub deny_gc_boundary_crossings: bool,
    /// Optional target preset for target-restricted checks.
    pub target: Option<Target>,
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
    Warning,
    Error,
}

/// Check error
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CheckError {
    pub file: String,
    pub line: usize,
    pub column: usize,
    pub severity: ErrorSeverity,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub code: Option<String>,
    pub message: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub expected: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub found: Option<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub notes: Vec<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub help: Vec<String>,
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
    let files = expand_check_inputs(files);
    let mut all_results = Vec::new();
    let mut has_errors = false;
    let deny_gc_boundary_crossings = should_deny_gc_boundary_crossings(&options);

    for file in &files {
        if !options.quiet && options.verbose {
            println!("Checking {}...", file.display());
        }

        let result = check_file(file, &options.source_roots, deny_gc_boundary_crossings);

        match &result.status {
            CheckStatus::Success => {
                if !options.quiet && !options.json {
                    println!("Checking {}... \x1b[32mOK\x1b[0m", file.display());
                }
            }
            CheckStatus::Warning | CheckStatus::Error => {
                if result.errors.iter().any(|error| error.severity == ErrorSeverity::Error) {
                    has_errors = true;
                }
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
        let error_count: usize = all_results
            .iter()
            .map(|r| r.errors.iter().filter(|e| e.severity == ErrorSeverity::Error).count())
            .sum();
        let warning_count: usize = all_results
            .iter()
            .map(|r| r.errors.iter().filter(|e| e.severity == ErrorSeverity::Warning).count())
            .sum();
        if error_count > 0 {
            println!(
                "\x1b[31m✗ {} error(s) found in {} file(s)\x1b[0m",
                error_count,
                files.len()
            );
        } else if warning_count > 0 {
            println!(
                "\x1b[33m⚠ {} warning(s) found in {} file(s)\x1b[0m",
                warning_count,
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

fn should_deny_gc_boundary_crossings(options: &CheckOptions) -> bool {
    options.deny_gc_boundary_crossings || options.target.is_some_and(|target| target.is_baremetal())
}

fn expand_check_inputs(inputs: &[PathBuf]) -> Vec<PathBuf> {
    let mut expanded = Vec::new();
    for input in inputs {
        expand_check_input(input, &mut expanded);
    }
    expanded.sort();
    expanded.dedup();
    expanded
}

fn expand_check_input(path: &Path, out: &mut Vec<PathBuf>) {
    if path.is_dir() {
        let mut entries = match fs::read_dir(path) {
            Ok(entries) => entries.filter_map(Result::ok).map(|e| e.path()).collect::<Vec<_>>(),
            Err(_) => {
                return;
            }
        };
        entries.sort();
        for entry in entries {
            expand_check_input(&entry, out);
        }
        return;
    }

    if path.extension().and_then(|ext| ext.to_str()) == Some("spl") {
        out.push(path.to_path_buf());
    }
}

/// Check a single file
fn check_file(path: &Path, source_roots: &[PathBuf], deny_gc_boundary_crossings: bool) -> FileCheckResult {
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
                    code: Some("E0001".to_string()),
                    message: format!("cannot read file: {}", e),
                    expected: None,
                    found: None,
                    notes: Vec::new(),
                    help: vec!["check that the path exists and is readable".to_string()],
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
            validate_imports(path, &module.items, &mut errors, source_roots);
            validate_gc_boundary_lints(path, &module.items, &mut errors, deny_gc_boundary_crossings);
            noalloc::validate_noalloc_reachable_import_closure(
                path,
                &mut errors,
                source_roots,
                deny_gc_boundary_crossings,
            );
            type_annotations::validate_basic_type_annotations(path, &module.items, &mut errors);
        }
        Err(e) => {
            // Convert ParseError to CheckError
            errors.push(parse_error_to_check_error(&e, path));
        }
    }

    let has_hard_errors = errors.iter().any(|error| error.severity == ErrorSeverity::Error);
    let status = if has_hard_errors {
        CheckStatus::Error
    } else if !errors.is_empty() {
        CheckStatus::Warning
    } else {
        CheckStatus::Success
    };

    FileCheckResult {
        file: path.display().to_string(),
        status,
        errors,
    }
}

fn validate_gc_boundary_lints(
    file_path: &Path,
    items: &[Node],
    errors: &mut Vec<CheckError>,
    deny_gc_boundary_crossings: bool,
) {
    let mut config = LintConfig::new();
    for lint in LintName::all_lints() {
        config.set_level(lint, LintLevel::Allow);
    }
    let gc_boundary_level = if deny_gc_boundary_crossings {
        LintLevel::Deny
    } else {
        LintLevel::Warn
    };
    config.set_level(LintName::GcBoundaryCrossing, gc_boundary_level);

    let mut checker = LintChecker::with_config(config).with_source_file(Some(file_path.to_path_buf()));
    checker.check_module(items);

    for diagnostic in checker.take_diagnostics() {
        if diagnostic.lint != LintName::GcBoundaryCrossing {
            continue;
        }

        let mut help = Vec::new();
        if let Some(suggestion) = &diagnostic.suggestion {
            help.push(suggestion.clone());
        }

        errors.push(CheckError {
            file: file_path.display().to_string(),
            line: diagnostic.span.line,
            column: diagnostic.span.column,
            severity: if diagnostic.is_error() {
                ErrorSeverity::Error
            } else {
                ErrorSeverity::Warning
            },
            code: Some(diagnostic.lint.as_str().to_string()),
            message: diagnostic.message,
            expected: None,
            found: None,
            notes: Vec::new(),
            help,
        });
    }
}

fn find_simple_workspace_root(start: &Path) -> Option<PathBuf> {
    let mut current = if start.is_dir() {
        start.to_path_buf()
    } else {
        start.parent()?.to_path_buf()
    };

    loop {
        if current.join("src/compiler").is_dir() && current.join("src/lib").is_dir() {
            return Some(current);
        }
        if !current.pop() {
            return None;
        }
    }
}

/// Validate import statements in a module
fn validate_imports(file_path: &Path, items: &[Node], errors: &mut Vec<CheckError>, source_roots: &[PathBuf]) {
    // Create one or more project-aware module resolvers.
    let abs_path = if file_path.is_absolute() {
        file_path.to_path_buf()
    } else {
        std::env::current_dir()
            .map(|cwd| cwd.join(file_path))
            .unwrap_or_else(|_| file_path.to_path_buf())
    };
    let cwd = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    let mut resolvers = Vec::new();
    if source_roots.is_empty() {
        if let Some(workspace_root) = find_simple_workspace_root(&cwd) {
            let source_root = workspace_root.join("src");
            resolvers.push(ModuleResolver::new(workspace_root, source_root));
        }
        resolvers.push(ModuleResolver::single_file_with_project_hint(&abs_path, Some(&cwd)));
    } else {
        for source_root in source_roots {
            let abs_root = if source_root.is_absolute() {
                source_root.clone()
            } else {
                cwd.join(source_root)
            };
            resolvers.push(ModuleResolver::new(cwd.clone(), abs_root));
        }
    }

    fn target_module_path(
        module_path: &simple_parser::ast::ModulePath,
        target: &ImportTarget,
    ) -> Option<simple_parser::ast::ModulePath> {
        match target {
            ImportTarget::Single(name) | ImportTarget::Aliased { name, .. } => {
                let mut segments = module_path.segments.clone();
                segments.push(name.clone());
                Some(simple_parser::ast::ModulePath::new(segments))
            }
            _ => None,
        }
    }

    fn import_resolves(
        resolvers: &[ModuleResolver],
        module_path: &simple_parser::ast::ModulePath,
        target: &ImportTarget,
        from_file: &Path,
    ) -> bool {
        if let Some(candidate_path) = target_module_path(module_path, target) {
            if resolvers
                .iter()
                .any(|resolver| resolver.resolve(&candidate_path, from_file).is_ok())
            {
                return true;
            }
        }

        resolvers
            .iter()
            .any(|resolver| resolver.resolve(module_path, from_file).is_ok())
    }

    for item in items {
        match item {
            Node::UseStmt(use_stmt) => {
                if use_stmt.path.segments.is_empty() {
                    continue;
                }
                let resolved = import_resolves(&resolvers, &use_stmt.path, &use_stmt.target, &abs_path);
                if !resolved {
                    let msg = resolvers
                        .iter()
                        .find_map(|resolver| resolver.resolve(&use_stmt.path, &abs_path).err())
                        .map(|e| e.to_string())
                        .unwrap_or_else(|| "unknown import resolution failure".to_string());
                    // Only report as warning since the module might be in a different project location
                    errors.push(CheckError {
                        file: file_path.display().to_string(),
                        line: use_stmt.span.line,
                        column: use_stmt.span.column,
                        severity: ErrorSeverity::Warning,
                        code: Some("W0410".to_string()),
                        message: format!("unresolved import '{}': {}", use_stmt.path.segments.join("."), msg),
                        expected: None,
                        found: None,
                        notes: Vec::new(),
                        help: vec!["check the module path or add the source root with --source-root".to_string()],
                    });
                }
            }
            Node::CommonUseStmt(common_use) => {
                if common_use.path.segments.is_empty() {
                    continue;
                }
                let resolved = import_resolves(&resolvers, &common_use.path, &common_use.target, &abs_path);
                if !resolved {
                    let msg = resolvers
                        .iter()
                        .find_map(|resolver| resolver.resolve(&common_use.path, &abs_path).err())
                        .map(|e| e.to_string())
                        .unwrap_or_else(|| "unknown import resolution failure".to_string());
                    errors.push(CheckError {
                        file: file_path.display().to_string(),
                        line: common_use.span.line,
                        column: common_use.span.column,
                        severity: ErrorSeverity::Warning,
                        code: Some("W0411".to_string()),
                        message: format!(
                            "unresolved common import '{}': {}",
                            common_use.path.segments.join("."),
                            msg
                        ),
                        expected: None,
                        found: None,
                        notes: Vec::new(),
                        help: vec!["check the module path or add the source root with --source-root".to_string()],
                    });
                }
            }
            Node::ExportUseStmt(export_use) => {
                if export_use.path.segments.is_empty() {
                    continue;
                }
                let resolved = import_resolves(&resolvers, &export_use.path, &export_use.target, &abs_path);
                if !resolved {
                    let msg = resolvers
                        .iter()
                        .find_map(|resolver| resolver.resolve(&export_use.path, &abs_path).err())
                        .map(|e| e.to_string())
                        .unwrap_or_else(|| "unknown import resolution failure".to_string());
                    errors.push(CheckError {
                        file: file_path.display().to_string(),
                        line: export_use.span.line,
                        column: export_use.span.column,
                        severity: ErrorSeverity::Warning,
                        code: Some("W0412".to_string()),
                        message: format!(
                            "unresolved export import '{}': {}",
                            export_use.path.segments.join("."),
                            msg
                        ),
                        expected: None,
                        found: None,
                        notes: Vec::new(),
                        help: vec![
                            "check the exported module path or add the source root with --source-root".to_string(),
                        ],
                    });
                }
            }
            _ => {}
        }
    }
}

/// Convert ParseError to CheckError
fn parse_error_to_check_error(err: &ParseError, path: &Path) -> CheckError {
    use simple_parser::ParseError;
    let diagnostic = err.to_diagnostic();
    let code = diagnostic.code.clone();
    let notes = diagnostic.notes.clone();
    let help = diagnostic.help.clone();

    match err {
        ParseError::SyntaxError {
            message, line, column, ..
        } => CheckError {
            file: path.display().to_string(),
            line: *line,
            column: *column,
            severity: ErrorSeverity::Error,
            code,
            message: message.clone(),
            expected: None,
            found: None,
            notes,
            help,
        },
        ParseError::UnexpectedToken {
            expected, found, span, ..
        } => CheckError {
            file: path.display().to_string(),
            line: span.line,
            column: span.column,
            severity: ErrorSeverity::Error,
            code,
            message: "unexpected token".to_string(),
            expected: Some(expected.clone()),
            found: Some(found.clone()),
            notes,
            help,
        },
        ParseError::MissingToken { expected, span, .. } => CheckError {
            file: path.display().to_string(),
            line: span.line,
            column: span.column,
            severity: ErrorSeverity::Error,
            code,
            message: format!("missing expected token: {}", expected),
            expected: Some(expected.clone()),
            found: None,
            notes,
            help,
        },
        ParseError::UnclosedString { span, .. } => {
            let (line, column) = if let Some(s) = span { (s.line, s.column) } else { (0, 0) };
            CheckError {
                file: path.display().to_string(),
                line,
                column,
                severity: ErrorSeverity::Error,
                code,
                message: "unclosed string literal".to_string(),
                expected: None,
                found: None,
                notes,
                help,
            }
        }
        ParseError::InvalidIndentation { line, .. } => CheckError {
            file: path.display().to_string(),
            line: *line,
            column: 1,
            severity: ErrorSeverity::Error,
            code,
            message: "invalid indentation".to_string(),
            expected: None,
            found: None,
            notes,
            help,
        },
        ParseError::InvalidPattern { span, message, .. } => CheckError {
            file: path.display().to_string(),
            line: span.line,
            column: span.column,
            severity: ErrorSeverity::Error,
            code,
            message: format!("invalid pattern: {}", message),
            expected: None,
            found: None,
            notes,
            help,
        },
        ParseError::InvalidType { span, message, .. } => CheckError {
            file: path.display().to_string(),
            line: span.line,
            column: span.column,
            severity: ErrorSeverity::Error,
            code,
            message: format!("invalid type: {}", message),
            expected: None,
            found: None,
            notes,
            help,
        },
        _ => CheckError {
            file: path.display().to_string(),
            line: 0,
            column: 0,
            severity: ErrorSeverity::Error,
            code,
            message: err.to_string(),
            expected: None,
            found: None,
            notes,
            help,
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

    let level = match error.severity {
        ErrorSeverity::Error => "error",
        ErrorSeverity::Warning => "warning",
    };
    let code = error
        .code
        .as_ref()
        .map(|code| format!("[{}]", code))
        .unwrap_or_default();
    println!(
        "{}{}:{}:{}: {}{}{}: {}",
        color, error.file, error.line, error.column, level, code, reset, error.message
    );

    if let Some(expected) = &error.expected {
        println!("  expected: {}", expected);
    }
    if let Some(found) = &error.found {
        println!("  found:    {}", found);
    }
    for note in &error.notes {
        println!("  = note: {}", note);
    }
    for help in &error.help {
        println!("  = help: {}", help);
    }
}

/// Output results in JSON format
fn output_json(results: &[FileCheckResult]) {
    let all_errors: Vec<CheckError> = results.iter().flat_map(|r| r.errors.clone()).collect();

    let has_errors = all_errors.iter().any(|error| error.severity == ErrorSeverity::Error);
    let has_warnings = all_errors.iter().any(|error| error.severity == ErrorSeverity::Warning);

    let output = CheckResult {
        status: if has_errors {
            CheckStatus::Error
        } else if has_warnings {
            CheckStatus::Warning
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
