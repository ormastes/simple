//! Code quality commands: lint and format.

use simple_common::diagnostic::{Diagnostics, EasyFix, FixConfidence, SourceRegistry};
use simple_common::fix_applicator::FixApplicator;
use simple_compiler::{Formatter, LintChecker, LintConfig};
use simple_parser::Parser;
use std::fs;
use std::path::PathBuf;
use walkdir::WalkDir;

use super::commands::arg_parsing::FixFlags;
use crate::cli::interactive_fix;

/// Run the linter on a file or directory
pub fn run_lint(args: &[String]) -> i32 {
    // Parse arguments
    let path = args
        .get(1)
        .map(|s| PathBuf::from(s))
        .unwrap_or_else(|| PathBuf::from("."));
    let json_output = args.iter().any(|a| a == "--json");
    let fix_flags = FixFlags::parse(args);

    // Check if path is directory
    if path.is_dir() {
        return lint_directory(&path, json_output, &fix_flags);
    }

    // Lint single file
    lint_file(&path, json_output, &fix_flags)
}

/// Lint all .spl files in a directory
pub fn lint_directory(dir: &PathBuf, json_output: bool, fix_flags: &FixFlags) -> i32 {
    let mut all_errors = false;
    let mut total_errors = 0;
    let mut total_warnings = 0;
    let mut all_diags = Diagnostics::new();
    let mut all_fixes: Vec<EasyFix> = Vec::new();
    let mut sources = SourceRegistry::new();

    for entry in WalkDir::new(dir)
        .follow_links(true)
        .into_iter()
        .filter_map(|e| e.ok())
        .filter(|e| e.path().extension().and_then(|s| s.to_str()) == Some("spl"))
    {
        let path = entry.path();
        let result = lint_file_internal(path, false);

        if let Some((has_err, err_count, warn_count, diags, fixes, source)) = result {
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

            all_fixes.extend(fixes);
            if let Some(src) = source {
                sources.add(path.display().to_string(), src);
            }
        }
    }

    // Apply fixes if requested
    if fix_flags.any_fix_mode() && !all_fixes.is_empty() {
        apply_fixes(&all_fixes, &sources, fix_flags);
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
pub fn lint_file(path: &PathBuf, json_output: bool, fix_flags: &FixFlags) -> i32 {
    if let Some((has_errors, _, _, diags, fixes, source)) = lint_file_internal(path, json_output) {
        // Apply fixes if requested
        if fix_flags.any_fix_mode() && !fixes.is_empty() {
            let mut sources = SourceRegistry::new();
            if let Some(src) = source {
                sources.add(path.display().to_string(), src);
            }
            apply_fixes(&fixes, &sources, fix_flags);
        }

        if json_output {
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
/// Returns: (has_errors, error_count, warning_count, diagnostics, easy_fixes, source_text)
pub fn lint_file_internal(
    path: &std::path::Path,
    json_output: bool,
) -> Option<(bool, usize, usize, Vec<simple_common::diagnostic::Diagnostic>, Vec<EasyFix>, Option<String>)> {
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
    let mut checker = LintChecker::with_config(config).with_source_file(Some(path.to_path_buf()));

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

    // Collect easy fixes from diagnostics
    let easy_fixes: Vec<EasyFix> = diagnostics
        .iter()
        .filter_map(|d| d.easy_fix.clone())
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
                let level_str = if diagnostic.is_error() { "error" } else { "warning" };
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
                if diagnostic.easy_fix.is_some() {
                    println!("  fix: available (use --fix to apply)");
                }
            }
        }
    }

    Some((has_errors, error_count, warning_count, common_diags, easy_fixes, Some(source)))
}

/// Apply collected fixes based on fix flags
fn apply_fixes(fixes: &[EasyFix], sources: &SourceRegistry, fix_flags: &FixFlags) {
    // Filter fixes based on flags
    let filtered: Vec<&EasyFix> = if fix_flags.fix_all {
        fixes.iter().collect()
    } else if fix_flags.fix {
        FixApplicator::filter_by_confidence(fixes, FixConfidence::Safe)
    } else if let Some(ref id) = fix_flags.fix_id {
        FixApplicator::filter_by_id(fixes, id)
    } else if let Some(ref code) = fix_flags.fix_code {
        fixes.iter().filter(|f| f.id.starts_with(code)).collect()
    } else if let Some(nth) = fix_flags.fix_nth {
        if nth > 0 && nth <= fixes.len() {
            vec![&fixes[nth - 1]]
        } else {
            eprintln!("error: --fix-nth={} is out of range (1-{})", nth, fixes.len());
            return;
        }
    } else {
        // Default: safe fixes only
        FixApplicator::filter_by_confidence(fixes, FixConfidence::Safe)
    };

    if filtered.is_empty() {
        println!("No applicable fixes found.");
        return;
    }

    // Interactive mode
    if fix_flags.fix_interactive {
        let accepted = interactive_fix::prompt_fixes(&filtered);
        if accepted.is_empty() {
            println!("No fixes applied.");
            return;
        }
        let owned: Vec<EasyFix> = accepted.into_iter().cloned().collect();
        match FixApplicator::apply_to_disk(&owned, sources, fix_flags.fix_dry_run) {
            Ok(report) => print_fix_report(&report, fix_flags.fix_dry_run),
            Err(e) => eprintln!("error applying fixes: {}", e),
        }
        return;
    }

    // Non-interactive: apply all filtered fixes
    let owned: Vec<EasyFix> = filtered.into_iter().cloned().collect();
    match FixApplicator::apply_to_disk(&owned, sources, fix_flags.fix_dry_run) {
        Ok(report) => print_fix_report(&report, fix_flags.fix_dry_run),
        Err(e) => eprintln!("error applying fixes: {}", e),
    }
}

fn print_fix_report(report: &simple_common::fix_applicator::FixReport, dry_run: bool) {
    let prefix = if dry_run { "Would apply" } else { "Applied" };
    println!("{} {} fix(es):", prefix, report.applied);
    for detail in &report.details {
        println!("  {}", detail);
    }
    if !report.modified_files.is_empty() {
        let verb = if dry_run { "Would modify" } else { "Modified" };
        println!("{} {} file(s):", verb, report.modified_files.len());
        for file in &report.modified_files {
            println!("  {}", file);
        }
    }
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

    // Format the source code
    let mut formatter = Formatter::new();
    let formatted = match formatter.format_source(&source) {
        Ok(f) => f,
        Err(e) => {
            eprintln!("error: {}", e);
            return 1;
        }
    };

    if check_only {
        // Check if file is already formatted
        if source == formatted {
            println!("{}: formatted correctly", path.display());
            0
        } else {
            eprintln!("{}: needs formatting", path.display());
            1
        }
    } else {
        // Write formatted code back to file
        match fs::write(&path, &formatted) {
            Ok(_) => {
                println!("{}: formatted", path.display());
                0
            }
            Err(e) => {
                eprintln!("error: cannot write {}: {}", path.display(), e);
                1
            }
        }
    }
}
