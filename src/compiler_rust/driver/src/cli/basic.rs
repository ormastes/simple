//! Basic CLI operations: running files, code, and watching for changes.

use crate::cli::examples_safety::{
    is_timeout_error, run_isolated_example_file, timeout_error_message, ExamplesWatchdogGuard,
};
use crate::runner::Runner;
use crate::watcher::watch;
use std::path::Path;

/// Create a runner with appropriate GC configuration
pub fn create_runner(gc_log: bool, gc_off: bool) -> Runner {
    if gc_off {
        Runner::new_no_gc()
    } else if gc_log {
        Runner::new_with_gc_logging()
    } else {
        Runner::new()
    }
}

/// Run a source file (.spl) or compiled binary (.smf)
pub fn run_file(path: &Path, gc_log: bool, gc_off: bool) -> i32 {
    run_file_with_args(path, gc_log, gc_off, vec![])
}

/// Run a source file (.spl) with command-line arguments
pub fn run_file_with_args(path: &Path, gc_log: bool, gc_off: bool, args: Vec<String>) -> i32 {
    if let Some(code) = run_isolated_example_file(path, gc_log, gc_off, &args) {
        return code;
    }

    let path = path.to_path_buf();
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(move || {
        let watchdog = ExamplesWatchdogGuard::for_path(&path);
        let runner = create_runner(gc_log, gc_off);
        let extension = path.extension().and_then(|e| e.to_str()).unwrap_or("");
        let result = if matches!(extension, "spl" | "simple" | "sscript" | "shs" | "") {
            runner.run_file_interpreted_with_args(&path, args)
        } else {
            runner.run_file(&path)
        };
        match result {
            Ok(code) => code,
            Err(e) => {
                if watchdog.is_active() && is_timeout_error(&e) {
                    eprintln!("error: {}", timeout_error_message(&path, watchdog.timeout_secs()));
                } else {
                    print_cli_error(&e);
                }
                1
            }
        }
    }));
    match result {
        Ok(code) => code,
        Err(panic_info) => {
            let msg = if let Some(s) = panic_info.downcast_ref::<&str>() {
                s.to_string()
            } else if let Some(s) = panic_info.downcast_ref::<String>() {
                s.clone()
            } else {
                "unknown internal error".to_string()
            };
            eprintln!("fatal: interpreter crashed: {}", msg);
            eprintln!("This is a bug in the Simple compiler. Please report it.");
            101
        }
    }
}

/// Run code from a string
pub fn run_code(code: &str, gc_log: bool, gc_off: bool) -> i32 {
    let code = code.to_string();
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(move || {
        let runner = create_runner(gc_log, gc_off);
        let print_exit_code = should_print_code_result(&code);

        // Wrap expression in main if not already a full program
        let full_code = if code.contains("main") || code.contains("fn ") || code.contains("let ") {
            code
        } else {
            format!("main = {}", code)
        };

        match runner.run_source_in_memory(&full_code) {
            Ok(exit_code) => {
                if print_exit_code {
                    println!("{}", exit_code);
                }
                exit_code
            }
            Err(e) => {
                print_cli_error(&e);
                1
            }
        }
    }));
    match result {
        Ok(code) => code,
        Err(panic_info) => {
            let msg = if let Some(s) = panic_info.downcast_ref::<&str>() {
                s.to_string()
            } else if let Some(s) = panic_info.downcast_ref::<String>() {
                s.clone()
            } else {
                "unknown internal error".to_string()
            };
            eprintln!("fatal: interpreter crashed: {}", msg);
            eprintln!("This is a bug in the Simple compiler. Please report it.");
            101
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct CliErrorDiagnostic {
    code: Option<&'static str>,
    message: String,
    help: Vec<&'static str>,
}

fn print_cli_error(error: &str) {
    let diagnostic = classify_cli_error(error);
    match diagnostic.code {
        Some(code) => eprintln!("error[{}]: {}", code, diagnostic.message),
        None => eprintln!("error: {}", diagnostic.message),
    }
    for help in diagnostic.help {
        eprintln!("  = help: {}", help);
    }
}

fn classify_cli_error(error: &str) -> CliErrorDiagnostic {
    if let Some(message) = error.strip_prefix("failed to read ") {
        return CliErrorDiagnostic {
            code: Some("E0001"),
            message: format!("cannot read file: {}", message),
            help: vec!["check that the path exists and is readable"],
        };
    }

    if let Some(message) = error.strip_prefix("parse error: ") {
        return CliErrorDiagnostic {
            code: Some("E0002"),
            message: message.to_string(),
            help: vec!["fix the syntax at the reported location"],
        };
    }

    if let Some(message) = error.strip_prefix("semantic: ") {
        if message.starts_with("function `") && message.ends_with("` not found") {
            return CliErrorDiagnostic {
                code: Some("E1002"),
                message: message.to_string(),
                help: vec!["check the function name or import the module that defines it"],
            };
        }
        if message == "division by zero" {
            return CliErrorDiagnostic {
                code: Some("E2001"),
                message: message.to_string(),
                help: vec!["check the divisor before dividing"],
            };
        }
    }

    CliErrorDiagnostic {
        code: None,
        message: error.to_string(),
        help: Vec::new(),
    }
}

fn should_print_code_result(code: &str) -> bool {
    let trimmed = code.trim();
    if trimmed.is_empty() || trimmed.contains('\n') {
        return false;
    }
    if trimmed.starts_with("main =") || trimmed.starts_with("main=") {
        return true;
    }
    if trimmed.starts_with("print ")
        || trimmed.starts_with("if ")
        || trimmed.starts_with("while ")
        || trimmed.starts_with("for ")
        || trimmed.starts_with("var ")
        || trimmed.starts_with("val ")
        || trimmed.starts_with("fn ")
        || trimmed.starts_with("class ")
        || trimmed.starts_with("struct ")
        || trimmed.starts_with("enum ")
        || trimmed.starts_with("use ")
        || trimmed.starts_with("extern ")
    {
        return false;
    }
    true
}

/// Watch a file for changes and auto-recompile
pub fn watch_file(path: &Path) -> i32 {
    println!("Watching {} for changes...", path.display());
    println!("Press Ctrl-C to stop.");

    match watch(path, true) {
        Ok(()) => 0,
        Err(e) => {
            eprintln!("error: {}", e);
            1
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn classify_undefined_function_error() {
        let diagnostic = classify_cli_error("semantic: function `missing_function` not found");

        assert_eq!(diagnostic.code, Some("E1002"));
        assert_eq!(diagnostic.message, "function `missing_function` not found");
        assert!(!diagnostic.help.is_empty());
    }

    #[test]
    fn classify_division_by_zero_error() {
        let diagnostic = classify_cli_error("semantic: division by zero");

        assert_eq!(diagnostic.code, Some("E2001"));
        assert_eq!(diagnostic.message, "division by zero");
        assert!(!diagnostic.help.is_empty());
    }

    #[test]
    fn keeps_unclassified_error_message() {
        let diagnostic = classify_cli_error("codegen: backend unavailable");

        assert_eq!(diagnostic.code, None);
        assert_eq!(diagnostic.message, "codegen: backend unavailable");
        assert!(diagnostic.help.is_empty());
    }
}
