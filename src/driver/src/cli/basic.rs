//! Basic CLI operations: running files, code, and watching for changes.

use crate::runner::Runner;
use crate::watcher::watch;
use std::path::PathBuf;

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
pub fn run_file(path: &PathBuf, gc_log: bool, gc_off: bool) -> i32 {
    run_file_with_args(path, gc_log, gc_off, vec![])
}

/// Run a source file (.spl) with command-line arguments
pub fn run_file_with_args(path: &PathBuf, gc_log: bool, gc_off: bool, args: Vec<String>) -> i32 {
    let runner = create_runner(gc_log, gc_off);
    // Use interpreted mode with args for spl files
    let extension = path.extension().and_then(|e| e.to_str()).unwrap_or("");
    let result = if matches!(extension, "spl" | "simple" | "sscript" | "") {
        runner.run_file_interpreted_with_args(path, args)
    } else {
        runner.run_file(path)
    };
    match result {
        Ok(code) => code,
        Err(e) => {
            eprintln!("error: {}", e);
            1
        }
    }
}

/// Run code from a string
pub fn run_code(code: &str, gc_log: bool, gc_off: bool) -> i32 {
    let runner = create_runner(gc_log, gc_off);

    // Wrap expression in main if not already a full program
    let full_code = if code.contains("main") || code.contains("fn ") || code.contains("let ") {
        code.to_string()
    } else {
        format!("main = {}", code)
    };

    match runner.run_source_in_memory(&full_code) {
        Ok(exit_code) => {
            println!("{}", exit_code);
            exit_code
        }
        Err(e) => {
            eprintln!("error: {}", e);
            1
        }
    }
}

/// Watch a file for changes and auto-recompile
pub fn watch_file(path: &PathBuf) -> i32 {
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
