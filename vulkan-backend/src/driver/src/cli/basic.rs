//! Basic CLI operations: running files, code, and watching for changes.

use simple_driver::runner::Runner;
use simple_driver::watcher::watch;
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
    let runner = create_runner(gc_log, gc_off);
    match runner.run_file(path) {
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
