//! Watch mode for automatic test re-running.
//!
//! Monitors test directories for changes and automatically re-runs tests.

use std::path::PathBuf;
use std::time::Instant;

use notify::{Config, EventKind, RecommendedWatcher, RecursiveMode, Watcher};
use std::sync::mpsc::channel;

use super::test_discovery::is_test_file;
use super::test_output::print_summary;
use super::types::{TestOptions, OutputFormat};
use super::runner::run_tests;

/// Watch test directories and auto-regenerate documentation on changes
pub fn watch_tests(options: TestOptions) -> Result<(), String> {
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
        RecommendedWatcher::new(tx, Config::default()).map_err(|e| format!("Failed to initialize watcher: {}", e))?;

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
                    println!("Completed in {:.2}s. Watching for changes...", duration.as_secs_f64());
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
