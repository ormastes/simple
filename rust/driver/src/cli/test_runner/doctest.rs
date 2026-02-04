//! Doctest discovery and execution.
//!
//! Handles running doctests from source files (.spl) and documentation (.md).

use std::path::PathBuf;
use std::time::Instant;

use crate::doctest::{discover_doctests, discover_md_doctests, run_examples, DoctestStatus};
use super::types::{TestFileResult, TestOptions};

/// Run doctests from configured directories
pub fn run_doctests(options: &TestOptions, quiet: bool) -> Vec<TestFileResult> {
    let mut results = Vec::new();
    let cwd = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));

    // Collect doctest source directories
    let mut doctest_paths = Vec::new();

    if options.doctest_src {
        let src_dir = options.doctest_src_dir.clone().unwrap_or_else(|| {
            // Try common source directories
            for dir in &["src", "simple/std_lib", "lib"] {
                let p = cwd.join(dir);
                if p.is_dir() {
                    return p;
                }
            }
            cwd.join("src")
        });

        if src_dir.is_dir() {
            if !quiet {
                println!("Discovering doctests in: {}", src_dir.display());
            }
            doctest_paths.push(src_dir);
        }
    }

    if options.doctest_doc {
        let doc_dir = options.doctest_doc_dir.clone().unwrap_or_else(|| cwd.join("doc"));

        if doc_dir.is_dir() {
            if !quiet {
                println!("Discovering doctests in: {}", doc_dir.display());
            }
            doctest_paths.push(doc_dir);
        }
    }

    // Discover and run doctests
    for path in doctest_paths {
        match discover_doctests(&path) {
            Ok(examples) => {
                if examples.is_empty() {
                    continue;
                }

                if !quiet {
                    println!("Found {} doctest example(s) in {}", examples.len(), path.display());
                }

                let start = Instant::now();
                let doctest_results = run_examples(&examples);
                let duration_ms = start.elapsed().as_millis() as u64;

                // Group results by source file
                let mut file_results: std::collections::HashMap<PathBuf, (usize, usize, Vec<String>)> =
                    std::collections::HashMap::new();

                for result in doctest_results {
                    let entry = file_results
                        .entry(result.example.source.clone())
                        .or_insert((0, 0, Vec::new()));

                    match result.status {
                        DoctestStatus::Passed => entry.0 += 1,
                        DoctestStatus::Failed(msg) => {
                            entry.1 += 1;
                            let section = result
                                .example
                                .section_name
                                .as_ref()
                                .map(|s| format!(" [{}]", s))
                                .unwrap_or_default();
                            entry.2.push(format!(
                                "Line {}{}:\n  Expected: {:?}\n  Actual: {}\n  Error: {}",
                                result.example.start_line, section, result.example.expected, result.actual, msg
                            ));
                        }
                    }
                }

                for (source_path, (passed, failed, errors)) in file_results {
                    let error = if errors.is_empty() {
                        None
                    } else {
                        Some(errors.join("\n"))
                    };

                    if !quiet {
                        let status = if failed > 0 {
                            "\x1b[31mFAILED\x1b[0m"
                        } else {
                            "\x1b[32mPASSED\x1b[0m"
                        };
                        println!(
                            "  Doctest: {} {} ({} passed, {} failed)",
                            source_path.display(),
                            status,
                            passed,
                            failed
                        );
                    }

                    results.push(TestFileResult {
                        path: source_path,
                        passed,
                        failed,
                        skipped: 0,
                        ignored: 0,
                        duration_ms: duration_ms / (results.len() as u64 + 1).max(1),
                        error,
                        individual_results: vec![],
                    });
                }
            }
            Err(e) => {
                if !quiet {
                    eprintln!("Warning: Failed to discover doctests in {}: {}", path.display(), e);
                }
            }
        }
    }

    results
}

/// Run README.md-based doctests
pub fn run_md_doctests(options: &TestOptions, quiet: bool) -> Vec<TestFileResult> {
    let mut results = Vec::new();
    let cwd = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));

    let doc_dir = options.doctest_md_dir.clone().unwrap_or_else(|| cwd.join("doc"));

    if !doc_dir.is_dir() {
        if !quiet {
            eprintln!("Warning: Doc directory not found: {}", doc_dir.display());
        }
        return results;
    }

    if !quiet {
        println!("Discovering README.md doctests in: {}", doc_dir.display());
    }

    match discover_md_doctests(&doc_dir) {
        Ok(examples) => {
            if examples.is_empty() {
                if !quiet {
                    println!("  No doctests found in README.md hierarchy");
                }
                return results;
            }

            if !quiet {
                println!("Found {} doctest example(s) via README.md hierarchy", examples.len());
            }

            let start = Instant::now();
            let doctest_results = run_examples(&examples);
            let duration_ms = start.elapsed().as_millis() as u64;

            // Group results by source file
            let mut file_results: std::collections::HashMap<PathBuf, (usize, usize, Vec<String>)> =
                std::collections::HashMap::new();

            for result in doctest_results {
                let entry = file_results
                    .entry(result.example.source.clone())
                    .or_insert((0, 0, Vec::new()));

                match result.status {
                    DoctestStatus::Passed => entry.0 += 1,
                    DoctestStatus::Failed(msg) => {
                        entry.1 += 1;
                        let section = result
                            .example
                            .section_name
                            .as_ref()
                            .map(|s| format!(" [{}]", s))
                            .unwrap_or_default();
                        entry.2.push(format!(
                            "Line {}{}:\n  Expected: {:?}\n  Actual: {}\n  Error: {}",
                            result.example.start_line, section, result.example.expected, result.actual, msg
                        ));
                    }
                }
            }

            for (source_path, (passed, failed, errors)) in file_results {
                let error = if errors.is_empty() {
                    None
                } else {
                    Some(errors.join("\n"))
                };

                if !quiet {
                    let status = if failed > 0 {
                        "\x1b[31mFAILED\x1b[0m"
                    } else {
                        "\x1b[32mPASSED\x1b[0m"
                    };
                    println!(
                        "  MD Doctest: {} {} ({} passed, {} failed)",
                        source_path.display(),
                        status,
                        passed,
                        failed
                    );
                }

                results.push(TestFileResult {
                    path: source_path,
                    passed,
                    failed,
                    skipped: 0,
                    ignored: 0,
                    duration_ms: duration_ms / (results.len() as u64 + 1).max(1),
                    error,
                    individual_results: vec![],
                });
            }
        }
        Err(e) => {
            if !quiet {
                eprintln!("Warning: Failed to discover README.md doctests: {}", e);
            }
        }
    }

    results
}
