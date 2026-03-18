//! Doctest execution using pre-discovered cache.
//!
//! Runs doctests from the cached discovery results (no re-walk).

use std::path::PathBuf;
use std::time::Instant;

use crate::doctest::{run_examples, DoctestExample, DoctestStatus};
use super::discovery::DoctestCache;
use super::types::TestFileResult;

/// Run all cached doctests, returning file-level results.
pub fn run_cached_doctests(cache: &DoctestCache, quiet: bool) -> Vec<TestFileResult> {
    let mut results = Vec::new();

    if !cache.src_examples.is_empty() {
        run_and_collect(&cache.src_examples, "Doctest", quiet, &mut results);
    }
    if !cache.doc_examples.is_empty() {
        run_and_collect(&cache.doc_examples, "Doctest", quiet, &mut results);
    }
    if !cache.md_examples.is_empty() {
        run_and_collect(&cache.md_examples, "MD Doctest", quiet, &mut results);
    }

    results
}

/// Run a set of examples, group by source file, and append results.
fn run_and_collect(examples: &[DoctestExample], label: &str, quiet: bool, results: &mut Vec<TestFileResult>) {
    let start = Instant::now();
    let doctest_results = run_examples(examples);
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

    let file_count = file_results.len().max(1) as u64;
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
                "  {}: {} {} ({} passed, {} failed)",
                label,
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
            duration_ms: duration_ms / file_count,
            error,
            individual_results: vec![],
            contract_results: vec![],
        });
    }
}
