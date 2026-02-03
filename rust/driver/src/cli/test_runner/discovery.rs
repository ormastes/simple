//! Test discovery and summarization.
//!
//! Handles discovering test files and printing discovery summaries.

use std::path::PathBuf;

use crate::doctest::{discover_doctests, discover_md_doctests};
use super::types::TestOptions;

/// Print test discovery summary
pub fn print_discovery_summary(test_files: &[PathBuf], options: &TestOptions, quiet: bool) {
    if quiet {
        return;
    }

    let spec_count = test_files
        .iter()
        .filter(|p| {
            p.file_name()
                .and_then(|n| n.to_str())
                .map(|n| n.ends_with("_spec.spl"))
                .unwrap_or(false)
        })
        .count();
    let test_count = test_files.len() - spec_count;

    println!("───────────────────────────────────────────────────────────────");
    println!("Test Discovery");
    println!("───────────────────────────────────────────────────────────────");
    println!("  Spec files (*_spec.spl):  {}", spec_count);
    println!("  Test files (*_test.spl):  {}", test_count);

    // Count doctests if enabled
    print_doctest_counts(options);

    println!("───────────────────────────────────────────────────────────────");
    println!();
}

/// Print doctest counts
fn print_doctest_counts(options: &TestOptions) {
    if options.doctest_src || options.doctest_doc {
        let cwd = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
        let src_dir = options
            .doctest_src_dir
            .clone()
            .unwrap_or_else(|| cwd.join("src/std/src"));
        let doc_dir = options.doctest_doc_dir.clone().unwrap_or_else(|| cwd.join("doc"));

        if options.doctest_src && src_dir.is_dir() {
            if let Ok(examples) = discover_doctests(&src_dir) {
                let count: usize = examples.len();
                println!("  Src doctests (.spl):      {}", count);
            }
        }
        if options.doctest_doc && doc_dir.is_dir() {
            if let Ok(examples) = discover_doctests(&doc_dir) {
                let count: usize = examples.len();
                println!("  Doc doctests (.md):       {}", count);
            }
        }
    }

    if options.doctest_md {
        let cwd = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
        let md_dir = options.doctest_md_dir.clone().unwrap_or_else(|| cwd.join("doc"));

        if md_dir.is_dir() {
            if let Ok(examples) = discover_md_doctests(&md_dir) {
                let count: usize = examples.len();
                println!("  MD doctests (README.md):  {}", count);
            }
        }
    }
}
