//! Test discovery and summarization.
//!
//! Handles discovering test files, doctest examples, and printing discovery summaries.
//! Doctest discovery happens once and is cached for both display and execution.

use std::path::PathBuf;

use crate::doctest::{discover_doctests, discover_md_doctests, DoctestExample};
use super::types::TestOptions;

/// Cached doctest discovery results to avoid walking the filesystem twice.
pub struct DoctestCache {
    /// Doctests from src directories (.spl, .sdt files)
    pub src_examples: Vec<DoctestExample>,
    /// Doctests from doc directory (.md files)
    pub doc_examples: Vec<DoctestExample>,
    /// Doctests from README.md hierarchy
    pub md_examples: Vec<DoctestExample>,
}

/// Discover all doctest examples once, returning a cache for later use.
pub fn discover_all_doctests(options: &TestOptions) -> DoctestCache {
    let cwd = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));

    let src_examples = if options.doctest_src {
        let src_dir = options.doctest_src_dir.clone().unwrap_or_else(|| {
            for dir in &["src", "simple/std_lib", "lib"] {
                let p = cwd.join(dir);
                if p.is_dir() {
                    return p;
                }
            }
            cwd.join("src")
        });
        if src_dir.is_dir() {
            discover_doctests(&src_dir).unwrap_or_default()
        } else {
            Vec::new()
        }
    } else {
        Vec::new()
    };

    let doc_examples = if options.doctest_doc {
        let doc_dir = options.doctest_doc_dir.clone().unwrap_or_else(|| cwd.join("doc"));
        if doc_dir.is_dir() {
            discover_doctests(&doc_dir).unwrap_or_default()
        } else {
            Vec::new()
        }
    } else {
        Vec::new()
    };

    let md_examples = if options.doctest_md {
        let md_dir = options.doctest_md_dir.clone().unwrap_or_else(|| cwd.join("doc"));
        if md_dir.is_dir() {
            discover_md_doctests(&md_dir).unwrap_or_default()
        } else {
            Vec::new()
        }
    } else {
        Vec::new()
    };

    DoctestCache {
        src_examples,
        doc_examples,
        md_examples,
    }
}

/// Print test discovery summary including doctest counts from cache.
pub fn print_discovery_summary(test_files: &[PathBuf], cache: &DoctestCache, quiet: bool) {
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

    if !cache.src_examples.is_empty() {
        println!("  Src doctests (.spl/.sdt): {}", cache.src_examples.len());
    }
    if !cache.doc_examples.is_empty() {
        println!("  Doc doctests (.md):       {}", cache.doc_examples.len());
    }
    if !cache.md_examples.is_empty() {
        println!("  MD doctests (README.md):  {}", cache.md_examples.len());
    }

    println!("───────────────────────────────────────────────────────────────");
    println!();
}
