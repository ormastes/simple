//! Test discovery and summarization.
//!
//! Handles discovering test files, doctest examples, and printing discovery summaries.
//! Doctest discovery happens once and is cached for both display and execution.

use std::path::PathBuf;
use std::collections::HashSet;

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

    let targeted_path = options.path.clone().map(|path| {
        if path.is_absolute() {
            path
        } else {
            cwd.join(path)
        }
    });
    let targeted_ext = targeted_path
        .as_ref()
        .and_then(|path| path.extension().and_then(|ext| ext.to_str()))
        .map(|ext| ext.to_string());

    let src_examples = if options.doctest_src && targeted_ext.as_deref() != Some("md") {
        let src_path = targeted_path.clone().unwrap_or_else(|| {
            options.doctest_src_dir.clone().unwrap_or_else(|| {
                for dir in &["src", "simple/std_lib", "lib"] {
                    let p = cwd.join(dir);
                    if p.is_dir() {
                        return p;
                    }
                }
                cwd.join("src")
            })
        });
        discover_doctests(&src_path).unwrap_or_default()
    } else {
        Vec::new()
    };

    let doc_examples = if options.doctest_doc {
        let doc_path = targeted_path.clone().unwrap_or_else(|| {
            options.doctest_doc_dir.clone().unwrap_or_else(|| cwd.join("doc"))
        });
        discover_doctests(&doc_path).unwrap_or_default()
    } else {
        Vec::new()
    };

    let md_examples = if options.doctest_md {
        let md_path = targeted_path.unwrap_or_else(|| {
            options.doctest_md_dir.clone().unwrap_or_else(|| cwd.join("doc"))
        });
        discover_md_doctests(&md_path).unwrap_or_default()
    } else {
        Vec::new()
    };

    let mut cache = DoctestCache {
        src_examples,
        doc_examples,
        md_examples,
    };
    dedupe_doctest_cache(&mut cache, targeted_ext.as_deref());
    cache
}

fn dedupe_doctest_cache(cache: &mut DoctestCache, targeted_ext: Option<&str>) {
    let mut seen = HashSet::new();
    if matches!(targeted_ext, Some("md")) {
        dedupe_examples(&mut cache.doc_examples, &mut seen);
        dedupe_examples(&mut cache.md_examples, &mut seen);
        dedupe_examples(&mut cache.src_examples, &mut seen);
    } else {
        dedupe_examples(&mut cache.src_examples, &mut seen);
        dedupe_examples(&mut cache.doc_examples, &mut seen);
        dedupe_examples(&mut cache.md_examples, &mut seen);
    }
}

fn dedupe_examples(examples: &mut Vec<DoctestExample>, seen: &mut HashSet<String>) {
    examples.retain(|example| {
        let key = format!(
            "{}:{}:{}:{}",
            example.source.display(),
            example.start_line,
            example.section_name.as_deref().unwrap_or(""),
            example.commands.join("\n")
        );
        seen.insert(key)
    });
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use tempfile::tempdir;

    #[test]
    fn discover_all_doctests_honors_targeted_markdown_path() {
        let temp = tempdir().expect("tempdir");
        let readme = temp.path().join("README.md");
        fs::write(
            &readme,
            "# Sample\n\n```sdoctest\n>>> 1 + 1\n2\n```\n",
        )
        .expect("write doctest");

        let mut options = TestOptions::default();
        options.path = Some(readme.clone());
        options.doctest_src = false;
        options.doctest_doc = true;
        options.doctest_md = true;

        let cache = discover_all_doctests(&options);
        assert_eq!(cache.src_examples.len(), 0);
        assert_eq!(cache.doc_examples.len() + cache.md_examples.len(), 1);
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
