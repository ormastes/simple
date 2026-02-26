//! Static test registry for fast test queries.
//!
//! This module provides a fast registry for querying test metadata
//! WITHOUT executing DSL code. Tests are discovered by parsing source
//! files and extracting metadata statically.
//!
//! # Performance
//!
//! Target: List 1000+ tests in under 1 second (parse only, no execution).
//!
//! # Example
//!
//! ```rust,ignore
//! use simple_driver::cli::test_runner::static_registry::StaticTestRegistry;
//!
//! let registry = StaticTestRegistry::from_files(&test_files)?;
//!
//! // Fast queries - no instantiation
//! let all_tests = registry.list_tests();
//! let slow_tests = registry.list_slow();
//! let skipped = registry.list_skipped();
//! let by_tag = registry.filter_by_tag("integration");
//! ```

use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::Instant;

use simple_parser::test_analyzer::{extract_file_test_meta, merge_content_tags};
use simple_parser::Parser;
use simple_parser::ast::nodes::test_meta::{FileTestMeta, TestInfo, TestRef};

/// Static test registry for fast test queries.
///
/// This registry parses test files to extract metadata WITHOUT
/// executing any DSL code, enabling fast test listing.
#[derive(Debug, Default)]
pub struct StaticTestRegistry {
    /// Metadata indexed by file path
    pub files: HashMap<PathBuf, FileTestMeta>,
    /// Tests indexed by tag name
    pub tag_index: HashMap<String, Vec<TestRef>>,
    /// All slow test references
    pub slow_refs: Vec<TestRef>,
    /// All skipped test references
    pub skipped_refs: Vec<TestRef>,
    /// All ignored test references
    pub ignored_refs: Vec<TestRef>,
    /// Time spent parsing (for diagnostics)
    pub parse_time_ms: u64,
}

impl StaticTestRegistry {
    /// Create a new empty registry
    pub fn new() -> Self {
        Self::default()
    }

    /// Build registry from a list of test files.
    ///
    /// This parses each file and extracts test metadata statically.
    /// It's designed to be fast - no DSL execution, just AST analysis.
    pub fn from_files(files: &[PathBuf]) -> Result<Self, String> {
        let start = Instant::now();
        let mut registry = Self::new();

        for file_path in files {
            match registry.add_file(file_path) {
                Ok(_) => {}
                Err(e) => {
                    // Log error but continue - don't fail entire discovery
                    eprintln!("Warning: Failed to parse {}: {}", file_path.display(), e);
                }
            }
        }

        registry.parse_time_ms = start.elapsed().as_millis() as u64;
        registry.build_indexes();
        Ok(registry)
    }

    /// Add a single file to the registry
    fn add_file(&mut self, file_path: &Path) -> Result<(), String> {
        // Read file content
        let content = fs::read_to_string(file_path).map_err(|e| format!("Failed to read file: {}", e))?;

        // Parse the file
        let mut parser = Parser::new(&content);
        let module = parser.parse().map_err(|e| format!("Parse error: {:?}", e))?;

        // Extract test metadata from AST
        let path_buf = file_path.to_path_buf();
        let mut file_meta = extract_file_test_meta(&module.items, Some(&path_buf));

        // Also extract content-based tags (comments, attributes)
        merge_content_tags(&mut file_meta, &content);

        // Store in registry
        self.files.insert(path_buf, file_meta);

        Ok(())
    }

    /// Build index structures after all files are loaded
    fn build_indexes(&mut self) {
        self.tag_index.clear();
        self.slow_refs.clear();
        self.skipped_refs.clear();
        self.ignored_refs.clear();

        for (file_path, file_meta) in &self.files {
            let all_tests = file_meta.all_tests();

            for (idx, test) in all_tests.into_iter().enumerate() {
                let test_ref = TestRef {
                    file_path: file_path.clone(),
                    test_index: idx,
                };

                // Index by tags
                if let Some(tags) = test.tags() {
                    for tag in tags {
                        self.tag_index.entry(tag.clone()).or_default().push(test_ref.clone());
                    }
                }

                // Index by test type
                if test.is_slow() {
                    self.slow_refs.push(test_ref.clone());
                }
                if test.is_skipped() {
                    self.skipped_refs.push(test_ref.clone());
                }
                if test.is_ignored() {
                    self.ignored_refs.push(test_ref);
                }
            }
        }
    }

    /// List all tests (returns TestInfo for display)
    pub fn list_tests(&self) -> Vec<TestInfo> {
        let mut tests = Vec::new();
        for (file_path, file_meta) in &self.files {
            for test in file_meta.all_tests() {
                tests.push(TestInfo::from_test_meta(test, file_path.clone()));
            }
        }
        tests
    }

    /// List skipped tests
    pub fn list_skipped(&self) -> Vec<TestInfo> {
        let mut tests = Vec::new();
        for (file_path, file_meta) in &self.files {
            for test in file_meta.skipped_tests() {
                tests.push(TestInfo::from_test_meta(test, file_path.clone()));
            }
        }
        tests
    }

    /// List slow tests
    pub fn list_slow(&self) -> Vec<TestInfo> {
        let mut tests = Vec::new();
        for (file_path, file_meta) in &self.files {
            for test in file_meta.slow_tests() {
                tests.push(TestInfo::from_test_meta(test, file_path.clone()));
            }
        }
        tests
    }

    /// List ignored tests
    pub fn list_ignored(&self) -> Vec<TestInfo> {
        let mut tests = Vec::new();
        for (file_path, file_meta) in &self.files {
            for test in file_meta.ignored_tests() {
                tests.push(TestInfo::from_test_meta(test, file_path.clone()));
            }
        }
        tests
    }

    /// Filter tests by tag
    pub fn filter_by_tag(&self, tag: &str) -> Vec<TestInfo> {
        let mut tests = Vec::new();
        for (file_path, file_meta) in &self.files {
            for test in file_meta.tests_with_tag(tag) {
                tests.push(TestInfo::from_test_meta(test, file_path.clone()));
            }
        }
        tests
    }

    /// Get total test count
    pub fn total_count(&self) -> usize {
        self.files.values().map(|f| f.total_tests).sum()
    }

    /// Get skipped count
    pub fn skipped_count(&self) -> usize {
        self.files.values().map(|f| f.skipped_count).sum()
    }

    /// Get slow count
    pub fn slow_count(&self) -> usize {
        self.files.values().map(|f| f.slow_count).sum()
    }

    /// Get ignored count
    pub fn ignored_count(&self) -> usize {
        self.files.values().map(|f| f.ignored_count).sum()
    }

    /// Get all unique tags
    pub fn all_tags(&self) -> Vec<String> {
        let mut tags: Vec<_> = self.tag_index.keys().cloned().collect();
        tags.sort();
        tags
    }

    /// Format test list for output
    pub fn format_list(&self, show_tags: bool, only_slow: bool, only_skipped: bool, only_ignored: bool) -> String {
        let tests = if only_slow {
            self.list_slow()
        } else if only_skipped {
            self.list_skipped()
        } else if only_ignored {
            self.list_ignored()
        } else {
            self.list_tests()
        };

        let mut output = String::new();

        for test in &tests {
            // Format: file_path:line - test_name [tags]
            output.push_str(&format!(
                "{}:{} - {}",
                test.file_path.display(),
                test.line,
                test.full_name
            ));

            // Add test type indicators
            if test.is_slow {
                output.push_str(" [slow]");
            }
            if test.is_skipped {
                output.push_str(" [skip]");
            }
            if test.is_ignored {
                output.push_str(" [ignore]");
            }

            // Add tags if requested
            if show_tags && !test.tags.is_empty() {
                output.push_str(&format!(" (tags: {})", test.tags.join(", ")));
            }

            output.push('\n');
        }

        // Add summary
        output.push_str(&format!(
            "\nTotal: {} tests ({} slow, {} skipped, {} ignored)\n",
            tests.len(),
            tests.iter().filter(|t| t.is_slow).count(),
            tests.iter().filter(|t| t.is_skipped).count(),
            tests.iter().filter(|t| t.is_ignored).count()
        ));
        output.push_str(&format!("Parse time: {}ms\n", self.parse_time_ms));

        output
    }
}

/// Try to load test metadata using static analysis.
///
/// Falls back to returning an empty registry if parsing fails.
/// This is designed to be resilient - partial results are better than failure.
pub fn try_static_discovery(files: &[PathBuf]) -> StaticTestRegistry {
    match StaticTestRegistry::from_files(files) {
        Ok(registry) => registry,
        Err(e) => {
            eprintln!("Warning: Static discovery failed: {}", e);
            StaticTestRegistry::new()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;
    use tempfile::NamedTempFile;

    fn create_test_file(content: &str) -> NamedTempFile {
        let mut file = NamedTempFile::new().unwrap();
        file.write_all(content.as_bytes()).unwrap();
        file
    }

    #[test]
    fn test_empty_registry() {
        let registry = StaticTestRegistry::new();
        assert_eq!(registry.total_count(), 0);
        assert!(registry.list_tests().is_empty());
    }

    #[test]
    fn test_format_list() {
        let registry = StaticTestRegistry::new();
        let output = registry.format_list(false, false, false, false);
        assert!(output.contains("Total: 0 tests"));
    }

    #[test]
    fn test_try_static_discovery_empty() {
        let registry = try_static_discovery(&[]);
        assert_eq!(registry.total_count(), 0);
    }
}
