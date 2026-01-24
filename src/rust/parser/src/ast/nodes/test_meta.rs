//! Static test metadata structures for compile-time test analysis.
//!
//! This module provides metadata structures that can be extracted from test files
//! at parse time, WITHOUT executing DSL code. This enables fast test listing (~1 second)
//! and queryable metadata for skip/slow/ignore lists.
//!
//! # Design
//!
//! Reuses the existing `ConstMeta` infrastructure from `const_meta.rs`:
//! - `TestMeta` - Individual test metadata (description, flags, tags)
//! - `TestGroupMeta` - Group metadata (describe/context blocks)
//! - `FileTestMeta` - File-level aggregation
//!
//! # Example
//!
//! ```simple
//! describe "Math operations":
//!     @slow
//!     it "handles large numbers":
//!         # This test has TestMeta with:
//!         # - description: "handles large numbers"
//!         # - is_slow: true
//!         pass
//!
//!     @skip("not implemented")
//!     it "supports complex numbers":
//!         pass
//! ```
//!
//! The static analyzer extracts this metadata without executing the DSL functions.

use std::collections::HashMap;

use super::const_meta::{ConstMeta, MetaValue};
use crate::token::Span;

/// Kind of test function (determines default metadata)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum TestKind {
    /// Regular test: `it "description"`
    #[default]
    Normal,
    /// Slow test: `slow_it "description"`
    Slow,
    /// Skipped test: `skip_it "description"` or `skip "description"`
    Skipped,
    /// Ignored test: `ignore_it "description"`
    Ignored,
}

/// Static test metadata extracted at parse time.
///
/// This struct stores all compile-time known information about a single test,
/// extracted from DSL calls and decorators without executing the test code.
#[derive(Debug, Clone)]
pub struct TestMeta {
    /// Core metadata storage (reuses ConstMeta infrastructure)
    pub meta: ConstMeta,
    /// Source location for diagnostics
    pub span: Span,
    /// What kind of DSL call created this test
    pub kind: TestKind,
    /// Full path: ["Math operations", "handles large numbers"]
    pub path: Vec<String>,
}

impl Default for TestMeta {
    fn default() -> Self {
        Self {
            meta: ConstMeta::new(),
            span: Span::new(0, 0, 0, 0),
            kind: TestKind::Normal,
            path: Vec::new(),
        }
    }
}

impl TestMeta {
    /// Create new test metadata with just a description
    pub fn new(description: String, span: Span) -> Self {
        let mut meta = ConstMeta::new();
        meta.set("description".to_string(), MetaValue::String(description));
        Self {
            meta,
            span,
            kind: TestKind::Normal,
            path: Vec::new(),
        }
    }

    /// Create test metadata with kind (slow, skipped, etc.)
    pub fn with_kind(description: String, span: Span, kind: TestKind) -> Self {
        let mut test_meta = Self::new(description, span);
        test_meta.kind = kind;

        // Set appropriate flags based on kind
        match kind {
            TestKind::Slow => {
                test_meta.meta.set("is_slow".to_string(), MetaValue::Bool(true));
            }
            TestKind::Skipped => {
                test_meta.meta.set("is_skipped".to_string(), MetaValue::Bool(true));
            }
            TestKind::Ignored => {
                test_meta.meta.set("is_ignored".to_string(), MetaValue::Bool(true));
            }
            TestKind::Normal => {}
        }

        test_meta
    }

    /// Get the test description
    pub fn description(&self) -> Option<&str> {
        self.meta.get("description").and_then(|v| v.as_string())
    }

    /// Check if test is marked as slow
    pub fn is_slow(&self) -> bool {
        self.meta.get("is_slow").and_then(|v| v.as_bool()).unwrap_or(false)
    }

    /// Check if test is marked as skipped
    pub fn is_skipped(&self) -> bool {
        self.meta.get("is_skipped").and_then(|v| v.as_bool()).unwrap_or(false)
    }

    /// Check if test is marked as ignored
    pub fn is_ignored(&self) -> bool {
        self.meta.get("is_ignored").and_then(|v| v.as_bool()).unwrap_or(false)
    }

    /// Get tags for this test
    pub fn tags(&self) -> Option<&Vec<String>> {
        self.meta.get("tags").and_then(|v| v.as_string_set())
    }

    /// Get timeout in seconds (if specified)
    pub fn timeout_seconds(&self) -> Option<i64> {
        self.meta.get("timeout_seconds").and_then(|v| v.as_integer())
    }

    /// Get skip reason (if test is skipped with a reason)
    pub fn skip_reason(&self) -> Option<&str> {
        self.meta.get("skip_reason").and_then(|v| v.as_string())
    }

    /// Set test as slow
    pub fn set_slow(&mut self, is_slow: bool) {
        self.meta.set("is_slow".to_string(), MetaValue::Bool(is_slow));
    }

    /// Set test as skipped with optional reason
    pub fn set_skipped(&mut self, is_skipped: bool, reason: Option<String>) {
        self.meta.set("is_skipped".to_string(), MetaValue::Bool(is_skipped));
        if let Some(r) = reason {
            self.meta.set("skip_reason".to_string(), MetaValue::String(r));
        }
    }

    /// Set test as ignored
    pub fn set_ignored(&mut self, is_ignored: bool) {
        self.meta.set("is_ignored".to_string(), MetaValue::Bool(is_ignored));
    }

    /// Add a tag to this test
    pub fn add_tag(&mut self, tag: String) {
        let tags = self
            .meta
            .get("tags")
            .and_then(|v| v.as_string_set())
            .cloned()
            .unwrap_or_default();
        let mut tags = tags;
        if !tags.contains(&tag) {
            tags.push(tag);
        }
        self.meta.set("tags".to_string(), MetaValue::StringSet(tags));
    }

    /// Set timeout in seconds
    pub fn set_timeout(&mut self, seconds: i64) {
        self.meta
            .set("timeout_seconds".to_string(), MetaValue::Integer(seconds));
    }

    /// Get full test name (path joined with " > ")
    pub fn full_name(&self) -> String {
        if self.path.is_empty() {
            self.description().unwrap_or("").to_string()
        } else {
            self.path.join(" > ")
        }
    }
}

/// Group metadata for describe/context blocks.
///
/// Represents a container for tests and nested groups,
/// allowing hierarchical test organization.
#[derive(Debug, Clone)]
pub struct TestGroupMeta {
    /// Core metadata storage
    pub meta: ConstMeta,
    /// Group description (from describe/context call)
    pub description: String,
    /// Tests directly in this group
    pub tests: Vec<TestMeta>,
    /// Nested groups (describe/context inside describe/context)
    pub children: Vec<TestGroupMeta>,
    /// Source location
    pub span: Span,
    /// Tags inherited by all tests in this group
    pub tags: Vec<String>,
}

impl Default for TestGroupMeta {
    fn default() -> Self {
        Self {
            meta: ConstMeta::new(),
            description: String::new(),
            tests: Vec::new(),
            children: Vec::new(),
            span: Span::new(0, 0, 0, 0),
            tags: Vec::new(),
        }
    }
}

impl TestGroupMeta {
    /// Create a new group with description
    pub fn new(description: String, span: Span) -> Self {
        let mut meta = ConstMeta::new();
        meta.set("description".to_string(), MetaValue::String(description.clone()));
        Self {
            meta,
            description,
            tests: Vec::new(),
            children: Vec::new(),
            span,
            tags: Vec::new(),
        }
    }

    /// Add a test to this group
    pub fn add_test(&mut self, mut test: TestMeta, group_path: &[String]) {
        // Build full path for the test
        // Note: group_path already includes all parent groups including this one
        let mut path = group_path.to_vec();
        if let Some(desc) = test.description() {
            path.push(desc.to_string());
        }
        test.path = path;

        // Inherit group tags
        for tag in &self.tags {
            test.add_tag(tag.clone());
        }

        self.tests.push(test);
    }

    /// Add a nested group
    pub fn add_child(&mut self, group: TestGroupMeta) {
        self.children.push(group);
    }

    /// Add a tag to this group (inherited by tests)
    pub fn add_tag(&mut self, tag: String) {
        if !self.tags.contains(&tag) {
            self.tags.push(tag);
        }
    }

    /// Count total tests in this group and all children
    pub fn total_tests(&self) -> usize {
        let direct = self.tests.len();
        let nested: usize = self.children.iter().map(|c| c.total_tests()).sum();
        direct + nested
    }

    /// Count skipped tests
    pub fn skipped_count(&self) -> usize {
        let direct = self.tests.iter().filter(|t| t.is_skipped()).count();
        let nested: usize = self.children.iter().map(|c| c.skipped_count()).sum();
        direct + nested
    }

    /// Count slow tests
    pub fn slow_count(&self) -> usize {
        let direct = self.tests.iter().filter(|t| t.is_slow()).count();
        let nested: usize = self.children.iter().map(|c| c.slow_count()).sum();
        direct + nested
    }

    /// Count ignored tests
    pub fn ignored_count(&self) -> usize {
        let direct = self.tests.iter().filter(|t| t.is_ignored()).count();
        let nested: usize = self.children.iter().map(|c| c.ignored_count()).sum();
        direct + nested
    }

    /// Get all tests (flattened from this group and children)
    pub fn all_tests(&self) -> Vec<&TestMeta> {
        let mut tests: Vec<&TestMeta> = self.tests.iter().collect();
        for child in &self.children {
            tests.extend(child.all_tests());
        }
        tests
    }
}

/// File-level test metadata aggregation.
///
/// Contains all test groups and provides summary statistics
/// for a single test file.
#[derive(Debug, Clone, Default)]
pub struct FileTestMeta {
    /// Top-level groups in the file
    pub groups: Vec<TestGroupMeta>,
    /// Top-level tests not in any group
    pub top_level_tests: Vec<TestMeta>,
    /// Total test count (cached for performance)
    pub total_tests: usize,
    /// Skipped test count
    pub skipped_count: usize,
    /// Slow test count
    pub slow_count: usize,
    /// Ignored test count
    pub ignored_count: usize,
    /// File-level tags (from __init__.spl or file header)
    pub file_tags: Vec<String>,
}

impl FileTestMeta {
    /// Create empty file metadata
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a top-level group
    pub fn add_group(&mut self, group: TestGroupMeta) {
        self.groups.push(group);
        self.recalculate_counts();
    }

    /// Add a top-level test (not in any group)
    pub fn add_top_level_test(&mut self, test: TestMeta) {
        self.top_level_tests.push(test);
        self.recalculate_counts();
    }

    /// Recalculate cached counts
    pub fn recalculate_counts(&mut self) {
        self.total_tests = self.top_level_tests.len() + self.groups.iter().map(|g| g.total_tests()).sum::<usize>();

        self.skipped_count = self.top_level_tests.iter().filter(|t| t.is_skipped()).count()
            + self.groups.iter().map(|g| g.skipped_count()).sum::<usize>();

        self.slow_count = self.top_level_tests.iter().filter(|t| t.is_slow()).count()
            + self.groups.iter().map(|g| g.slow_count()).sum::<usize>();

        self.ignored_count = self.top_level_tests.iter().filter(|t| t.is_ignored()).count()
            + self.groups.iter().map(|g| g.ignored_count()).sum::<usize>();
    }

    /// Get all tests in this file (flattened)
    pub fn all_tests(&self) -> Vec<&TestMeta> {
        let mut tests: Vec<&TestMeta> = self.top_level_tests.iter().collect();
        for group in &self.groups {
            tests.extend(group.all_tests());
        }
        tests
    }

    /// Filter tests by tag
    pub fn tests_with_tag(&self, tag: &str) -> Vec<&TestMeta> {
        self.all_tests()
            .into_iter()
            .filter(|t| t.tags().map(|tags| tags.contains(&tag.to_string())).unwrap_or(false))
            .collect()
    }

    /// Get all skipped tests
    pub fn skipped_tests(&self) -> Vec<&TestMeta> {
        self.all_tests().into_iter().filter(|t| t.is_skipped()).collect()
    }

    /// Get all slow tests
    pub fn slow_tests(&self) -> Vec<&TestMeta> {
        self.all_tests().into_iter().filter(|t| t.is_slow()).collect()
    }

    /// Get all ignored tests
    pub fn ignored_tests(&self) -> Vec<&TestMeta> {
        self.all_tests().into_iter().filter(|t| t.is_ignored()).collect()
    }
}

/// Reference to a test (file path + test index)
#[derive(Debug, Clone)]
pub struct TestRef {
    /// Path to the file containing the test
    pub file_path: std::path::PathBuf,
    /// Index into file's test list
    pub test_index: usize,
}

/// Summary information about a test (for listing)
#[derive(Debug, Clone)]
pub struct TestInfo {
    /// Full path to the test file
    pub file_path: std::path::PathBuf,
    /// Full test name (group path + test description)
    pub full_name: String,
    /// Test description only
    pub description: String,
    /// Is this test slow?
    pub is_slow: bool,
    /// Is this test skipped?
    pub is_skipped: bool,
    /// Is this test ignored?
    pub is_ignored: bool,
    /// Tags on this test
    pub tags: Vec<String>,
    /// Skip reason (if any)
    pub skip_reason: Option<String>,
    /// Source location (line number)
    pub line: usize,
}

impl TestInfo {
    /// Create from TestMeta with file path
    pub fn from_test_meta(meta: &TestMeta, file_path: std::path::PathBuf) -> Self {
        Self {
            file_path,
            full_name: meta.full_name(),
            description: meta.description().unwrap_or("").to_string(),
            is_slow: meta.is_slow(),
            is_skipped: meta.is_skipped(),
            is_ignored: meta.is_ignored(),
            tags: meta.tags().cloned().unwrap_or_default(),
            skip_reason: meta.skip_reason().map(|s| s.to_string()),
            line: meta.span.line,
        }
    }
}

/// Index of tests by various criteria
#[derive(Debug, Clone, Default)]
pub struct TestIndex {
    /// Tests indexed by tag
    pub by_tag: HashMap<String, Vec<TestRef>>,
    /// All slow tests
    pub slow: Vec<TestRef>,
    /// All skipped tests
    pub skipped: Vec<TestRef>,
    /// All ignored tests
    pub ignored: Vec<TestRef>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_test_meta_basic() {
        let span = Span::new(0, 10, 1, 0);
        let meta = TestMeta::new("my test".to_string(), span);

        assert_eq!(meta.description(), Some("my test"));
        assert!(!meta.is_slow());
        assert!(!meta.is_skipped());
    }

    #[test]
    fn test_test_meta_with_kind() {
        let span = Span::new(0, 10, 1, 0);
        let slow_meta = TestMeta::with_kind("slow test".to_string(), span.clone(), TestKind::Slow);
        assert!(slow_meta.is_slow());

        let skip_meta = TestMeta::with_kind("skipped test".to_string(), span.clone(), TestKind::Skipped);
        assert!(skip_meta.is_skipped());
    }

    #[test]
    fn test_test_meta_tags() {
        let span = Span::new(0, 10, 1, 0);
        let mut meta = TestMeta::new("tagged test".to_string(), span);

        meta.add_tag("integration".to_string());
        meta.add_tag("database".to_string());

        let tags = meta.tags().unwrap();
        assert!(tags.contains(&"integration".to_string()));
        assert!(tags.contains(&"database".to_string()));
    }

    #[test]
    fn test_group_meta() {
        let span = Span::new(0, 100, 1, 0);
        let mut group = TestGroupMeta::new("Math operations".to_string(), span.clone());

        let test1 = TestMeta::new("adds numbers".to_string(), span.clone());
        let test2 = TestMeta::with_kind("handles overflow".to_string(), span.clone(), TestKind::Slow);

        group.add_test(test1, &[]);
        group.add_test(test2, &[]);

        assert_eq!(group.total_tests(), 2);
        assert_eq!(group.slow_count(), 1);
    }

    #[test]
    fn test_file_meta() {
        let span = Span::new(0, 100, 1, 0);
        let mut file_meta = FileTestMeta::new();

        let mut group = TestGroupMeta::new("Group".to_string(), span.clone());
        group.add_test(TestMeta::new("test1".to_string(), span.clone()), &[]);
        group.add_test(
            TestMeta::with_kind("test2".to_string(), span.clone(), TestKind::Skipped),
            &[],
        );

        file_meta.add_group(group);

        assert_eq!(file_meta.total_tests, 2);
        assert_eq!(file_meta.skipped_count, 1);
    }
}
