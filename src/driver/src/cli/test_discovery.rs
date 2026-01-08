// Test discovery and tag matching
//
// This module handles:
// - Discovering test files in directories
// - Checking if files are test files
// - Extracting and matching tags

use std::path::{Path, PathBuf};

use super::test_runner::TestLevel;

/// Discover test files in a directory
pub fn discover_tests(dir: &Path, level: TestLevel) -> Vec<PathBuf> {
    let mut tests = Vec::new();

    if !dir.is_dir() {
        if is_test_file(dir) {
            tests.push(dir.to_path_buf());
        }
        return tests;
    }

    // Walk directory recursively
    if let Ok(entries) = std::fs::read_dir(dir) {
        for entry in entries.filter_map(|e| e.ok()) {
            let path = entry.path();

            if path.is_dir() {
                let dir_name = path.file_name().and_then(|n| n.to_str()).unwrap_or("");

                // Filter by test level based on directory name
                let should_include = match level {
                    TestLevel::All => true,
                    TestLevel::Unit => {
                        dir_name == "unit" || !["integration", "system"].contains(&dir_name)
                    }
                    TestLevel::Integration => dir_name == "integration",
                    TestLevel::System => dir_name == "system",
                };

                if should_include {
                    tests.extend(discover_tests(&path, level));
                }
            } else if is_test_file(&path) {
                tests.push(path);
            }
        }
    }

    tests.sort();
    tests
}

/// Check if a file is a test file
pub fn is_test_file(path: &Path) -> bool {
    if let Some(name) = path.file_name().and_then(|n| n.to_str()) {
        let is_spl = name.ends_with(".spl");
        let is_test = name.ends_with("_spec.spl") || name.ends_with("_test.spl");
        is_spl && is_test
    } else {
        false
    }
}

/// Extract tags from a test file.
///
/// Tags can be specified in the file using:
/// - `#[tag("name")]` decorator
/// - `@tag name` comment
/// - `#tag: name` comment
///
/// Also checks if the tag is in the file name (e.g., `slow_spec.spl` matches tag "slow")
pub fn extract_tags(path: &Path) -> Vec<String> {
    let mut tags = Vec::new();

    // Check file name for tag patterns
    if let Some(name) = path.file_name().and_then(|n| n.to_str()) {
        // e.g., "slow_spec.spl" -> tag "slow", "integration_test.spl" -> tag "integration"
        let stem = name
            .trim_end_matches(".spl")
            .trim_end_matches("_spec")
            .trim_end_matches("_test");
        if !stem.is_empty() {
            // Split by underscore and take potential tag prefixes
            for part in stem.split('_') {
                if !part.is_empty() {
                    tags.push(part.to_lowercase());
                }
            }
        }
    }

    // Try to read file content for tag decorators/comments
    if let Ok(content) = std::fs::read_to_string(path) {
        // Look for #[tag("name")] pattern using simple string matching
        for line in content.lines() {
            let trimmed = line.trim();

            // Match #[tag("name")]
            if let Some(rest) = trimmed.strip_prefix("#[tag(\"") {
                if let Some(end) = rest.find("\")]") {
                    let tag = &rest[..end];
                    tags.push(tag.to_lowercase());
                }
            }

            // Match @tag name (in comments like # @tag slow)
            if let Some(idx) = trimmed.find("@tag ") {
                let after = &trimmed[idx + 5..];
                let tag: String = after
                    .chars()
                    .take_while(|c| c.is_alphanumeric() || *c == '_')
                    .collect();
                if !tag.is_empty() {
                    tags.push(tag.to_lowercase());
                }
            }

            // Match #tag: name
            if let Some(rest) = trimmed.strip_prefix("#tag:") {
                let tag: String = rest
                    .trim()
                    .chars()
                    .take_while(|c| c.is_alphanumeric() || *c == '_')
                    .collect();
                if !tag.is_empty() {
                    tags.push(tag.to_lowercase());
                }
            }
        }
    }

    // Deduplicate
    tags.sort();
    tags.dedup();
    tags
}

/// Check if a file matches the tag filter.
///
/// Returns true if:
/// - No tag filter is specified (tag is None)
/// - The file's tags contain the filter tag
pub fn matches_tag(path: &Path, tag_filter: &Option<String>) -> bool {
    match tag_filter {
        None => true,
        Some(filter) => {
            let filter_lower = filter.to_lowercase();
            let tags = extract_tags(path);
            tags.iter().any(|t| t == &filter_lower)
        }
    }
}
